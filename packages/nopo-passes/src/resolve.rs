//! Symbol resolution.

use std::collections::HashMap;
use std::fmt;

use la_arena::{Arena, ArenaMap, Idx};
use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::{Diagnostics, IntoReport, Report};
use smol_str::SmolStr;

use nopo_parser::ast::{
    BinaryExpr, ConstructedType, DataConstructor, Expr, FnType, Ident, IdentExpr, ItemId,
    LambdaExpr, LambdaParam, LetExpr, LetId, LetItem, Param, PathType, TupleType, Type, TypeDef,
    TypeId, TypeItem, TypeParam,
};
use nopo_parser::lexer::BinOp;
use nopo_parser::visitor::{walk_expr, walk_let_item, walk_type_item, Visitor};

use crate::map::NodeMap;

#[derive(Report)]
#[kind("error")]
#[message("unresolved type parameter `'{param}`")]
struct UnresolvedTypeParam {
    span: Span,
    #[label(message = "Type param `'{param}` not found in current scope")]
    param: Spanned<Ident>,
}

#[derive(Report)]
#[kind("error")]
#[message("unresolved type `{ty}`")]
struct UnresolvedType {
    span: Span,
    #[label(message = "Type `{ty}` not found in current scope")]
    ty: Spanned<Type>,
}

#[derive(Report)]
#[kind("error")]
#[message("unresolved binding `{ident}`")]
struct UnresolvedBinding {
    span: Span,
    #[label(message = "Binding `{ident}` not found in current scope")]
    ident: Spanned<Ident>,
}

#[derive(Report)]
#[kind("error")]
#[message("wrong number of type parameters for type `{ty}`")]
struct WrongNumberOfTypeParams {
    span: Span,
    #[label(
        message = "{expected} type parameter(s) expected but {found} found",
        order = 1
    )]
    ty: Spanned<Ident>,
    #[label(message = "`{ty}` defined here", order = 2)]
    def_site: Spanned<Ident>,
    expected: usize,
    found: usize,
}

#[derive(Report)]
#[kind("error")]
#[message("`{ty}` is not a kind")]
struct NotAKind<'a> {
    span: Span,
    #[label(message = "`{ty}` is a type, not a kind")]
    ty: Spanned<ResolvedTypePretty<'a>>,
}

/// AST pass for resolving symbols. Does not resolve record fields since that requires type
/// information.
#[derive(Debug)]
pub struct ResolveSymbols {
    pub bindings: Arena<Binding>,

    /// Mapping from identifiers/let-items/let-exprs etc. to their bindings.
    pub bindings_map: BindingsMap,
    /// Mapping from types/type-items to their type data.
    pub types_map: TypesMap,

    /// Stack of current bindings in scope.
    bindings_stack: Vec<BindingId>,
    /// Stack of current types in scope.
    types_stack: Vec<(TypeSymbol, ResolvedType)>,
    /// Temporary state of current item being visited. This is used for creating implicit type
    /// params.
    current_item_id: Option<ItemId>,

    diagnostics: Diagnostics,
}

struct StackState {
    bindings_stack: usize,
    types_stack: usize,
}

impl ResolveSymbols {
    pub fn new(diagnostics: Diagnostics) -> Self {
        Self {
            bindings: Arena::new(),
            bindings_map: BindingsMap::default(),
            types_map: TypesMap::default(),
            bindings_stack: Vec::new(),
            types_stack: Vec::new(),
            current_item_id: None,
            diagnostics,
        }
    }

    fn get_stack_state(&self) -> StackState {
        StackState {
            bindings_stack: self.bindings_stack.len(),
            types_stack: self.types_stack.len(),
        }
    }

    fn restore_stack_state(&mut self, state: StackState) {
        self.bindings_stack.truncate(state.bindings_stack);
        self.types_stack.truncate(state.types_stack);
    }

    fn resolve_type(&mut self, ty: &Spanned<Type>) -> ResolvedType {
        let resolved = self.resolve_type_inner(ty);
        let data_def = self.data_def_of_constructed(&resolved);
        let expected = self.num_of_ty_params(&resolved);
        if let ResolvedType::Constructed {
            constructor,
            arg: _,
        } = &resolved
        {
            let found = resolved.num_of_constructed();
            // Check that resolved is not a kind.
            match (expected, found) {
                (Some(expected), found) if expected == found => resolved,
                (Some(expected), found) => {
                    self.diagnostics.add(WrongNumberOfTypeParams {
                        span: ty.span(),
                        ty: data_def.unwrap().ident.clone().respan(ty.span()),
                        def_site: data_def.unwrap().ident.clone(),
                        expected,
                        found,
                    });
                    ResolvedType::Err
                }
                (None, _found) => {
                    self.diagnostics.add(NotAKind {
                        span: ty.span(),
                        ty: spanned(ty.span(), constructor.pretty(&self.types_map.items)),
                    });
                    ResolvedType::Err
                }
            }
        } else if let Some(expected) = expected {
            if expected != 0 {
                self.diagnostics.add(WrongNumberOfTypeParams {
                    span: ty.span(),
                    ty: data_def.unwrap().ident.clone().respan(ty.span()),
                    def_site: data_def.unwrap().ident.clone(),
                    expected,
                    found: 0,
                });
                ResolvedType::Err
            } else {
                resolved
            }
        } else {
            resolved
        }
    }

    /// Resolve a type or kind.
    fn resolve_type_inner(&mut self, ty: &Type) -> ResolvedType {
        // TODO: check modules
        match ty {
            Type::Path(ty) => self.resolve_path_type(ty),
            Type::Fn(Spanned(FnType { arg_ty, ret_ty }, _)) => ResolvedType::Fn {
                arg: Box::new(self.resolve_type(arg_ty)),
                ret: Box::new(self.resolve_type(ret_ty)),
            },
            Type::Tuple(Spanned(TupleType { fields }, _)) => {
                ResolvedType::Tuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::Constructed(Spanned(ConstructedType { constructor, arg }, _)) => {
                ResolvedType::Constructed {
                    constructor: Box::new(self.resolve_type_inner(constructor)),
                    arg: Box::new(self.resolve_type(arg)),
                }
            }
            Type::Param(Spanned(TypeParam { ident }, span)) => {
                let symbol = TypeSymbol::Param(ident.as_ref().clone());
                if let Some(resolved) = self.try_resolve_type_symbol(&symbol) {
                    resolved
                } else if let Some(ItemId::Let(_)) = self.current_item_id {
                    // If we are inside a let, we can create type parameter implicitly.
                    let resolved = ResolvedType::Param(ident.as_ref().clone().into());
                    self.types_stack.push((symbol, resolved.clone()));
                    resolved
                } else {
                    self.diagnostics.add(UnresolvedTypeParam {
                        span: *span,
                        param: ident.clone(),
                    });
                    ResolvedType::Err
                }
            }
            Type::Err => unreachable!(),
        }
    }

    fn resolve_path_type(&self, ty: &Spanned<PathType>) -> ResolvedType {
        if ty.path.len() != 1 {
            todo!("modules");
        }
        // Lookup type with name ty.path[0]
        if let Some(resolved) =
            self.try_resolve_type_symbol(&TypeSymbol::Path(ty.path[0].as_ref().clone()))
        {
            resolved
        } else {
            // TODO: do not hardcode built-in types in type resolution.
            match ty.path[0].to_string().as_str() {
                "bool" => ResolvedType::Bool,
                "int" => ResolvedType::Int,
                "float" => ResolvedType::Float,
                "string" => ResolvedType::String,
                "char" => ResolvedType::Char,
                _ => {
                    let mut report = UnresolvedType {
                        span: ty.span(),
                        ty: spanned(ty.span(), Type::Path(ty.clone())),
                    }
                    .into_report();
                    // Maybe confused with a binding?
                    if self.try_resolve_binding(&ty.path[0]).is_some() {
                        report.set_help("A binding with the same name exists in this scope");
                    }
                    self.diagnostics.add(report);
                    ResolvedType::Err
                }
            }
        }
    }

    /// Try to resolve a type symbol in the current scope.
    fn try_resolve_type_symbol(&self, symbol: &TypeSymbol) -> Option<ResolvedType> {
        if let Some((_, resolved)) = self.types_stack.iter().rev().find(|(x, _)| x == symbol) {
            Some(resolved.clone())
        } else {
            None
        }
    }

    /// Get the number of type parameters expected. If the type is not a constructed type of
    /// identifiers, returns `None`.
    fn num_of_ty_params(&self, ty: &ResolvedType) -> Option<usize> {
        self.data_def_of_constructed(ty)
            .map(|def| def.ty_params.len())
    }

    fn data_def_of_constructed(&self, ty: &ResolvedType) -> Option<&DataDef> {
        ty.ident_of_constructed()
            .map(|id| &self.types_map.items[id])
    }

    /// Create a new scope for a binding and return the created binding id.
    #[must_use = "binding should be saved to BindingsMap"]
    fn new_binding_scope(&mut self, binding: Binding) -> BindingId {
        let id = self.bindings.alloc(binding);
        self.bindings_stack.push(id);
        id
    }

    fn try_resolve_binding(&self, ident: &Spanned<Ident>) -> Option<BindingId> {
        for id in self.bindings_stack.iter().rev() {
            if &self.bindings[*id].ident == &**ident {
                return Some(*id);
            }
        }
        None
    }

    /// Resolve a binding in the current scope. If binding is not found, produces a diagnostic.
    fn resolve_binding(&self, ident: &Spanned<Ident>) -> ResolvedBinding {
        if let Some(id) = self.try_resolve_binding(ident) {
            return ResolvedBinding::Ok(id);
        }
        // Binding not found.
        let mut report = UnresolvedBinding {
            span: ident.span(),
            ident: ident.clone(),
        }
        .into_report();
        // Maybe confused with a type?
        if self
            .try_resolve_type_symbol(&TypeSymbol::Path(ident.as_ref().clone()))
            .is_some()
        {
            report.set_help("A type with the same name exists in this scope");
        }
        self.diagnostics.add(report);
        ResolvedBinding::Err
    }
}

impl Visitor for ResolveSymbols {
    fn visit_let_item(&mut self, idx: LetId, item: &Spanned<LetItem>) {
        self.current_item_id = Some(ItemId::Let(idx));
        // If no params, then this is a value instead of a function. Don't allow recursive values.
        if item.params.is_empty() {
            walk_let_item(self, item);
        }
        // Create binding for let item itself.
        let let_binding = self.new_binding_scope(Binding {
            ident: item.ident.as_ref().clone(),
        });
        self.bindings_map.let_items.insert(item, let_binding);
        // We want the environment to be restored to this state after the let item.
        let state = self.get_stack_state();
        // Create bindings for all params.
        for param in &item.params {
            let param_binding = self.new_binding_scope(Binding {
                ident: param.ident.as_ref().clone(),
            });
            self.bindings_map.params.insert(param, param_binding);
        }
        if !item.params.is_empty() {
            walk_let_item(self, item);
        }
        self.restore_stack_state(state);
        self.current_item_id = None;
    }

    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        self.current_item_id = Some(ItemId::Type(idx));
        // Create type for type item itself.
        let symbol = TypeSymbol::Path(item.ident.as_ref().clone());
        let resolved = ResolvedType::Ident(idx);
        self.types_stack.push((symbol, resolved));

        // Create bindings for all ADT data constructors.
        if let TypeDef::Adt(adt) = &*item.def {
            for data_constructor in &adt.data_constructors {
                let binding = self.new_binding_scope(Binding {
                    ident: data_constructor.ident.as_ref().clone(),
                });
                self.bindings_map
                    .data_constructors
                    .insert(data_constructor, binding);
            }
        }

        // We want the environment to be restored to this state after the type item.
        let state = self.get_stack_state();

        // Create type parameters.
        for ty_param in &item.ty_params {
            let symbol = TypeSymbol::Param(ty_param.ident.as_ref().clone());
            let resolved = ResolvedType::Param(ty_param.ident.as_ref().clone().into());
            self.types_stack.push((symbol, resolved));
        }

        // Create a temporary data def since we might access it while resolving the types of the
        // ADT data constructors.
        let data_def = DataDef {
            ident: item.ident.clone(),
            kind: TypeKind::Tmp,
            ty_params: item.ty_params.clone(),
            span: item.span(),
        };
        self.types_map.items.insert(idx, data_def);

        walk_type_item(self, item);

        // Update data def with updated information.
        let kind = match &*item.def {
            TypeDef::Adt(adt) => TypeKind::Adt(AdtSymbol {
                variants: adt
                    .data_constructors
                    .iter()
                    .map(|x| AdtVariant {
                        ident: x.ident.as_ref().clone(),
                        types: x
                            .of
                            .iter()
                            .map(|ty| self.types_map.types[ty].clone())
                            .collect(),
                    })
                    .collect(),
            }),
            TypeDef::Record(record) => TypeKind::Record(RecordSymbol {
                fields: record
                    .fields
                    .iter()
                    .map(|field| {
                        (
                            field.ident.as_ref().clone(),
                            self.types_map.types[&field.ty].clone(),
                        )
                    })
                    .collect(),
            }),
            TypeDef::Err => unreachable!(),
        };
        self.types_map.items[idx].kind = kind;

        self.restore_stack_state(state);
        self.current_item_id = None;
    }

    fn visit_type(&mut self, ty: &Spanned<Type>) {
        let resolved = self.resolve_type(ty);
        self.types_map.types.insert(ty, resolved);
    }

    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Let(Spanned(
                let_expr @ LetExpr {
                    ident,
                    ret_ty,
                    expr,
                    _in,
                },
                _,
            )) => {
                // We cannot access the binding inside the expression itself.
                self.visit_expr(expr);
                // Now we can add the binding.
                let binding = self.new_binding_scope(Binding {
                    ident: ident.as_ref().clone(),
                });
                self.bindings_map.let_exprs.insert(let_expr, binding);

                self.visit_expr(_in);

                // Resolve the types of ret.
                if let Some(ret_ty) = ret_ty {
                    self.visit_type(ret_ty);
                }
            }
            Expr::Lambda(Spanned(LambdaExpr { params, expr }, _)) => {
                // Lambdas create a new scope.
                let state = self.get_stack_state();
                // Create bindings for all params.
                for param in params {
                    let binding = self.new_binding_scope(Binding {
                        ident: param.ident.as_ref().clone(),
                    });
                    self.bindings_map.lambda_params.insert(param, binding);
                }

                self.visit_expr(expr);

                self.restore_stack_state(state);
            }
            Expr::Binary(Spanned(BinaryExpr { lhs, op, rhs: _ }, _)) if **op == BinOp::Dot => {
                // We only want to visit the LHS of a member access since the RHS will depend on
                // the type of the LHS.
                self.visit_expr(lhs);
            }
            Expr::Ident(Spanned(ident_expr @ IdentExpr { ident }, _)) => {
                // Lookup the binding for this ident.
                let resolved_binding = self.resolve_binding(&ident);
                self.bindings_map
                    .idents
                    .insert(ident_expr, resolved_binding);
            }
            _ => walk_expr(self, expr),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TypeSymbol {
    Path(Ident),
    Param(Ident),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedType {
    Ident(TypeId),
    Tuple(Vec<Self>),
    Fn {
        arg: Box<Self>,
        ret: Box<Self>,
    },
    Constructed {
        constructor: Box<Self>,
        arg: Box<Self>,
    },
    // Built-in types.
    Bool,
    Int,
    Float,
    String,
    Char,
    /// A type parameter.
    ///
    /// Unlike type variables, these are initially universally quantified, such that constraining
    /// the type param to a specific type is a contradiction (since there is more than a single
    /// type in the domain).
    Param(TypeVar),
    /// A type variable. This can either be free or bound. Type vars can not be explicitly
    /// referenced (TODO: update when inferred types are added).
    ///
    /// Since identifiers cannot start with numbers, automatically generated type vars are always
    /// integers.
    Var(TypeVar),
    /// Universal types.
    /// `'a . f('a)` where `f` is any type potentially containing `'a`.
    ForAll {
        var: TypeVar,
        ty: Box<Self>,
    },
    /// Type could not be resolved.
    Err,
}

pub type TypeVar = SmolStr;

impl ResolvedType {
    /// Create a new resolved type representing a curried function.
    ///
    /// For example, a function with params `a`, `b`, `c` and return value `ret` would become the
    /// type `a -> (b -> (c -> ret))`.
    pub fn new_curried_function(args: &[Self], ret: Self) -> Self {
        match args.split_first() {
            Some((first, rest @ [_, ..])) => Self::Fn {
                arg: Box::new(first.clone()),
                ret: Box::new(Self::new_curried_function(rest, ret)),
            },
            Some((first, _rest @ [])) => Self::Fn {
                arg: Box::new(first.clone()),
                ret: Box::new(ret),
            },
            None => ret,
        }
    }

    /// Create a new resolved type representing a curried constructed type.
    ///
    /// For example, a type `foo` with type params `'a`, `'b` would become the type `(foo 'a) 'b`.
    pub fn new_curried_constructed_ty(constructor: Self, args: &[Self]) -> Self {
        match args.split_first() {
            Some((first, rest @ [_, ..])) => Self::new_curried_constructed_ty(
                Self::Constructed {
                    constructor: Box::new(constructor.clone()),
                    arg: Box::new(first.clone()),
                },
                rest,
            ),
            Some((first, _rest @ [])) => Self::Constructed {
                constructor: Box::new(constructor.clone()),
                arg: Box::new(first.clone()),
            },
            None => constructor,
        }
    }

    /// Create a new resolved type referring to a type item.
    pub fn of_type_item(id: TypeId, type_item_map: &ArenaMap<TypeId, DataDef>) -> Self {
        let ty_params = type_item_map[id]
            .ty_params
            .iter()
            .map(|param| Self::Var(param.ident.as_ref().clone().into()))
            .collect::<Vec<_>>();
        Self::new_curried_constructed_ty(Self::Ident(id), &ty_params)
    }

    pub fn ident_of_constructed(&self) -> Option<TypeId> {
        match self {
            ResolvedType::Ident(id) => Some(*id),
            ResolvedType::Constructed {
                constructor,
                arg: _,
            } => constructor.ident_of_constructed(),
            _ => None,
        }
    }

    fn num_of_constructed(&self) -> usize {
        match self {
            ResolvedType::Constructed {
                constructor,
                arg: _,
            } => constructor.num_of_constructed() + 1,
            _ => 0,
        }
    }

    /// Pretty print the type.
    pub fn pretty<'a>(&'a self, map: &'a ArenaMap<TypeId, DataDef>) -> ResolvedTypePretty<'a> {
        ResolvedTypePretty(self, map)
    }
}

/// Pretty printer for [`ResolvedType`].
pub struct ResolvedTypePretty<'a>(&'a ResolvedType, &'a ArenaMap<TypeId, DataDef>);
impl<'a> fmt::Display for ResolvedTypePretty<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            ResolvedType::Ident(id) => write!(f, "{}", self.1[*id].ident)?,
            ResolvedType::Tuple(types) => {
                write!(f, "(")?;
                if let Some(first) = types.first() {
                    write!(f, "{}", first.pretty(self.1))?;
                }
                for ty in types.iter().skip(1) {
                    write!(f, ", {}", ty.pretty(self.1))?;
                }
                write!(f, ")")?;
            }
            ResolvedType::Fn { arg, ret } => {
                write!(f, "({} -> {})", arg.pretty(self.1), ret.pretty(self.1))?
            }
            ResolvedType::Constructed { constructor, arg } => {
                write!(f, "({} {})", constructor.pretty(self.1), arg.pretty(self.1))?
            }
            ResolvedType::Bool => write!(f, "bool")?,
            ResolvedType::Int => write!(f, "int")?,
            ResolvedType::Float => write!(f, "float")?,
            ResolvedType::String => write!(f, "string")?,
            ResolvedType::Char => write!(f, "char")?,
            ResolvedType::Param(var) => write!(f, "'{var}")?,
            ResolvedType::Var(var) => write!(f, "{{{var}}}")?,
            ResolvedType::ForAll { var, ty } => write!(f, "forall '{var} . {}", ty.pretty(self.1))?,
            ResolvedType::Err => write!(f, "ERR")?,
        }

        Ok(())
    }
}

/// Information about type data.
#[derive(Debug)]
pub struct DataDef {
    pub ident: Spanned<Ident>,
    pub kind: TypeKind,
    pub ty_params: Vec<Spanned<TypeParam>>,
    pub span: Span,
}
#[derive(Debug)]
pub enum TypeKind {
    Record(RecordSymbol),
    Adt(AdtSymbol),
    /// Temporary dummy variable.
    Tmp,
}
impl TypeKind {
    pub fn as_record(&self) -> Option<&RecordSymbol> {
        if let Self::Record(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_adt(&self) -> Option<&AdtSymbol> {
        if let Self::Adt(v) = self {
            Some(v)
        } else {
            None
        }
    }
}
#[derive(Debug)]
pub struct RecordSymbol {
    pub fields: HashMap<Ident, ResolvedType>,
}
#[derive(Debug)]
pub struct AdtSymbol {
    pub variants: Vec<AdtVariant>,
}
#[derive(Debug)]
pub struct AdtVariant {
    pub ident: Ident,
    pub types: Vec<ResolvedType>,
}

#[derive(Debug, Default)]
pub struct TypesMap {
    pub items: ArenaMap<TypeId, DataDef>,
    pub types: NodeMap<Type, ResolvedType>,
}

#[derive(Debug, Default)]
pub struct BindingsMap {
    /// Mapping from identifiers to their bindings.
    pub idents: NodeMap<IdentExpr, ResolvedBinding>,
    /// Mapping from data-constructors to their bindings. Data-constructors are treated just like
    /// functions.
    pub data_constructors: NodeMap<DataConstructor, BindingId>,
    /// Mapping from let params to their bindings.
    pub params: NodeMap<Param, BindingId>,
    /// Mapping from let items to their bindings.
    pub let_items: NodeMap<LetItem, BindingId>,
    /// Mapping from let expressions to their bindings.
    pub let_exprs: NodeMap<LetExpr, BindingId>,
    /// Mapping from lambda params to their bindings.
    pub lambda_params: NodeMap<LambdaParam, BindingId>,
}

pub type BindingId = Idx<Binding>;

/// Represents a symbol that can be referred to by an identifier.
#[derive(Debug)]
pub struct Binding {
    pub ident: Ident,
}

#[derive(Debug)]
pub enum ResolvedBinding {
    Ok(BindingId),
    Err,
}
