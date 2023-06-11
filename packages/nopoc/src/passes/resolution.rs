//! Symbol resolution.
//!
//! This happens in phases:
//!
//! # Phase 1
//! Go through the module and collect the identifiers of all let and type items.
//!
//! # Phase 2
//! Now that we know all the names of all the types, we can resolve the bodies of the types
//! themselves.
//!
//! # Phase 3
//! Now that we know all the bodies of all the types, we can finally resolve the bodies of the let
//! items.

use std::collections::HashMap;
use std::fmt;

use la_arena::{Arena, ArenaMap, Idx};
use nopo_diagnostics::{Diagnostics, IntoReport};

use crate::ast::visitor::{walk_expr, walk_let_item, walk_root, Visitor};
use crate::ast::{
    BinaryExpr, ConstructedType, DataConstructor, Expr, FnType, Ident, IdentExpr, LetExpr, LetId,
    LetItem, Param, PathType, Root, TupleType, Type, TypeDef, TypeId, TypeItem, TypeParam,
};
use crate::parser::lexer::BinOp;
use nopo_diagnostics::span::{spanned, Span, Spanned};

use super::map::NodeMap;

#[derive(IntoReport)]
#[kind("error")]
#[message("unresolved type parameter `'{param}`")]
struct UnresolvedTypeParam {
    span: Span,
    #[label(message = "`'{param}` not found in current scope")]
    param: Spanned<Ident>,
}

#[derive(IntoReport)]
#[kind("error")]
#[message("unresolved type `{ty}`")]
struct UnresolvedType {
    span: Span,
    #[label(message = "Type `{ty}` not found in current scope")]
    ty: Spanned<Type>,
}

#[derive(IntoReport)]
#[kind("error")]
#[message("unresolved binding `{ident}`")]
struct UnresolvedBinding {
    span: Span,
    #[label(message = "Binding `{ident}` not found in current scope")]
    ident: Spanned<Ident>,
}

/// Phase 1: Collect names of all items in module. Also checks for duplicate top-level symbols.
#[derive(Debug, Default)]
pub struct CollectIdents {
    pub let_items: HashMap<Ident, LetId>,
    pub type_items: HashMap<Ident, TypeId>,
}
impl CollectIdents {
    fn has_symbol_with_ident(&self, ident: &Ident) -> bool {
        self.let_items.get(ident).is_some() || self.type_items.get(ident).is_some()
    }
}

impl Visitor for CollectIdents {
    fn visit_let_item(&mut self, idx: LetId, item: &Spanned<LetItem>) {
        if self.has_symbol_with_ident(&item.ident) {
            panic!(
                "symbol with ident {} already exists in this scope",
                *item.ident
            );
        }
        self.let_items.insert(item.ident.as_ref().clone(), idx);
    }
    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        if self.has_symbol_with_ident(&item.ident) {
            panic!(
                "symbol with ident {} already exists in this scope",
                *item.ident
            );
        }
        self.type_items.insert(item.ident.as_ref().clone(), idx);
    }
}

/// Phase 2: Resolve type contents.
#[derive(Debug)]
pub struct ResolveTypeContents {
    idents: CollectIdents,
    /// Map from type items to their type data.
    pub type_item_map: ArenaMap<TypeId, TypeData>,
    /// Temporary state of current type item being visited.
    current_type_id: Option<TypeId>,
    /// Temporary state of current let item being visited.
    current_let_id: Option<LetId>,
    /// Current list of type args in scope.
    current_type_params: Vec<Ident>,
    diagnostics: Diagnostics,
}
impl ResolveTypeContents {
    pub fn new(idents: CollectIdents, diagnostics: Diagnostics) -> Self {
        Self {
            idents,
            type_item_map: ArenaMap::new(),
            current_type_id: None,
            current_let_id: None,
            current_type_params: Vec::new(),
            diagnostics,
        }
    }

    /// `create_ty_params` should be `true` only when called for the parameter of a let item. This
    /// will automatically create a new type param instead of producing an error.
    pub fn resolve_type(&mut self, ty: &Type, create_ty_params: bool) -> ResolvedType {
        // TODO: check modules
        match ty {
            Type::Path(ty) => self.resolve_path_type(ty),
            Type::Fn(Spanned(FnType { arg_ty, ret_ty }, _)) => ResolvedType::Fn {
                arg: Box::new(self.resolve_type(arg_ty, create_ty_params)),
                ret: Box::new(self.resolve_type(ret_ty, create_ty_params)),
            },
            Type::Tuple(Spanned(TupleType { fields }, _)) => ResolvedType::Tuple(
                fields
                    .iter()
                    .map(|ty| self.resolve_type(ty, create_ty_params))
                    .collect(),
            ),
            Type::Constructed(Spanned(ConstructedType { constructor, arg }, _)) => {
                ResolvedType::Constructed {
                    constructor: Box::new(self.resolve_type(constructor, create_ty_params)),
                    arg: Box::new(self.resolve_type(arg, create_ty_params)),
                }
            }
            Type::Param(Spanned(TypeParam { ident }, span)) => {
                if let Some(param_pos) = self.current_type_params.iter().position(|x| &**ident == x)
                {
                    if let Some(constructor) = self.current_type_id {
                        ResolvedType::TypeParamOnType {
                            constructor,
                            param_pos,
                        }
                    } else if let Some(item) = self.current_let_id {
                        ResolvedType::TypeParamOnLet { item, param_pos }
                    } else {
                        unreachable!(
                            "resolve_type can only be called in the context of a let or type item"
                        );
                    }
                } else if create_ty_params {
                    let param_pos = self.current_type_params.len();
                    self.current_type_params.push(ident.as_ref().clone());
                    // Can only automatically create a type param on a let.
                    ResolvedType::TypeParamOnLet {
                        item: self.current_let_id.unwrap(),
                        param_pos,
                    }
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
        else if let Some(id) = self.idents.type_items.get(&*ty.path[0]) {
            ResolvedType::Ident(*id)
        } else {
            // TODO: do not hardcode built-in types in type resolution.
            match ty.path[0].to_string().as_str() {
                "bool" => ResolvedType::Bool,
                "int" => ResolvedType::Int,
                "float" => ResolvedType::Float,
                "string" => ResolvedType::String,
                "char" => ResolvedType::Char,
                _ => {
                    self.diagnostics.add(UnresolvedType {
                        span: ty.span(),
                        ty: spanned(ty.span(), Type::Path(ty.clone())),
                    });
                    ResolvedType::Err
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedType {
    Ident(TypeId),
    Tuple(Vec<ResolvedType>),
    Fn {
        arg: Box<ResolvedType>,
        ret: Box<ResolvedType>,
    },
    Constructed {
        constructor: Box<ResolvedType>,
        arg: Box<ResolvedType>,
    },
    TypeParamOnType {
        constructor: TypeId,
        param_pos: usize,
    },
    TypeParamOnLet {
        item: LetId,
        /// The position where this type parameter appears in the signature of the let item.
        param_pos: usize,
    },
    // Built-in types.
    Bool,
    Int,
    Float,
    String,
    Char,
    /// Used for expressions that have not had their type inferred yet.
    Tmp(u32),
    /// Type could not be resolved.
    Err,
}

impl ResolvedType {
    /// Create a new resolved type representing a curried function.
    ///
    /// For example, a function with params `a`, `b`, `c` and return value `ret` would become the
    /// type `a -> b -> c -> ret`.
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

    pub fn of_type_item(id: TypeId) -> Self {
        Self::Ident(id)
    }

    /// Pretty print the type.
    pub fn pretty<'a>(&'a self, map: &'a ArenaMap<TypeId, TypeData>) -> ResolvedTypePretty<'a> {
        ResolvedTypePretty(self, map)
    }
}

pub struct ResolvedTypePretty<'a>(&'a ResolvedType, &'a ArenaMap<TypeId, TypeData>);
impl<'a> fmt::Display for ResolvedTypePretty<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            ResolvedType::Ident(id) => write!(f, "{}", self.1[*id].ident)?,
            ResolvedType::Tuple(types) => {
                write!(f, "(")?;
                for ty in types {
                    write!(f, "{}", ty.pretty(self.1))?;
                }
                write!(f, ")")?;
            }
            ResolvedType::Fn { arg, ret } => {
                write!(f, "({} -> {})", arg.pretty(self.1), ret.pretty(self.1))?
            }
            ResolvedType::Constructed { constructor, arg } => {
                write!(f, "({} {})", constructor.pretty(self.1), arg.pretty(self.1))?
            }
            ResolvedType::TypeParamOnType {
                constructor,
                param_pos,
            } => write!(f, "'{}", self.1[*constructor].ty_params[*param_pos].ident)?,
            // TODO: display actual name.
            ResolvedType::TypeParamOnLet { item: _, param_pos } => write!(f, "'{param_pos}")?,
            ResolvedType::Bool => write!(f, "bool")?,
            ResolvedType::Int => write!(f, "int")?,
            ResolvedType::Float => write!(f, "float")?,
            ResolvedType::String => write!(f, "string")?,
            ResolvedType::Char => write!(f, "char")?,
            ResolvedType::Tmp(i) => write!(f, "{{unknown:{i}}}")?,
            ResolvedType::Err => write!(f, "ERR")?,
        }

        Ok(())
    }
}

/// Data about a type.
#[derive(Debug)]
pub struct TypeData {
    pub ident: Spanned<Ident>,
    pub kind: TypeKind,
    pub ty_params: Vec<Spanned<TypeParam>>,
    pub span: Span,
}
#[derive(Debug)]
pub enum TypeKind {
    Record(RecordSymbol),
    Adt(AdtSymbol),
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

impl Visitor for ResolveTypeContents {
    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        self.current_type_id = Some(idx);
        self.current_type_params = item
            .ty_params
            .iter()
            .map(|x| x.ident.as_ref().clone())
            .collect();
        let kind = match &*item.def {
            TypeDef::Adt(adt) => {
                let mut variants = Vec::new();
                for variant in &adt.data_constructors {
                    variants.push(AdtVariant {
                        ident: variant.ident.as_ref().clone(),
                        types: variant
                            .of
                            .iter()
                            .map(|ty| self.resolve_type(ty, false))
                            .collect(),
                    })
                }
                TypeKind::Adt(AdtSymbol { variants })
            }
            TypeDef::Record(record) => TypeKind::Record(RecordSymbol {
                fields: record
                    .fields
                    .iter()
                    .map(|field| {
                        (
                            field.ident.as_ref().clone(),
                            self.resolve_type(&field.ty, false),
                        )
                    })
                    .collect(),
            }),
            TypeDef::Err => unreachable!(),
        };
        self.type_item_map.insert(
            idx,
            TypeData {
                ident: item.ident.clone(),
                kind,
                ty_params: item.ty_params.clone(),
                span: item.span(),
            },
        );
        self.current_type_id = None;
        self.current_type_params.clear();
    }
}

/// Phase 3: Resolve let bodies.
#[derive(Debug)]
pub struct ResolveLetContents {
    pub type_contents: ResolveTypeContents,
    pub bindings: Arena<BindingData>,
    global_bindings: Vec<BindingId>,
    local_bindings_stack: Vec<BindingId>,
    /// Mapping from AST nodes to bindings.
    pub bindings_map: BindingsMap,
    /// Mapping from type items too the types that they represent.
    pub type_map: NodeMap<Type, ResolvedType>,
    diagnostics: Diagnostics,
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
}

pub type BindingId = Idx<BindingData>;
#[derive(Debug)]
pub struct BindingData {
    pub ident: Ident,
}

#[derive(Debug)]
pub enum ResolvedBinding {
    Ok(BindingId),
    Err,
}

impl ResolveLetContents {
    pub fn new(type_contents: ResolveTypeContents, diagnostics: Diagnostics) -> Self {
        Self {
            type_contents,
            bindings: Arena::new(),
            global_bindings: Vec::new(),
            local_bindings_stack: Vec::new(),
            bindings_map: BindingsMap::default(),
            type_map: NodeMap::default(),
            diagnostics,
        }
    }

    /// Try to resolve a variable binding. If no binding is found, an error is produce and a
    /// [`ResolvedBinding::Err`] is returned.
    fn resolve_binding(&self, ident: &Spanned<Ident>) -> ResolvedBinding {
        // Check local bindings stack first, going in reverse direction.
        for &local_binding in self.local_bindings_stack.iter().rev() {
            if &self.bindings[local_binding].ident == &**ident {
                return ResolvedBinding::Ok(local_binding);
            }
        }
        // Check if binding is in global scope.
        if let Some(binding) = self
            .global_bindings
            .iter()
            .find(|idx| &self.bindings[**idx].ident == &**ident)
        {
            ResolvedBinding::Ok(*binding)
        } else {
            self.diagnostics.add(UnresolvedBinding {
                span: ident.span(),
                ident: ident.clone(),
            });
            ResolvedBinding::Err
        }
    }
}

impl Visitor for ResolveLetContents {
    /// Create all the global bindings here and all the local bindings in other visitor methods.
    fn visit_root(&mut self, root: &Root) {
        // Create a binding for all the global let items.
        for (_idx, let_item) in root.let_items.iter() {
            let binding = self.bindings.alloc(BindingData {
                ident: let_item.ident.as_ref().clone(),
            });
            self.bindings_map.let_items.insert(let_item, binding);
            self.global_bindings.push(binding);
        }

        // Create a binding for all data constructors.
        for (_idx, type_item) in root.type_items.iter() {
            match &*type_item.def {
                TypeDef::Adt(adt) => {
                    for data_constructor in &adt.data_constructors {
                        let binding = self.bindings.alloc(BindingData {
                            ident: data_constructor.ident.as_ref().clone(),
                        });
                        self.bindings_map
                            .data_constructors
                            .insert(data_constructor, binding);
                        self.global_bindings.push(binding);
                    }
                }
                TypeDef::Record(_) => {}
                TypeDef::Err => unreachable!(),
            }
        }

        // We can create the local bindings now that we have all the global ones.
        walk_root(self, root);
    }

    fn visit_let_item(&mut self, idx: LetId, item: &Spanned<LetItem>) {
        self.type_contents.current_let_id = Some(idx);
        // Add all the params as bindings in this scope.
        for param in &item.params {
            let binding = self.bindings.alloc(BindingData {
                ident: param.ident.as_ref().clone(),
            });
            self.bindings_map.params.insert(param, binding);
            self.local_bindings_stack.push(binding);
        }
        walk_let_item(self, item);
        for _ in &item.params {
            self.local_bindings_stack.pop();
        }

        // Resolve the types of the params and ret.
        for param in &item.params {
            if let Some(ty) = &param.ty {
                let resolved_ty = self.type_contents.resolve_type(ty, true);
                self.type_map.insert(ty, resolved_ty);
            }
        }
        if let Some(ret_ty) = &item.ret_ty {
            let resolved_ty = self.type_contents.resolve_type(ret_ty, true);
            self.type_map.insert(ret_ty, resolved_ty);
        }

        self.type_contents.current_let_id = None;
        self.type_contents.current_type_params.clear(); // Clear the type params from this let item.
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
                let binding = self.bindings.alloc(BindingData {
                    ident: ident.as_ref().clone(),
                });
                self.bindings_map.let_exprs.insert(let_expr, binding);

                self.local_bindings_stack.push(binding);
                self.visit_expr(_in);
                self.local_bindings_stack.pop();

                // Resolve the types of ret.
                if let Some(ret_ty) = ret_ty {
                    let resolved_ty = self.type_contents.resolve_type(ret_ty, false);
                    self.type_map.insert(ret_ty, resolved_ty);
                }
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
