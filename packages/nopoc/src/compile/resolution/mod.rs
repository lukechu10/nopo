//! Symbol resolution and type-checking.
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

use la_arena::{Arena, ArenaMap, Idx};

use crate::ast::visitor::{walk_expr, walk_let_item, Visitor};
use crate::ast::{
    BinaryExpr, ConstructedType, Expr, FnType, IdentExpr, LetExpr, LetId, LetItem, PathType, Root,
    TupleType, Type, TypeDef, TypeId, TypeItem,
};
use crate::parser::lexer::BinOp;
use crate::span::{Span, Spanned};

use super::map::NodeMap;

/// Phase 1: Collect names of all items in module. Also checks for duplicate top-level symbols.
#[derive(Debug, Default)]
pub struct CollectIdents {
    pub let_items: HashMap<String, LetId>,
    pub type_items: HashMap<String, TypeId>,
}
impl CollectIdents {
    fn has_symbol_with_ident(&self, ident: &str) -> bool {
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
        self.let_items.insert(item.ident.to_string(), idx);
    }
    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        if self.has_symbol_with_ident(&item.ident) {
            panic!(
                "symbol with ident {} already exists in this scope",
                *item.ident
            );
        }
        self.type_items.insert(item.ident.to_string(), idx);
    }
}

/// Phase 2: Resolve type contents.
#[derive(Debug)]
pub struct ResolveTypeContents {
    idents: CollectIdents,
    pub types: ArenaMap<TypeId, TypeData>,
    current_type_id: Option<TypeId>,
    /// Current list of type args in scope.
    current_type_params: Vec<String>,
}
impl ResolveTypeContents {
    pub fn new(idents: CollectIdents) -> Self {
        Self {
            idents,
            types: ArenaMap::new(),
            current_type_id: None,
            current_type_params: Vec::new(),
        }
    }

    pub fn resolve_type(&self, ty: &Type) -> ResolvedType {
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
                    constructor: Box::new(self.resolve_type(constructor)),
                    arg: Box::new(self.resolve_type(arg)),
                }
            }
        }
    }

    fn resolve_path_type(&self, ty: &PathType) -> ResolvedType {
        if ty.path.len() != 1 {
            todo!("modules");
        }
        // First check if it is a type param.
        if let Some(param_pos) = self
            .current_type_params
            .iter()
            .position(|x| &*ty.path[0] == x)
        {
            ResolvedType::TypeParam {
                constructor: self.current_type_id.unwrap(),
                param_pos,
            }
        }
        // Lookup type with name ty.path[0]
        else if let Some(id) = self.idents.type_items.get(&*ty.path[0]) {
            ResolvedType::Ident(*id)
        } else {
            eprintln!("unresolved type {ty:?}, TODO: implement diagnostics");
            ResolvedType::Err
        }
    }
}

#[derive(Debug)]
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
    TypeParam {
        constructor: TypeId,
        param_pos: usize,
    },
    /// Type could not be resolved.
    Err,
}
/// Data about a type.
#[derive(Debug)]
pub struct TypeData {
    pub ident: Spanned<String>,
    pub kind: TypeKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum TypeKind {
    Record(RecordSymbol),
    Adt(AdtSymbol),
}
#[derive(Debug)]
pub struct RecordSymbol {
    pub fields: HashMap<String, ResolvedType>,
}
#[derive(Debug)]
pub struct AdtSymbol {
    pub variants: Vec<AdtVariant>,
}
#[derive(Debug)]
pub struct AdtVariant {
    pub ident: String,
    pub types: Vec<ResolvedType>,
}

impl Visitor for ResolveTypeContents {
    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        self.current_type_id = Some(idx);
        self.current_type_params = item.ty_params.iter().map(|x| x.ident.to_string()).collect();
        let kind = match &*item.def {
            TypeDef::Adt(adt) => {
                let mut variants = Vec::new();
                for variant in &adt.data_constructors {
                    variants.push(AdtVariant {
                        ident: variant.ident.to_string(),
                        types: variant.of.iter().map(|ty| self.resolve_type(ty)).collect(),
                    })
                }
                TypeKind::Adt(AdtSymbol { variants })
            }
            TypeDef::Record(record) => TypeKind::Record(RecordSymbol {
                fields: record
                    .fields
                    .iter()
                    .map(|field| (field.ident.to_string(), self.resolve_type(&field.ty)))
                    .collect(),
            }),
        };
        self.types.insert(
            idx,
            TypeData {
                ident: item.ident.clone(),
                kind,
                span: item.span(),
            },
        );
    }
}

/// Phase 3: Resolve let bodies.
#[derive(Debug)]
pub struct ResolveLetContents {
    type_contents: ResolveTypeContents,
    bindings: Arena<BindingData>,
    global_bindings_map: HashMap<LetId, BindingId>,
    local_bindings_stack: Vec<BindingId>,
    /// Mapping from identifier and let expressions to the associated [`BindingId`].
    ///
    /// If the expression is an identifier, the binding id is the binding which this identifier
    /// references. If the expression is a `let` expression, the binding id is the binding which is
    /// created by this expression.
    expr_bindings_map: NodeMap<Expr, ResolvedBinding>,
    type_map: NodeMap<Type, ResolvedType>,
}

type BindingId = Idx<BindingData>;
#[derive(Debug)]
pub struct BindingData {
    pub ident: String,
}

#[derive(Debug)]
pub enum ResolvedBinding {
    Ok(BindingId),
    Err,
}

impl ResolveLetContents {
    pub fn new(type_contents: ResolveTypeContents) -> Self {
        let mut bindings = Arena::new();
        let mut global_bindings_map = HashMap::new();
        // Create a binding for all the global let items.
        for (ident, idx) in &type_contents.idents.let_items {
            let binding = bindings.alloc(BindingData {
                ident: ident.clone(),
            });
            global_bindings_map.insert(*idx, binding);
        }

        Self {
            type_contents,
            bindings,
            global_bindings_map,
            local_bindings_stack: Vec::new(),
            expr_bindings_map: NodeMap::default(),
            type_map: NodeMap::default(),
        }
    }

    /// Try to resolve a variable binding. If no binding is found, an error is produce and a
    /// [`ResolvedBinding::Err`] is returned.
    fn resolve_binding(&self, ident: &str) -> ResolvedBinding {
        // Check local bindings stack first, going in reverse direction.
        for &local_binding in self.local_bindings_stack.iter().rev() {
            if &self.bindings[local_binding].ident == ident {
                return ResolvedBinding::Ok(local_binding);
            }
        }
        // Check if binding is in global scope.
        if let Some(let_id) = self.type_contents.idents.let_items.get(ident) {
            ResolvedBinding::Ok(self.global_bindings_map[let_id])
        } else {
            eprintln!("binding not found, TODO: implement diagnostics");
            ResolvedBinding::Err
        }
    }
}

impl Visitor for ResolveLetContents {
    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        // Add all the params as bindings in this scope.
        for param in &item.params {
            let binding = self.bindings.alloc(BindingData {
                ident: param.ident.to_string(),
            });
            self.local_bindings_stack.push(binding);
        }
        walk_let_item(self, item);
        for _ in &item.params {
            self.local_bindings_stack.pop();
        }

        // Resolve the types of the params and ret.
        for param in &item.params {
            if let Some(ty) = &param.ty {
                let resolved_ty = self.type_contents.resolve_type(ty);
                self.type_map.insert(ty, resolved_ty);
            }
        }
        if let Some(ret_ty) = &item.ret_ty {
            let resolved_ty = self.type_contents.resolve_type(ret_ty);
            self.type_map.insert(ret_ty, resolved_ty);
        }
    }

    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Let(Spanned(
                LetExpr {
                    ident,
                    ret_ty,
                    expr,
                    _in,
                },
                _,
            )) => {
                // We cannot access the binding inside the expression itself.
                self.visit_expr(expr);
                // No we can add the binding.
                let binding = self.bindings.alloc(BindingData {
                    ident: ident.to_string(),
                });
                self.expr_bindings_map
                    .insert(expr, ResolvedBinding::Ok(binding));
                self.local_bindings_stack.push(binding);
                self.visit_expr(_in);
                self.local_bindings_stack.pop();

                // Resolve the types of the params and ret.
                if let Some(ret_ty) = ret_ty {
                    let resolved_ty = self.type_contents.resolve_type(ret_ty);
                    self.type_map.insert(ret_ty, resolved_ty);
                }
            }
            Expr::Binary(Spanned(BinaryExpr { lhs, op, rhs: _ }, _)) if **op == BinOp::Dot => {
                // We only want to visit the LHS of a member access since the RHS will depend on
                // the type of the LHS.
                self.visit_expr(lhs);
            }
            Expr::Ident(Spanned(IdentExpr { ident }, _)) => {
                // Lookup the binding for this ident.
                let resolved_binding = self.resolve_binding(&ident);
                self.expr_bindings_map.insert(expr, resolved_binding);
            }
            _ => walk_expr(self, expr),
        }
    }
}

pub fn run_resolution_passes(root: &Root) {
    let mut collect_idents = CollectIdents::default();
    collect_idents.visit_root(root);
    let mut resolve_type_contents = ResolveTypeContents::new(collect_idents);
    resolve_type_contents.visit_root(root);
    let mut resolve_let_contents = ResolveLetContents::new(resolve_type_contents);
    resolve_let_contents.visit_root(root);
}
