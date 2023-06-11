//! Type unification / type inference.
//!
//! We want to infer the type of every binding.
//!
//! Prefix all constraint types in code with `c_` to distinguish from syntax elements.

use std::collections::HashMap;
use std::ops::Sub;

use la_arena::{Arena, ArenaMap};
use nopo_diagnostics::span::{FileId, Span, Spanned};
use nopo_diagnostics::{Diagnostics, IntoReport};

use crate::ast::visitor::{walk_expr, Visitor};
use crate::ast::{Expr, LetId, LetItem, Root, Type, TypeDef, TypeId, TypeItem};
use crate::parser::lexer::UnaryOp;

use super::map::NodeMap;
use super::resolution::{
    BindingData, BindingId, BindingsMap, ResolveLetContents, ResolvedBinding, ResolvedType,
    TypeData, TypeKind,
};

#[derive(IntoReport)]
#[kind("error")]
#[message("could not unify types")]
struct CouldNotUnifyTypes {
    span: Span,
}

#[derive(IntoReport)]
#[kind("error")]
#[message("cannot create infinite type")]
struct CannotCreateInfiniteType {
    span: Span,
}

#[derive(Debug)]
pub struct UnifyTypes {
    bindings: Arena<BindingData>,
    bindings_map: BindingsMap,
    type_map: NodeMap<Type, ResolvedType>,
    type_item_map: ArenaMap<TypeId, TypeData>,
    state: InferState,
    diagnostics: Diagnostics,
}

/// Temporary state used in unifying types.
#[derive(Debug, Default)]
pub struct InferState {
    type_var_counter: u32,
    /// Contains the type of all the bindings.
    binding_types_map: HashMap<BindingId, ResolvedType>,
    /// Keep track of all the types of all the expressions.
    ///
    /// This will not contain final inferred types but only temporary types, since this is only
    /// used to generate type constraints.
    expr_types_map: NodeMap<Expr, ResolvedType>,
    /// A list of constraints.
    constraints: Vec<Constraint>,
}

/// Represents a type constraint, constraing the LHS and the RHS together.
#[derive(Debug, Clone)]
pub struct Constraint(ResolvedType, ResolvedType);

impl InferState {
    /// Create a new type variable.
    pub fn new_type_var(&mut self) -> ResolvedType {
        let counter = self.type_var_counter;
        self.type_var_counter += 1;
        ResolvedType::Tmp(counter)
    }
}

impl UnifyTypes {
    pub fn new(resolution: ResolveLetContents, diagnostics: Diagnostics) -> Self {
        Self {
            bindings: resolution.bindings,
            bindings_map: resolution.bindings_map,
            type_map: resolution.type_map,
            type_item_map: resolution.type_contents.type_item_map,
            state: InferState::default(),
            diagnostics,
        }
    }
}

impl Visitor for UnifyTypes {
    fn visit_root(&mut self, root: &Root) {
        // Visit type items first since we know the types of all the data constructors.
        for (idx, item) in root.type_items.iter() {
            self.visit_type_item(idx, item);
        }

        for (idx, item) in root.let_items.iter() {
            self.visit_let_item(idx, item);
        }

        self.solve();
    }

    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        match &*item.def {
            TypeDef::Adt(adt) => {
                let type_data = match &self.type_item_map[idx].kind {
                    TypeKind::Record(_) => unreachable!(),
                    TypeKind::Adt(adt) => adt,
                };
                for (data_constructor, variant) in
                    adt.data_constructors.iter().zip(&type_data.variants)
                {
                    let binding = self.bindings_map.data_constructors[&**data_constructor];
                    let c_ty = ResolvedType::new_curried_function(
                        &variant.types,
                        ResolvedType::of_type_item(idx),
                    );
                    self.state.binding_types_map.insert(binding, c_ty);
                }
            }
            TypeDef::Record(_) => {}
            TypeDef::Err => unreachable!(),
        }
    }

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        // The type of the let item.
        let c_ty = self.state.new_type_var();
        let binding = self.bindings_map.let_items[&**item];
        self.state.binding_types_map.insert(binding, c_ty.clone());

        // Constraints for let params. Since params can have explicit type annotations, we can use
        // a shortcut and add the resolved types right away instead of inferring them.
        let c_params_ty = item
            .params
            .iter()
            .map(|param| {
                param.ty.as_ref().map_or_else(
                    || self.state.new_type_var(),
                    |ty| self.type_map[&*ty].clone(),
                )
            })
            .collect::<Vec<_>>();
        for (c_ty, param) in c_params_ty.iter().zip(&item.params) {
            let binding = self.bindings_map.params[&**param];
            self.state.binding_types_map.insert(binding, c_ty.clone());
        }

        // Constraint for return type.
        self.visit_expr(&item.expr);
        let c_expr_ty = self.state.expr_types_map[&**item.expr].clone();
        let c_ret_ty = if let Some(ret_ty) = &item.ret_ty {
            self.type_map[&**ret_ty].clone()
        } else {
            self.state.new_type_var()
        };
        self.state
            .constraints
            .push(Constraint(c_ret_ty.clone(), c_expr_ty));

        // Add type for the whole let item.
        let c_fn_ty = ResolvedType::new_curried_function(&c_params_ty, c_ret_ty);
        self.state.constraints.push(Constraint(c_ty, c_fn_ty));
    }

    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Let(let_expr) => {
                let binding = self.bindings_map.let_exprs[&**let_expr];
                let c_ty = if let Some(ret_ty) = &let_expr.ret_ty {
                    self.type_map[&**ret_ty].clone()
                } else {
                    self.state.new_type_var()
                };
                self.state.binding_types_map.insert(binding, c_ty);
            }
            _ => {}
        }

        // This ensures that self.state.expr_types_map is instantiated for all child nodes.
        walk_expr(self, expr);

        let c_ty = match &**expr {
            Expr::Ident(ident_expr) => {
                // Lookup binding and set that as the expression of the type.
                let binding = &self.bindings_map.idents[&**ident_expr];
                if let ResolvedBinding::Ok(binding) = binding {
                    self.state.binding_types_map[binding].clone()
                } else {
                    // If this ident was not resolved, it could potentially be anything.
                    // FIXME: make sure this does not produce extra errors about unbounded types.
                    self.state.new_type_var()
                }
            }
            Expr::Block(_) => {
                todo!("unify block expressions (should we even keep block expressions?)")
            }
            Expr::Tuple(tuple_expr) => ResolvedType::Tuple(
                tuple_expr
                    .elements
                    .iter()
                    .map(|element| self.state.expr_types_map[element].clone())
                    .collect(),
            ),
            Expr::Record(_) => todo!("unify record types"),
            Expr::Binary(binary_expr) => {
                // TODO: binary operations on types other than int (introduce new operator or
                // ad-hoc polymorphism?)
                let c_lhs = self.state.expr_types_map[&*binary_expr.lhs].clone();
                let c_rhs = self.state.expr_types_map[&*binary_expr.rhs].clone();
                self.state
                    .constraints
                    .push(Constraint(c_lhs, ResolvedType::Int));
                self.state
                    .constraints
                    .push(Constraint(c_rhs, ResolvedType::Int));
                ResolvedType::Int
            }
            Expr::Unary(unary_expr) => match *unary_expr.op {
                UnaryOp::Neg => {
                    let c_expr = self.state.expr_types_map[&*unary_expr.expr].clone();
                    self.state
                        .constraints
                        .push(Constraint(c_expr, ResolvedType::Int));
                    ResolvedType::Int
                }
                UnaryOp::Not => {
                    let c_expr = self.state.expr_types_map[&*unary_expr.expr].clone();
                    self.state
                        .constraints
                        .push(Constraint(c_expr, ResolvedType::Bool));
                    ResolvedType::Bool
                }
            },
            Expr::Index(_) => todo!("unify index expressions"),
            Expr::LitBool(_) => ResolvedType::Bool,
            Expr::LitInt(_) => ResolvedType::Int,
            Expr::LitFloat(_) => ResolvedType::Float,
            Expr::LitStr(_) => ResolvedType::String,
            Expr::LitChar(_) => ResolvedType::Char,
            Expr::If(if_expr) => {
                let c_cond_ty = self.state.expr_types_map[&if_expr.cond].clone();
                self.state
                    .constraints
                    .push(Constraint(c_cond_ty, ResolvedType::Bool));
                let c_branch_ty = self.state.new_type_var();
                let c_then = self.state.expr_types_map[&if_expr.then].clone();
                let c_else = self.state.expr_types_map[&if_expr.else_].clone();
                self.state
                    .constraints
                    .push(Constraint(c_branch_ty.clone(), c_then));
                self.state
                    .constraints
                    .push(Constraint(c_branch_ty.clone(), c_else));
                c_branch_ty
            }
            Expr::While(_) => todo!(),
            Expr::For(_) => todo!(),
            Expr::Loop(_) => todo!(),
            Expr::Return(_) => todo!(),
            Expr::Let(let_expr) => self.state.expr_types_map[&let_expr.expr].clone(),
            Expr::Err => unreachable!(),
        };
        self.state.expr_types_map.insert(expr, c_ty);
    }
}

impl UnifyTypes {
    /// Solve the constraints by using substitutions.
    fn solve(&mut self) {
        let solutions = solve_constraints(self.state.constraints.clone(), &mut self.diagnostics);
    }
}

fn solve_constraints(
    mut constraints: Vec<Constraint>,
    diagnostics: &mut Diagnostics,
) -> HashMap<u32, ResolvedType> {
    let mut map = HashMap::new();
    loop {
        let substitutions = constraints
            .iter()
            .map(Constraint::generate_subs)
            .collect::<Vec<_>>();

        // If there are no substitutions to be made left, we are done.
        if !substitutions
            .iter()
            .any(|sub| matches!(sub, SubSearch::Sub(_, _)))
        {
            break;
        }

        // Remove all the constraints that are tautologies.
        constraints = constraints
            .into_iter()
            .zip(&substitutions)
            .filter(|(_, sub)| sub == &&SubSearch::Tautology)
            .map(|(constraint, _)| constraint)
            .collect();

        // Handle all substitution errors.
        for substitution in substitutions {
            match substitution {
                SubSearch::Contradiction => {
                    diagnostics.add(CouldNotUnifyTypes {
                        span: Span::dummy(FileId::DUMMY),
                    });
                }
                SubSearch::Sub(i, c_ty) => {
                    apply_substitution(&mut constraints, i, c_ty.clone());
                    map.insert(i, c_ty);
                }
                SubSearch::InfiniteType => diagnostics.add(CannotCreateInfiniteType {
                    span: Span::dummy(FileId::DUMMY),
                }),
                SubSearch::None => {}
                SubSearch::Tautology => {}
            }
        }
    }

    map
}

/// Substitute the type variable with id `i` with `c_ty`.
fn apply_substitution(constraints: &mut [Constraint], i: u32, c_ty: ResolvedType) {
    for c in constraints {
        c.0.apply_sub(i, c_ty.clone());
        c.1.apply_sub(i, c_ty.clone());
    }
}

#[derive(Debug, PartialEq, Eq)]
enum SubSearch {
    /// Error, cannot unify types.
    Contradiction,
    /// Apply this substitution.
    Sub(u32, ResolvedType),
    /// Error, type is infinite.
    InfiniteType,
    /// Nothing to do.
    None,
    /// This constraint is a tautology. We can therefore remove it.
    Tautology,
}

impl SubSearch {
    fn propagate_up(&self) -> bool {
        matches!(
            self,
            Self::Contradiction | Self::Sub(_, _) | Self::InfiniteType
        )
    }
}

impl Constraint {
    /// Generate a substitution from the constraint. There may be more than one substitution.
    fn generate_subs(&self) -> SubSearch {
        use ResolvedType::*;

        if std::mem::discriminant(&self.0) != std::mem::discriminant(&self.1) {
            return SubSearch::Contradiction;
        } else {
            match (&self.0, &self.1) {
                (Tmp(a), rhs) => {
                    if rhs.includes_type_var(*a) {
                        SubSearch::InfiniteType
                    } else {
                        SubSearch::Sub(*a, rhs.clone())
                    }
                }
                (lhs, Tmp(a)) => {
                    if lhs.includes_type_var(*a) {
                        SubSearch::InfiniteType
                    } else {
                        SubSearch::Sub(*a, lhs.clone())
                    }
                }
                (Tuple(lhs), Tuple(rhs)) => {
                    if lhs.len() != rhs.len() {
                        SubSearch::Contradiction
                    } else {
                        for (lhs, rhs) in lhs.iter().zip(rhs) {
                            let sub = Self(lhs.clone(), rhs.clone()).generate_subs();
                            if sub.propagate_up() {
                                return sub;
                            }
                        }
                        SubSearch::None
                    }
                }
                (
                    Fn {
                        arg: lhs_arg,
                        ret: lhs_ret,
                    },
                    Fn {
                        arg: rhs_arg,
                        ret: rhs_ret,
                    },
                ) => {
                    let sub1 = Constraint(*lhs_arg.clone(), *rhs_arg.clone()).generate_subs();
                    if sub1.propagate_up() {
                        return sub1;
                    }
                    let sub2 = Constraint(*lhs_ret.clone(), *rhs_ret.clone()).generate_subs();
                    if sub2.propagate_up() {
                        return sub2;
                    }
                    SubSearch::None
                }
                (
                    Constructed {
                        constructor: lhs_constructor,
                        arg: lhs_arg,
                    },
                    Constructed {
                        constructor: rhs_constructor,
                        arg: rhs_arg,
                    },
                ) => {
                    let sub1 = Constraint(*lhs_constructor.clone(), *rhs_constructor.clone())
                        .generate_subs();
                    if sub1.propagate_up() {
                        return sub1;
                    }
                    let sub2 = Constraint(*lhs_arg.clone(), *rhs_arg.clone()).generate_subs();
                    if sub2.propagate_up() {
                        return sub2;
                    }
                    SubSearch::None
                }
                (lhs, rhs) if lhs == rhs => SubSearch::Tautology,
                _ => SubSearch::None,
            }
        }
    }
}

impl ResolvedType {
    /// Thread through the substitution.
    fn apply_sub(&mut self, i: u32, c_ty: Self) {
        match self {
            ResolvedType::Tuple(types) => {
                for ty in types {
                    ty.apply_sub(i, c_ty.clone());
                }
            }
            ResolvedType::Fn { arg, ret } => {
                arg.apply_sub(i, c_ty.clone());
                ret.apply_sub(i, c_ty);
            }
            ResolvedType::Constructed { constructor, arg } => {
                constructor.apply_sub(i, c_ty.clone());
                arg.apply_sub(i, c_ty);
            }
            ResolvedType::Tmp(j) if i == *j => *self = c_ty,
            _ => {}
        }
    }

    fn includes_type_var(&self, i: u32) -> bool {
        match self {
            ResolvedType::Tuple(types) => types.iter().any(|ty| ty.includes_type_var(i)),
            ResolvedType::Fn { arg, ret } => arg.includes_type_var(i) || ret.includes_type_var(i),
            ResolvedType::Constructed { constructor, arg } => {
                constructor.includes_type_var(i) || arg.includes_type_var(i)
            }
            ResolvedType::Tmp(j) if i == *j => true,
            _ => false,
        }
    }
}
