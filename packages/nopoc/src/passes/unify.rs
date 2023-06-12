//! Type unification / type inference.
//!
//! We want to infer the type of every binding.
//!
//! Prefix all constraint types in code with `c_` to distinguish from syntax elements.

use std::collections::HashMap;

use la_arena::Arena;
use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::{Diagnostics, Report};

use crate::ast::visitor::{walk_expr, Visitor};
use crate::ast::{Expr, LetId, LetItem, Root, TypeDef, TypeId, TypeItem};
use crate::parser::lexer::{BinOp, UnaryOp};

use super::map::NodeMap;
use super::resolve::{
    Binding, BindingId, BindingsMap, ResolveSymbols, ResolvedBinding, ResolvedType,
    ResolvedTypePretty, TypeKind, TypesMap,
};

#[derive(Report)]
#[kind("error")]
#[message("could not unify types")]
struct CouldNotUnifyTypes<'a> {
    span: Span,
    #[label(message = "this is of type `{first}`")]
    first: Spanned<ResolvedTypePretty<'a>>,
    #[label(message = "but inferred to be `{second}`")]
    second: Spanned<ResolvedTypePretty<'a>>,
}

#[derive(Report)]
#[kind("error")]
#[message("cannot create infinite type")]
struct CannotCreateInfiniteType<'a> {
    span: Span,
    #[label(message = "this is of type `{first}`")]
    first: Spanned<ResolvedTypePretty<'a>>,
    #[label(message = "but inferred to be `{second}`")]
    second: Spanned<ResolvedTypePretty<'a>>,
}

#[derive(Debug)]
pub struct UnifyTypes {
    bindings: Arena<Binding>,
    bindings_map: BindingsMap,
    types_map: TypesMap,
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
///
/// The spans represent where the constraints are coming from.
#[derive(Debug, Clone)]
pub struct Constraint(Spanned<ResolvedType>, Spanned<ResolvedType>);

impl InferState {
    /// Create a new type variable.
    pub fn new_type_var(&mut self) -> ResolvedType {
        let counter = self.type_var_counter;
        self.type_var_counter += 1;
        ResolvedType::Tmp(counter)
    }
}

impl UnifyTypes {
    pub fn new(resolve: ResolveSymbols, diagnostics: Diagnostics) -> Self {
        Self {
            bindings: resolve.bindings,
            bindings_map: resolve.bindings_map,
            types_map: resolve.types_map,
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

        let solutions = self.solve();
        // Back substitute back into bindings.
        for (id, ty) in &mut self.state.binding_types_map {
            for (var, sub) in &solutions {
                ty.apply_sub(*var, sub.clone());
            }
            eprintln!(
                "{}\t\t: {}",
                self.bindings[*id].ident,
                ty.pretty(&self.types_map.items)
            );
        }
    }

    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        match &*item.def {
            TypeDef::Adt(adt) => {
                let type_data = match &self.types_map.items[idx].kind {
                    TypeKind::Record(_) => unreachable!(),
                    TypeKind::Adt(adt) => adt,
                };
                let c_ty = ResolvedType::of_type_item(idx, &self.types_map.items);
                for (data_constructor, variant) in
                    adt.data_constructors.iter().zip(&type_data.variants)
                {
                    let binding = self.bindings_map.data_constructors[&**data_constructor];
                    let c_data_constructor_ty =
                        ResolvedType::new_curried_function(&variant.types, c_ty.clone());
                    self.state
                        .binding_types_map
                        .insert(binding, c_data_constructor_ty);
                }
            }
            TypeDef::Record(_) => {}
            TypeDef::Err => unreachable!(),
        }
    }

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        // The type of the let item.
        let c_ty = spanned(item.ident.span(), self.state.new_type_var());
        let binding = self.bindings_map.let_items[&**item];
        self.state
            .binding_types_map
            .insert(binding, c_ty.clone().unspan());

        // Constraints for let params. Since params can have explicit type annotations, we can use
        // a shortcut and add the resolved types right away instead of inferring them.
        let c_params_ty = item
            .params
            .iter()
            .map(|param| {
                param.ty.as_ref().map_or_else(
                    || self.state.new_type_var(),
                    |ty| self.types_map.types[&*ty].clone(),
                )
            })
            .collect::<Vec<_>>();
        for (c_ty, param) in c_params_ty.iter().zip(&item.params) {
            let binding = self.bindings_map.params[&**param];
            self.state.binding_types_map.insert(binding, c_ty.clone());
        }

        // Constraint for return type.
        self.visit_expr(&item.expr);
        let c_expr_ty = spanned(
            item.expr.span(),
            self.state.expr_types_map[&**item.expr].clone(),
        );
        let c_ret_ty = if let Some(ret_ty) = &item.ret_ty {
            spanned(ret_ty.span(), self.types_map.types[&**ret_ty].clone())
        } else {
            spanned(item.expr.span(), self.state.new_type_var())
        };
        self.state
            .constraints
            .push(Constraint(c_ret_ty.clone(), c_expr_ty));

        // Add type for the whole let item.
        let c_fn_ty = spanned(
            item.span(),
            ResolvedType::new_curried_function(&c_params_ty, c_ret_ty.unspan()),
        );
        self.state.constraints.push(Constraint(c_ty, c_fn_ty));
    }

    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        // Handle expressions which create new bindings seperately since we want to create a type
        // var for the binding first.
        match &**expr {
            Expr::Let(let_expr) => {
                let binding = self.bindings_map.let_exprs[&**let_expr];
                let c_ret = if let Some(ret_ty) = &let_expr.ret_ty {
                    spanned(ret_ty.span(), self.types_map.types[&**ret_ty].clone())
                } else {
                    spanned(let_expr.ident.span(), self.state.new_type_var())
                };
                self.state
                    .binding_types_map
                    .insert(binding, c_ret.clone().unspan());
                // Constrain let binding expression.
                self.visit_expr(&let_expr.expr);
                let c_expr = self.state.expr_types_map[&**let_expr.expr].clone();
                self.state
                    .constraints
                    .push(Constraint(c_ret, spanned(let_expr.expr.span(), c_expr)));

                self.visit_expr(&let_expr._in);
                let c_in = self.state.expr_types_map[&**let_expr._in].clone();
                self.state.expr_types_map.insert(expr, c_in);
                return;
            }
            Expr::Lambda(lambda_expr) => {
                let c_params = lambda_expr
                    .params
                    .iter()
                    .map(|_| self.state.new_type_var())
                    .collect::<Vec<_>>();
                for (param, c_param) in lambda_expr.params.iter().zip(&c_params) {
                    let binding = self.bindings_map.lambda_params[param];
                    self.state.binding_types_map.insert(binding, c_param.clone());
                }
                self.visit_expr(&lambda_expr.expr);
                let c_expr = self.state.expr_types_map[&*lambda_expr.expr].clone();

                let c_ty = ResolvedType::new_curried_function(&c_params, c_expr);
                self.state.expr_types_map.insert(expr, c_ty);
                return;
            }
            _ => (),
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
            Expr::Lambda(_) => unreachable!(),
            Expr::Tuple(tuple_expr) => ResolvedType::Tuple(
                tuple_expr
                    .elements
                    .iter()
                    .map(|element| self.state.expr_types_map[element].clone())
                    .collect(),
            ),
            Expr::Record(_) => todo!("unify record types"),
            Expr::Binary(binary_expr) => {
                let c_lhs = self.state.expr_types_map[&*binary_expr.lhs].clone();
                let c_rhs = self.state.expr_types_map[&*binary_expr.rhs].clone();
                // Handle fn calls seperately.
                if *binary_expr.op == BinOp::FnCall {
                    // Constrain LHS to be a function that takes the RHS.
                    let c_ret = self.state.new_type_var();
                    self.state.constraints.push(Constraint(
                        spanned(binary_expr.lhs.span(), c_lhs),
                        spanned(
                            binary_expr.lhs.span(),
                            ResolvedType::new_curried_function(&[c_rhs], c_ret.clone()),
                        ),
                    ));
                    c_ret
                } else {
                    // TODO: binary operations on types other than int (introduce new operator or
                    // ad-hoc polymorphism?)
                    let (c_arg, c_ret) = match *binary_expr.op {
                        BinOp::Plus
                        | BinOp::Minus
                        | BinOp::Mul
                        | BinOp::Div
                        | BinOp::Mod
                        | BinOp::And
                        | BinOp::Or
                        | BinOp::Xor
                        | BinOp::ShiftLeft
                        | BinOp::ShiftRight
                        | BinOp::UnsignedShiftRight => (ResolvedType::Int, ResolvedType::Int),
                        BinOp::Eq | BinOp::Neq => (self.state.new_type_var(), ResolvedType::Bool),
                        BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                            (ResolvedType::Int, ResolvedType::Bool)
                        }
                        BinOp::AndAnd | BinOp::OrOr => (ResolvedType::Bool, ResolvedType::Bool),
                        BinOp::Dot => todo!(),
                        BinOp::FnCall => unreachable!(),
                    };
                    self.state.constraints.push(Constraint(
                        spanned(binary_expr.lhs.span(), c_lhs),
                        spanned(binary_expr.op.span(), c_arg.clone()),
                    ));
                    self.state.constraints.push(Constraint(
                        spanned(binary_expr.rhs.span(), c_rhs),
                        spanned(binary_expr.op.span(), c_arg),
                    ));
                    c_ret
                }
            }
            Expr::Unary(unary_expr) => match *unary_expr.op {
                UnaryOp::Neg => {
                    let c_expr = self.state.expr_types_map[&*unary_expr.expr].clone();
                    self.state.constraints.push(Constraint(
                        spanned(unary_expr.expr.span(), c_expr),
                        spanned(unary_expr.op.span(), ResolvedType::Int),
                    ));
                    ResolvedType::Int
                }
                UnaryOp::Not => {
                    let c_expr = self.state.expr_types_map[&*unary_expr.expr].clone();
                    self.state.constraints.push(Constraint(
                        spanned(unary_expr.expr.span(), c_expr),
                        spanned(unary_expr.op.span(), ResolvedType::Bool),
                    ));
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
                self.state.constraints.push(Constraint(
                    spanned(if_expr.cond.span(), c_cond_ty),
                    spanned(if_expr.cond.span(), ResolvedType::Bool),
                ));
                let c_branch_ty = spanned(if_expr.span(), self.state.new_type_var());
                let c_then = spanned(
                    if_expr.then.span(),
                    self.state.expr_types_map[&if_expr.then].clone(),
                );
                let c_else = spanned(
                    if_expr.else_.span(),
                    self.state.expr_types_map[&if_expr.else_].clone(),
                );
                self.state
                    .constraints
                    .push(Constraint(c_branch_ty.clone(), c_then));
                self.state
                    .constraints
                    .push(Constraint(c_branch_ty.clone(), c_else));
                c_branch_ty.unspan()
            }
            Expr::While(_) => todo!(),
            Expr::For(_) => todo!(),
            Expr::Loop(_) => todo!(),
            Expr::Return(_) => todo!(),
            Expr::Let(_) => unreachable!(),
            Expr::Err => unreachable!(),
        };
        self.state.expr_types_map.insert(expr, c_ty);
    }
}

impl UnifyTypes {
    /// Solve the constraints by using substitutions.
    fn solve(&mut self) -> HashMap<u32, ResolvedType> {
        let mut constraints = self.state.constraints.clone();

        let mut solutions = HashMap::<u32, ResolvedType>::new();
        loop {
            let sub_search = constraints
                .iter()
                .cloned()
                .map(|constraint| {
                    (
                        constraint.clone(),
                        Constraint::generate_subs(constraint.0.unspan(), constraint.1.unspan()),
                    )
                })
                .collect::<Vec<_>>();

            let mut subs = sub_search
                .iter()
                .filter_map(|(_, sub)| match sub {
                    SubSearch::Sub(i, c_ty) => Some((*i, c_ty.clone())),
                    _ => None,
                })
                .collect::<Vec<_>>();

            // Emit all errors found during sub search.
            constraints = sub_search
                .into_iter()
                .filter_map(|(c, sub)| match sub {
                    SubSearch::Contradiction => {
                        self.diagnostics.add(CouldNotUnifyTypes {
                            span: c.0.span(),
                            first: spanned(c.0.span(), c.0.pretty(&self.types_map.items)),
                            second: spanned(c.1.span(), c.1.pretty(&self.types_map.items)),
                        });
                        None
                    }
                    SubSearch::Sub(_, _) => Some(c),
                    SubSearch::InfiniteType => {
                        self.diagnostics.add(CannotCreateInfiniteType {
                            span: c.0.span(),
                            first: spanned(c.0.span(), c.0.pretty(&self.types_map.items)),
                            second: spanned(c.1.span(), c.1.pretty(&self.types_map.items)),
                        });
                        None
                    }
                    SubSearch::None => Some(c),
                    SubSearch::Tautology => None,
                })
                .collect();

            // Apply all substitutions.
            for sub_i in 0..subs.len() {
                let (i, c_ty) = subs[sub_i].clone();
                // Substitute in constraints.
                apply_subs(&mut constraints, i, c_ty.clone());
                // Substitute in existing solutions.
                for (_, solution) in &mut solutions {
                    solution.apply_sub(i, c_ty.clone());
                }
                // Substitute in all other substitutions which have not already been substituted.
                for sub_j in sub_i + 1..subs.len() {
                    subs[sub_j].1.apply_sub(i, c_ty.clone());
                }
                solutions.insert(i, c_ty);
            }

            // If we did not make any substitutions, then we are done.
            if subs.is_empty() {
                break;
            }
        }

        solutions
    }
}

/// Substitute the type variable with id `i` with `c_ty`.
fn apply_subs(constraints: &mut [Constraint], i: u32, c_ty: ResolvedType) {
    for c in constraints {
        c.0.apply_sub(i, c_ty.clone());
        c.1.apply_sub(i, c_ty.clone());
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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
    fn generate_subs(lhs: ResolvedType, rhs: ResolvedType) -> SubSearch {
        use ResolvedType::*;

        match (lhs, rhs) {
            (Tmp(a), ty) | (ty, Tmp(a)) => {
                if ty == Tmp(a) {
                    SubSearch::None
                } else if ty.includes_type_var(a) {
                    SubSearch::InfiniteType
                } else {
                    SubSearch::Sub(a, ty.clone())
                }
            }
            (Tuple(lhs), Tuple(rhs)) => {
                if lhs.len() != rhs.len() {
                    SubSearch::Contradiction
                } else {
                    for (lhs, rhs) in lhs.into_iter().zip(rhs) {
                        let sub = Self::generate_subs(lhs, rhs);
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
                let sub1 = Self::generate_subs(*lhs_arg, *rhs_arg);
                if sub1.propagate_up() {
                    return sub1;
                }
                let sub2 = Self::generate_subs(*lhs_ret, *rhs_ret);
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
                let sub1 = Self::generate_subs(*lhs_constructor, *rhs_constructor);
                if sub1.propagate_up() {
                    return sub1;
                }
                let sub2 = Self::generate_subs(*lhs_arg, *rhs_arg);
                if sub2.propagate_up() {
                    return sub2;
                }
                SubSearch::None
            }
            (lhs, rhs) if lhs == rhs => SubSearch::Tautology,
            _ => SubSearch::Contradiction,
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
