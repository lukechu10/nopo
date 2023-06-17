//! Type unification / type inference.
//!
//! We want to infer the type of every binding.
//!
//! Prefix all constraint types in code with `c_` to distinguish from syntax elements.

use std::collections::{BTreeMap, HashMap};

use la_arena::Arena;
use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::{Diagnostics, Report};
use nopo_parser::ast::{Expr, LetId, LetItem, LitExpr, Pattern, Root, TypeDef, TypeId, TypeItem};
use nopo_parser::lexer::{BinOp, UnaryOp};
use nopo_parser::visitor::{walk_expr, walk_pattern, Visitor};

use crate::check_records::TypeCheckRecords;
use crate::resolve::Binding;

use super::map::NodeMap;
use super::resolve::{
    BindingId, BindingsMap, ResolveSymbols, ResolvedBinding, ResolvedType, ResolvedTypePretty,
    TypeKind, TypeVar, TypesMap,
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

/// Type unification pass (type inference).
#[derive(Debug)]
pub struct UnifyTypes {
    pub bindings: Arena<Binding>,
    pub bindings_map: BindingsMap,
    /// Contains the type of all the bindings.
    pub binding_types_map: HashMap<BindingId, ResolvedType>,
    pub types_map: TypesMap,
    state: GenerateConstraints,
    diagnostics: Diagnostics,
}

/// Temporary state used in unifying types.
#[derive(Debug, Default)]
pub struct GenerateConstraints {
    type_var_counter: u32,
    /// Keep track of all the types of all the expressions in this item.
    pub expr_types_map: NodeMap<Expr, ResolvedType>,
    /// Keep track of all the types of the patterns in this item.
    pub pattern_types_map: NodeMap<Pattern, ResolvedType>,
    /// A list of constraints.
    pub constraints: Vec<Constraint>,
}

/// Represents a type constraint, constraing the LHS and the RHS together.
///
/// The spans represent where the constraints are coming from.
#[derive(Debug, Clone)]
pub struct Constraint(pub Spanned<ResolvedType>, pub Spanned<ResolvedType>);

impl GenerateConstraints {
    /// Create a new type variable.
    pub fn new_type_var(&mut self) -> ResolvedType {
        let counter = self.type_var_counter;
        self.type_var_counter += 1;
        ResolvedType::Var(counter.to_string().into())
    }
}

impl UnifyTypes {
    pub fn new(resolve: ResolveSymbols, diagnostics: Diagnostics) -> Self {
        Self {
            bindings: resolve.bindings,
            bindings_map: resolve.bindings_map,
            binding_types_map: HashMap::new(),
            types_map: resolve.types_map,
            state: GenerateConstraints::default(),
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
            self.state = GenerateConstraints::default();
            self.visit_let_item(idx, item);
            let mut state = std::mem::take(&mut self.state);

            let solutions = state.solve(&self.diagnostics, &self.types_map);

            let binding_id = self.bindings_map.let_items[&*item];
            let mut binding_ty = self.binding_types_map[&binding_id].clone();

            // Substitute in solutions.
            for (var, sub) in solutions {
                binding_ty.apply_sub(&var, sub.clone());
                for expr_ty in state.expr_types_map.map.values_mut() {
                    expr_ty.apply_sub(&var, sub.clone());
                }
            }

            // Get types of member and record expressions.
            let mut check_records =
                TypeCheckRecords::new(self, &mut state, self.diagnostics.clone());
            check_records.visit_let_item(idx, item);

            // Solve constraints again now that we have types from records.
            let solutions = state.solve(&self.diagnostics, &self.types_map);
            for (var, sub) in solutions {
                binding_ty.apply_sub(&var, sub.clone());
                for expr_ty in self.state.expr_types_map.map.values_mut() {
                    expr_ty.apply_sub(&var, sub.clone());
                }
            }

            // Generalize the type of this binding.
            let binding_ty = binding_ty.generalize();

            let pretty = binding_ty.pretty(&self.types_map.items);
            eprintln!(" {}: {pretty}", item.ident);
            self.binding_types_map.insert(binding_id, binding_ty);
        }
    }

    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        match &*item.def {
            TypeDef::Adt(adt) => {
                let type_data = match &self.types_map.items[idx].kind {
                    TypeKind::Adt(adt) => adt,
                    _ => unreachable!(),
                };
                let c_ty = ResolvedType::of_type_item(idx, &self.types_map.items);
                for (data_constructor, variant) in
                    adt.data_constructors.iter().zip(&type_data.variants)
                {
                    let binding = self.bindings_map.data_constructors[&**data_constructor];
                    // We can generalize here since we don't do type inference for type items.
                    let c_data_constructor_ty =
                        ResolvedType::new_curried_function(&variant.types, c_ty.clone())
                            .generalize();
                    let pretty = c_data_constructor_ty.pretty(&self.types_map.items);
                    eprintln!("{:>20}: {pretty}", data_constructor.ident);
                    self.binding_types_map
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
        self.binding_types_map
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
            self.binding_types_map.insert(binding, c_ty.clone());
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
            .push(Constraint(c_expr_ty, c_ret_ty.clone()));

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
                self.binding_types_map
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
                    self.binding_types_map.insert(binding, c_param.clone());
                }
                self.visit_expr(&lambda_expr.expr);
                let c_expr = self.state.expr_types_map[&*lambda_expr.expr].clone();

                let c_ty = ResolvedType::new_curried_function(&c_params, c_expr);
                self.state.expr_types_map.insert(expr, c_ty);
                return;
            }
            Expr::Match(match_expr) => {
                self.visit_expr(&match_expr.matched);
                let c_matched = self.state.expr_types_map[&match_expr.matched].clone();
                let c_ret_ty = spanned(match_expr.span(), self.state.new_type_var());
                for arm in &match_expr.arms {
                    self.visit_pattern(&arm.pattern);
                    let c_pat_ty = self.state.pattern_types_map[&arm.pattern].clone();
                    self.state.constraints.push(Constraint(
                        spanned(arm.pattern.span(), c_pat_ty),
                        spanned(match_expr.matched.span(), c_matched.clone()),
                    ));
                    self.visit_expr(&arm.expr);
                    let c_arm_ty = spanned(
                        arm.expr.span(),
                        self.state.expr_types_map[&arm.expr].clone(),
                    );
                    self.state
                        .constraints
                        .push(Constraint(c_ret_ty.clone(), c_arm_ty));
                }
                // TODO: Constrain the type of the matched expression to the types of the patterns.
                self.state.expr_types_map.insert(expr, c_ret_ty.unspan());
                return;
            }
            _ => (),
        }

        // This ensures that self.state.expr_types_map is instantiated for all child nodes.
        match &**expr {
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => self.visit_expr(&bin_expr.lhs),
            _ => walk_expr(self, expr),
        }

        let c_ty = match &**expr {
            Expr::Ident(ident_expr) => {
                // Lookup binding and set that as the expression of the type.
                let binding = &self.bindings_map.idents[&**ident_expr];
                if let ResolvedBinding::Ok(binding) = binding {
                    let c_binding = self.binding_types_map[binding].clone();
                    self.state.instantiate(c_binding)
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
            // We don't try to infer record types from their fields.
            Expr::Record(_) => self.state.new_type_var(),
            // We don't try to infer member expressions from the field.
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => self.state.new_type_var(),
            Expr::Binary(bin_expr) => {
                let c_lhs = self.state.expr_types_map[&*bin_expr.lhs].clone();
                let c_rhs = self.state.expr_types_map[&*bin_expr.rhs].clone();
                // Handle fn calls seperately.
                if *bin_expr.op == BinOp::FnCall {
                    // Constrain LHS to be a function that takes the RHS.
                    let c_ret = self.state.new_type_var();
                    self.state.constraints.push(Constraint(
                        spanned(bin_expr.lhs.span(), c_lhs),
                        spanned(
                            bin_expr.lhs.span(),
                            ResolvedType::new_curried_function(&[c_rhs], c_ret.clone()),
                        ),
                    ));
                    c_ret
                } else {
                    // TODO: binary operations on types other than int (introduce new operator or
                    // ad-hoc polymorphism?)
                    let (c_arg, c_ret) = match *bin_expr.op {
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
                        spanned(bin_expr.lhs.span(), c_lhs),
                        spanned(bin_expr.op.span(), c_arg.clone()),
                    ));
                    self.state.constraints.push(Constraint(
                        spanned(bin_expr.rhs.span(), c_rhs),
                        spanned(bin_expr.op.span(), c_arg),
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
            Expr::Lit(lit) => match &**lit {
                LitExpr::Bool(_) => ResolvedType::Bool,
                LitExpr::Int(_) => ResolvedType::Int,
                LitExpr::Float(_) => ResolvedType::Float,
                LitExpr::String(_) => ResolvedType::String,
                LitExpr::Char(_) => ResolvedType::Char,
            },
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
            Expr::Lambda(_) => unreachable!(),
            Expr::Match(_) => unreachable!(),
            Expr::Err => unreachable!(),
        };
        self.state.expr_types_map.insert(expr, c_ty);
    }

    fn visit_pattern(&mut self, pattern: &Spanned<Pattern>) {
        walk_pattern(self, pattern);
        let c_ty = match &**pattern {
            Pattern::Path(_) => {
                if let Some(symbol) = self.bindings_map.pattern_tags.get(pattern) {
                    if let ResolvedBinding::Ok(symbol) = symbol {
                        let c_fn_ty = self.binding_types_map[symbol].clone();
                        c_fn_ty.uncurry_function().1
                    } else {
                        self.state.new_type_var()
                    }
                } else {
                    let binding = self.bindings_map.pattern[pattern];
                    let c_ty = self.state.new_type_var();
                    self.binding_types_map.insert(binding, c_ty.clone());
                    c_ty
                }
            }
            Pattern::Adt(adt) => {
                let symbol = &self.bindings_map.pattern_tags[pattern];
                if let ResolvedBinding::Ok(symbol) = symbol {
                    let c_fn_ty = self.binding_types_map[symbol].clone();
                    let (c_fn_args, c_ty) = c_fn_ty.uncurry_function();
                    // Constrain the types of all the fields.
                    for (sub_pattern, c_fn_arg) in adt.of.iter().zip(c_fn_args) {
                        let c_sub_pattern = self.state.pattern_types_map[sub_pattern].clone();
                        self.state.constraints.push(Constraint(
                            spanned(sub_pattern.span(), c_sub_pattern),
                            spanned(sub_pattern.span(), c_fn_arg),
                        ));
                    }
                    c_ty
                } else {
                    self.state.new_type_var()
                }
            }
            Pattern::Lit(lit) => match &**lit {
                LitExpr::Bool(_) => ResolvedType::Bool,
                LitExpr::Int(_) => ResolvedType::Int,
                LitExpr::Float(_) => ResolvedType::Float,
                LitExpr::String(_) => ResolvedType::String,
                LitExpr::Char(_) => ResolvedType::Char,
            },
            Pattern::Err => self.state.new_type_var(),
        };
        self.state.pattern_types_map.insert(pattern, c_ty);
    }
}

impl GenerateConstraints {
    /// Solve the constraints by using substitutions.
    fn solve(
        &mut self,
        diagnostics: &Diagnostics,
        types_map: &TypesMap,
    ) -> BTreeMap<TypeVar, ResolvedType> {
        let mut constraints = self.constraints.clone();

        let mut solutions = BTreeMap::<TypeVar, ResolvedType>::new();
        loop {
            let sub_search = constraints
                .iter()
                .cloned()
                .map(|constraint| {
                    (
                        constraint.clone(),
                        Constraint::generate_subs(&constraint.0.unspan(), &constraint.1.unspan()),
                    )
                })
                .collect::<Vec<_>>();

            let mut subs = sub_search
                .iter()
                .filter_map(|(_, sub)| match sub {
                    SubSearch::Sub(var, c_ty) => Some((var.clone(), c_ty.clone())),
                    _ => None,
                })
                .collect::<Vec<_>>();

            // Emit all errors found during sub search.
            constraints = sub_search
                .into_iter()
                .filter_map(|(c, sub)| match sub {
                    SubSearch::Contradiction => {
                        diagnostics.add(CouldNotUnifyTypes {
                            span: c.0.span(),
                            first: spanned(c.0.span(), c.0.pretty(&types_map.items)),
                            second: spanned(c.1.span(), c.1.pretty(&types_map.items)),
                        });
                        None
                    }
                    SubSearch::Sub(_, _) => Some(c),
                    SubSearch::InfiniteType => {
                        diagnostics.add(CannotCreateInfiniteType {
                            span: c.0.span(),
                            first: spanned(c.0.span(), c.0.pretty(&types_map.items)),
                            second: spanned(c.1.span(), c.1.pretty(&types_map.items)),
                        });
                        None
                    }
                    SubSearch::None => Some(c),
                    SubSearch::Tautology => None,
                })
                .collect();

            // Apply all substitutions.
            for sub_i in 0..subs.len() {
                let (var, c_ty) = subs[sub_i].clone();
                // Substitute in constraints.
                apply_subs(&mut constraints, &var, c_ty.clone());
                // Substitute in existing solutions.
                for (_, solution) in &mut solutions {
                    solution.apply_sub(&var, c_ty.clone());
                }
                // Substitute in all other substitutions which have not already been substituted.
                for sub_j in sub_i + 1..subs.len() {
                    subs[sub_j].1.apply_sub(&var, c_ty.clone());
                }
                solutions.insert(var.clone(), c_ty);
            }

            // If we did not make any substitutions, then we are done.
            if subs.is_empty() {
                break;
            }
        }

        self.constraints = constraints;
        solutions
    }

    /// Instantiate all the for alls on the left of the type. Will not instantiate for alls in the
    /// middle of a type.
    fn instantiate(&mut self, ty: ResolvedType) -> ResolvedType {
        match ty {
            ResolvedType::ForAll { var, mut ty } => {
                let new_var = self.new_type_var();
                ty.apply_sub(&var, new_var);
                self.instantiate(*ty)
            }
            _ => ty,
        }
    }
}

/// Substitute the type variable with id `i` with `c_ty`.
fn apply_subs(constraints: &mut [Constraint], var: &TypeVar, c_ty: ResolvedType) {
    for c in constraints {
        c.0.apply_sub(var, c_ty.clone());
        c.1.apply_sub(var, c_ty.clone());
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum SubSearch {
    /// Error, cannot unify types.
    Contradiction,
    /// Apply this substitution.
    Sub(TypeVar, ResolvedType),
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
    fn generate_subs(lhs: &ResolvedType, rhs: &ResolvedType) -> SubSearch {
        use ResolvedType::*;

        match (lhs, rhs) {
            (Var(a), ty) | (ty, Var(a)) => {
                if matches!(ty, Var(b) if a == b) {
                    SubSearch::None
                } else if ty.includes_type_var(a) {
                    SubSearch::InfiniteType
                } else {
                    SubSearch::Sub(a.clone(), ty.clone())
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
                let sub1 = Self::generate_subs(lhs_arg, rhs_arg);
                if sub1.propagate_up() {
                    return sub1;
                }
                let sub2 = Self::generate_subs(lhs_ret, rhs_ret);
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
                let sub1 = Self::generate_subs(lhs_constructor, rhs_constructor);
                if sub1.propagate_up() {
                    return sub1;
                }
                let sub2 = Self::generate_subs(lhs_arg, rhs_arg);
                if sub2.propagate_up() {
                    return sub2;
                }
                SubSearch::None
            }
            (ForAll { var: _, ty: lhs_ty }, ForAll { var: _, ty: rhs_ty }) => {
                Self::generate_subs(lhs_ty, rhs_ty)
            }
            (lhs, rhs) if lhs == rhs => SubSearch::Tautology,
            _ => SubSearch::Contradiction,
        }
    }
}

impl ResolvedType {
    /// Thread through the substitution.
    fn apply_sub(&mut self, var: &TypeVar, c_ty: Self) {
        match self {
            ResolvedType::Tuple(types) => {
                for ty in types {
                    ty.apply_sub(var, c_ty.clone());
                }
            }
            ResolvedType::Fn { arg, ret } => {
                arg.apply_sub(var, c_ty.clone());
                ret.apply_sub(var, c_ty);
            }
            ResolvedType::Constructed { constructor, arg } => {
                constructor.apply_sub(var, c_ty.clone());
                arg.apply_sub(var, c_ty);
            }
            ResolvedType::ForAll { var: x, ty } if var != x => ty.apply_sub(var, c_ty),
            ResolvedType::Var(x) | ResolvedType::Param(x) if x == var => *self = c_ty,
            _ => {}
        }
    }

    fn includes_type_var(&self, var: &TypeVar) -> bool {
        match self {
            ResolvedType::Tuple(types) => types.iter().any(|ty| ty.includes_type_var(var)),
            ResolvedType::Fn { arg, ret } => {
                arg.includes_type_var(var) || ret.includes_type_var(var)
            }
            ResolvedType::Constructed { constructor, arg } => {
                constructor.includes_type_var(var) || arg.includes_type_var(var)
            }
            ResolvedType::ForAll { var: x, ty } if var != x => ty.includes_type_var(var),
            ResolvedType::Var(x) if var == x => true,
            _ => false,
        }
    }

    /// Generalise the type, i.e. replace all free variables with bound variables in the scope
    /// of a universal quantifier.
    fn generalize(self) -> Self {
        // 1 - Get all free variables.
        let mut free = Vec::new();
        self.get_free_variables(&mut Vec::new(), &mut free);
        let free = free.into_iter().cloned().collect::<Vec<_>>();
        // 2 - Add universal quantification over all these variables.
        let mut ty = self;
        for var in free {
            ty = Self::ForAll {
                var: var.clone(),
                ty: Box::new(ty),
            }
        }
        ty
    }

    /// Get all type variables and type parameters.
    fn get_free_variables<'a>(&'a self, bound: &mut Vec<&'a TypeVar>, free: &mut Vec<&'a TypeVar>) {
        match self {
            ResolvedType::Tuple(types) => {
                for ty in types {
                    ty.get_free_variables(bound, free);
                }
            }
            ResolvedType::Fn { arg, ret } => {
                arg.get_free_variables(bound, free);
                ret.get_free_variables(bound, free);
            }
            ResolvedType::Constructed { constructor, arg } => {
                constructor.get_free_variables(bound, free);
                arg.get_free_variables(bound, free);
            }
            ResolvedType::ForAll { var, ty } => {
                bound.push(var);
                ty.get_free_variables(bound, free);
                bound.pop();
            }
            ResolvedType::Var(x) | ResolvedType::Param(x) => {
                if bound.iter().find(|y| &x == *y).is_none()
                    && free.iter().find(|y| &x == *y).is_none()
                {
                    free.push(x);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use crate::tests::{check_fail, check_types};

    #[test]
    fn literal_types() {
        check_types("let x = 42", expect!["x: int"]);
        check_types("let x = 3.141", expect!["x: float"]);
        check_types("let x = \"Hello World!\"", expect!["x: string"]);
        check_types("let x = 'a'", expect!["x: char"]);
    }

    #[test]
    fn let_items() {
        check_types(
            "let neg x = -x
             let sum x y = x + y
             let double z = sum z z",
            expect![[r#"
                neg: (int -> int)
                x: {1}
                sum: (int -> (int -> int))
                x: {1}
                y: {2}
                double: (int -> int)
                z: {1}"#]],
        );
    }

    #[test]
    fn let_items_with_explicit_type_annotations() {
        check_types("let x: int = 42", expect!["x: int"]);
        check_fail(
            "let x: string = 42",
            expect![[r#"
                Error: could not unify types
                   ╭─[<test>:1:17]
                   │
                 1 │ let x: string = 42
                   │        ───┬──   ─┬  
                   │           ╰───────── but inferred to be `string`
                   │                  │  
                   │                  ╰── this is of type `int`
                ───╯
            "#]],
        );
        check_types(
            "let add_one (x: int): int = x + 1",
            expect![[r#"
                add_one: (int -> int)
                x: int"#]],
        );
    }

    #[test]
    fn polymorphic_let() {
        check_types(
            "let id x = x
             let a = id 1
             let b = id \"Hello World!\"",
            expect![[r#"
                id: forall '2 . ({2} -> {2})
                x: {1}
                a: int
                b: string"#]],
        );
    }

    #[test]
    fn adt() {
        check_types(
            "type A = A
             let a = A",
            expect![[r#"
                A: A
                a: A"#]],
        );
        check_types(
            "type A = A of int
             let a = A 1",
            expect![[r#"
                A: (int -> A)
                a: A"#]],
        );
        check_types(
            "type List 'a = Nil | Cons of 'a (List 'a)
             let my_list = Cons 1 (Cons 2 (Cons 3 Nil))
             let push list x = Cons x list",
            expect![[r#"
                Nil: forall 'a . (List {a})
                Cons: forall 'a . ('a -> ((List 'a) -> (List {a})))
                my_list: (List int)
                push: forall '2 . ((List {2}) -> ({2} -> (List {2})))
                list: {1}
                x: {2}"#]],
        );
    }

    #[test]
    fn records() {
        check_types(
            "type User = {
                name: string,
                email: string,
                id: int,
            }
            let my_user: User = {
                name = \"Test\",
                email = \"test@test.com\",
                id = 123
            }
            let get_name (user: User) = user.name",
            expect![[r#"
                my_user: User
                get_name: (User -> string)
                user: User"#]],
        );
        check_fail(
            "type User = {
                name: string,
                email: string,
                id: int,
            }
            let get_name user = user.name",
            expect![[r#"
                Error: type must be known at this point
                   ╭─[<test>:6:33]
                   │
                 6 │             let get_name user = user.name
                   │                                 ──┬─  
                   │                                   ╰─── Type must be known at this point
                ───╯
            "#]],
        );
        check_fail(
            "type User = {
                name: string,
                email: string,
                id: int,
            }
            let get_name (user: User) = user.unknown_field",
            expect![[r#"
                Error: unknown field `unknown_field`
                   ╭─[<test>:6:46]
                   │
                 6 │             let get_name (user: User) = user.unknown_field
                   │                                              ──────┬──────  
                   │                                                    ╰──────── Field `unknown_field` not found on type `User`
                ───╯
            "#]],
        );
    }

    #[test]
    fn expressions() {
        check_types(
            "let a =
                 let b = 42
                 in b",
            expect![[r#"
                b: {1}
                a: int"#]],
        );
        check_types(
            "let a =
                 let b: string = \"abc\"
                 in b",
            expect![[r#"
                b: string
                a: string"#]],
        );
        check_types(
            "let compose f g = \\x -> f (g x)
             let a x = x + 1
             let b x = x * 2
             let ab = compose a b
             let y = ab 1",
            expect![[r#"
                compose: forall '3 . forall '5 . forall '4 . (({4} -> {5}) -> (({3} -> {4}) -> ({3} -> {5})))
                f: {1}
                g: {2}
                x: {3}
                a: (int -> int)
                x: {1}
                b: (int -> int)
                x: {1}
                ab: (int -> int)
                y: int"#]],
        );
        check_types("let a = if true then 0 else 1", expect!["a: int"]);
    }

    #[test]
    fn recursive_let_items() {
        check_types(
            "let factorial n = if n = 0 then 1 else n * factorial (n - 1)",
            expect![[r#"
                factorial: (int -> int)
                n: {1}"#]],
        );
    }

    #[test]
    fn recursive_types() {
        check_types(
            "type List 'a = Nil | Cons of 'a (List 'a)",
            expect![[r#"
                Nil: forall 'a . (List {a})
                Cons: forall 'a . ('a -> ((List 'a) -> (List {a})))"#]],
        );
    }

    #[test]
    fn infinite_type() {
        check_fail(
            "let f x = x x",
            expect![[r#"
                Error: cannot create infinite type
                   ╭─[<test>:1:11]
                   │
                 1 │ let f x = x x
                   │           ┬  
                   │           ╰── this is of type `{1}`
                   │           │  
                   │           ╰── but inferred to be `({1} -> {2})`
                ───╯
            "#]],
        );
    }
}
