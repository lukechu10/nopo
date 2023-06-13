//! Type check record and member expressions.
//!
//! This runs after type unification since we don't use record fields to infer types.

use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::{Diagnostics, Report};

use nopo_parser::ast::{Expr, Ident};
use nopo_parser::lexer::BinOp;
use nopo_parser::visitor::{walk_expr, Visitor};

use super::resolve::{ResolvedType, ResolvedTypePretty, TypeKind};
use super::unify::{Constraint, GenerateConstraints, UnifyTypes};

#[derive(Report)]
#[kind("error")]
#[message("field must be an identifier")]
struct FieldMustBeIdentifier {
    span: Span,
    #[label(message = "This must be an identifier")]
    expr: Span,
}

#[derive(Report)]
#[kind("error")]
#[message("type must be known at this point")]
struct TypeMustBeKnown {
    span: Span,
    #[label(message = "Type must be known at this point")]
    expr: Span,
}

#[derive(Report)]
#[kind("error")]
#[message("not a record type")]
struct NotRecordType<'a> {
    span: Span,
    #[label(message = "Type `{ty}` is not a record type")]
    expr: Span,
    ty: ResolvedTypePretty<'a>,
}

#[derive(Report)]
#[kind("error")]
#[message("unknown field `{field}`")]
struct UnknownField<'a> {
    span: Span,
    #[label(message = "Field `{field}` not found on type `{ty}`")]
    field: Spanned<Ident>,
    ty: ResolvedTypePretty<'a>,
}

#[derive(Report)]
#[kind("error")]
#[message("missing record fields")]
struct MissingFields {
    span: Span,
    #[label(message = "Missing fields: {missing}")]
    expr: Span,
    missing: String,
}

#[derive(Debug)]
pub struct TypeCheckRecords<'a> {
    unify: &'a mut UnifyTypes,
    state: &'a mut GenerateConstraints,
    diagnostics: Diagnostics,
}

impl<'a> TypeCheckRecords<'a> {
    pub fn new(
        unify: &'a mut UnifyTypes,
        state: &'a mut GenerateConstraints,
        diagnostics: Diagnostics,
    ) -> Self {
        Self {
            unify,
            state,
            diagnostics,
        }
    }
}

impl<'a> TypeCheckRecords<'a> {
    fn resolve_field_ty(&mut self, expr: &Spanned<Expr>, field: &Spanned<Expr>) -> ResolvedType {
        // Check that field is an identifier.
        let Expr::Ident(field) = &**field else {
            self.diagnostics.add(FieldMustBeIdentifier {
                span: field.span(),
                expr: field.span(),
            });
            return ResolvedType::Err;
        };
        let ty = &mut self.state.expr_types_map[&*expr];

        if let ResolvedType::Var(_) | ResolvedType::Param(_) = ty {
            self.diagnostics.add(TypeMustBeKnown {
                span: expr.span(),
                expr: expr.span(),
            });
            ResolvedType::Err
        } else if let Some(id) = ty.ident_of_constructed() {
            let data_def = &self.unify.types_map.items[id];
            match &data_def.kind {
                TypeKind::Record(record_def) => match record_def.fields.get(field.ident.as_ref()) {
                    Some(ty) => ty.clone(),
                    None => {
                        self.diagnostics.add(UnknownField {
                            span: field.span(),
                            field: field.ident.clone(),
                            ty: ty.pretty(&self.unify.types_map.items),
                        });
                        ResolvedType::Err
                    }
                },
                TypeKind::Adt(_) => {
                    self.diagnostics.add(NotRecordType {
                        span: expr.span(),
                        expr: expr.span(),
                        ty: ty.pretty(&self.unify.types_map.items),
                    });
                    ResolvedType::Err
                }
                TypeKind::Tmp => unreachable!(),
            }
        } else {
            self.diagnostics.add(NotRecordType {
                span: expr.span(),
                expr: expr.span(),
                ty: ty.pretty(&self.unify.types_map.items),
            });
            ResolvedType::Err
        }
    }
}

impl<'a> Visitor for TypeCheckRecords<'a> {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        walk_expr(self, expr);
        match &**expr {
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => {
                let c_ty = self.state.expr_types_map[&*expr].clone();
                // assert!(
                //     matches!(c_ty, ResolvedType::Var(_)),
                //     "record type should not be inferred yet"
                // );
                let c_expr = self.resolve_field_ty(&bin_expr.lhs, &bin_expr.rhs);
                self.state.constraints.push(Constraint(
                    spanned(bin_expr.rhs.span(), c_expr),
                    spanned(bin_expr.rhs.span(), c_ty),
                ));
            }
            Expr::Record(record_expr) => {
                let ty = &self.state.expr_types_map[&*expr];
                if let ResolvedType::Var(_) | ResolvedType::Param(_) = ty {
                    self.diagnostics.add(TypeMustBeKnown {
                        span: expr.span(),
                        expr: expr.span(),
                    });
                } else if let Some(id) = ty.ident_of_constructed() {
                    let data_def = &self.unify.types_map.items[id];
                    match &data_def.kind {
                        TypeKind::Record(record_def) => {
                            // Check every field in the record_expr.
                            for field in &record_expr.fields {
                                if record_def.fields.get(&field.ident).is_none() {
                                    self.diagnostics.add(UnknownField {
                                        span: field.span(),
                                        field: field.ident.clone(),
                                        ty: ty.pretty(&self.unify.types_map.items),
                                    });
                                }
                            }
                            // Check if any field is missing and add constraints on field types.
                            let mut missing = Vec::new();
                            for (ident, field_ty) in &record_def.fields {
                                let Some(field) = record_expr.fields.iter().find(|field| &*field.ident == ident) else {
                                    missing.push(format!("`{ident}`"));
                                    continue;
                                };
                                let c_expr = self.state.expr_types_map[&*field.expr].clone();
                                self.state.constraints.push(Constraint(
                                    spanned(field.expr.span(), c_expr),
                                    spanned(field.ident.span(), field_ty.clone()),
                                ));
                            }
                            if !missing.is_empty() {
                                self.diagnostics.add(MissingFields {
                                    span: expr.span(),
                                    expr: expr.span(),
                                    missing: missing.join(", "),
                                })
                            }
                        }
                        TypeKind::Adt(_) => {
                            self.diagnostics.add(NotRecordType {
                                span: expr.span(),
                                expr: expr.span(),
                                ty: ty.pretty(&self.unify.types_map.items),
                            });
                        }
                        TypeKind::Tmp => unreachable!(),
                    }
                } else {
                    self.diagnostics.add(NotRecordType {
                        span: expr.span(),
                        expr: expr.span(),
                        ty: ty.pretty(&self.unify.types_map.items),
                    });
                }
            }
            _ => {}
        }
    }
}
