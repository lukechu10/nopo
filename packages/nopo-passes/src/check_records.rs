//! Type check record and member expressions.
//!
//! This runs after type unification since we don't use record fields to infer types.

use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::Report;

use nopo_parser::ast::{Expr, Ident};
use nopo_parser::lexer::BinOp;
use nopo_parser::visitor::{walk_expr, Visitor};

use crate::db::{Db, ResolvedType, ResolvedTypePretty, TypeKind};
use crate::unify::{Constraint, GenerateConstraints};

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
    db: &'a mut Db,
    state: &'a mut GenerateConstraints,
}

impl<'a> TypeCheckRecords<'a> {
    pub fn new(db: &'a mut Db, state: &'a mut GenerateConstraints) -> Self {
        Self { db, state }
    }
}

impl<'a> TypeCheckRecords<'a> {
    fn resolve_field(
        &mut self,
        expr: &Spanned<Expr>,
        field: &Spanned<Expr>,
    ) -> (ResolvedType, u32) {
        // Check that field is an identifier.
        let Expr::Ident(field) = &**field else {
            self.db.diagnostics.add(FieldMustBeIdentifier {
                span: field.span(),
                expr: field.span(),
            });
            return (ResolvedType::Err, 0);
        };
        let ty = &mut self.state.expr_types_map[&*expr];

        if let ResolvedType::Var(_) | ResolvedType::Param(_) = ty {
            self.db.diagnostics.add(TypeMustBeKnown {
                span: expr.span(),
                expr: expr.span(),
            });
            (ResolvedType::Err, 0)
        } else if let Some(id) = ty.ident_of_constructed() {
            let data_def = &self.db.types_map.items[id];
            match &data_def.kind {
                TypeKind::Record(record_def) => match record_def.fields.get(field.ident.as_ref()) {
                    Some((ty, i)) => (ty.clone(), *i),
                    None => {
                        self.db.diagnostics.add(UnknownField {
                            span: field.span(),
                            field: field.ident.clone(),
                            ty: ty.pretty(&self.db.types_map.items),
                        });
                        (ResolvedType::Err, 0)
                    }
                },
                TypeKind::Adt(_) => {
                    self.db.diagnostics.add(NotRecordType {
                        span: expr.span(),
                        expr: expr.span(),
                        ty: ty.pretty(&self.db.types_map.items),
                    });
                    (ResolvedType::Err, 0)
                }
                TypeKind::Tmp => unreachable!(),
            }
        } else {
            self.db.diagnostics.add(NotRecordType {
                span: expr.span(),
                expr: expr.span(),
                ty: ty.pretty(&self.db.types_map.items),
            });
            (ResolvedType::Err, 0)
        }
    }
}

impl<'a> Visitor for TypeCheckRecords<'a> {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        walk_expr(self, expr);
        match &**expr {
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => {
                let c_ty = self.state.expr_types_map[&*expr].clone();
                let (c_expr, i) = self.resolve_field(&bin_expr.lhs, &bin_expr.rhs);
                self.state.constraints.push(Constraint(
                    spanned(bin_expr.rhs.span(), c_expr),
                    spanned(bin_expr.rhs.span(), c_ty),
                ));
                self.db.record_field_map.insert(expr, i);
            }
            Expr::Record(record_expr) => {
                let ty = &self.state.expr_types_map[&*expr];
                if let ResolvedType::Var(_) | ResolvedType::Param(_) = ty {
                    self.db.diagnostics.add(TypeMustBeKnown {
                        span: expr.span(),
                        expr: expr.span(),
                    });
                } else if let Some(id) = ty.ident_of_constructed() {
                    let data_def = &self.db.types_map.items[id];
                    match &data_def.kind {
                        TypeKind::Record(record_def) => {
                            // Check every field in the record_expr.
                            for field in &record_expr.fields {
                                if record_def.fields.get(&field.ident).is_none() {
                                    self.db.diagnostics.add(UnknownField {
                                        span: field.span(),
                                        field: field.ident.clone(),
                                        ty: ty.pretty(&self.db.types_map.items),
                                    });
                                }
                            }
                            // Check if any field is missing and add constraints on field types.
                            let mut missing = Vec::new();
                            for (ident, (field_ty, field_pos)) in &record_def.fields {
                                let Some(field) = record_expr.fields.iter().find(|field| &*field.ident == ident) else {
                                    missing.push(format!("`{ident}`"));
                                    continue;
                                };
                                let c_expr = self.state.expr_types_map[&*field.expr].clone();
                                self.state.constraints.push(Constraint(
                                    spanned(field.expr.span(), c_expr),
                                    spanned(field.ident.span(), field_ty.clone()),
                                ));
                                self.db.record_expr_field_map.insert(field, *field_pos);
                            }
                            if !missing.is_empty() {
                                self.db.diagnostics.add(MissingFields {
                                    span: expr.span(),
                                    expr: expr.span(),
                                    missing: missing.join(", "),
                                })
                            }
                        }
                        TypeKind::Adt(_) => {
                            self.db.diagnostics.add(NotRecordType {
                                span: expr.span(),
                                expr: expr.span(),
                                ty: ty.pretty(&self.db.types_map.items),
                            });
                        }
                        TypeKind::Tmp => unreachable!(),
                    }
                } else {
                    self.db.diagnostics.add(NotRecordType {
                        span: expr.span(),
                        expr: expr.span(),
                        ty: ty.pretty(&self.db.types_map.items),
                    });
                }
            }
            _ => {}
        }
    }
}
