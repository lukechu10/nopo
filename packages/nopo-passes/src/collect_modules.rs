use std::path::{Path, PathBuf};

use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::Report;
use nopo_parser::ast::{BinaryExpr, Expr, LitExpr};
use nopo_parser::lexer::BinOp;
use nopo_parser::visitor::{walk_expr, Visitor};

use crate::db::Db;

#[derive(Report)]
#[kind("error")]
#[message("module path must be a string literal or a path")]
struct InvalidImportPath {
    span: Span,
    #[label(message = "Module path must be a string literal or a path")]
    expr: Span,
}

#[derive(Debug, Clone)]
pub enum ModulePath {
    Relative(String),
    Absolute(Vec<String>),
}

/// Get all the import expressions to build the module graph.
pub struct CollectModules<'a> {
    pub modules: Vec<Spanned<ModulePath>>,
    parent: PathBuf,
    db: &'a mut Db,
}

impl<'a> CollectModules<'a> {
    pub fn new(parent: PathBuf, db: &'a mut Db) -> Self {
        Self {
            modules: Vec::new(),
            parent,
            db,
        }
    }
}

impl ModulePath {
    fn from_expr(expr: &Expr) -> Option<Self> {
        match expr {
            Expr::Lit(Spanned(LitExpr::String(path), _)) => Some(Self::Relative(path.clone())),
            _ => Self::absolute_from_expr(expr).map(Self::Absolute),
        }
    }

    fn absolute_from_expr(expr: &Expr) -> Option<Vec<String>> {
        match expr {
            Expr::Binary(Spanned(BinaryExpr { lhs, op, rhs }, _))
                if matches!(***lhs, Expr::Ident(_)) && **op == BinOp::Dot =>
            {
                Self::absolute_from_expr(lhs).and_then(|mut path| {
                    if let Expr::Ident(expr) = &***rhs {
                        path.push(expr.ident.to_string());
                        Some(path)
                    } else {
                        None
                    }
                })
            }
            Expr::Ident(expr) => Some(vec![expr.ident.to_string()]),
            _ => None,
        }
    }

    pub fn resolve(self, parent: &Path) -> Result<PathBuf, std::io::Error> {
        match self {
            ModulePath::Relative(path) => parent.join(path).canonicalize(),
            ModulePath::Absolute(_) => todo!("resolve absolute module"),
        }
    }
}

impl Visitor for CollectModules<'_> {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Macro(macro_expr) if &*macro_expr.ident == "import" => {
                let path = match ModulePath::from_expr(&macro_expr.expr) {
                    Some(path) => path,
                    None => {
                        self.db.diagnostics.add(InvalidImportPath {
                            span: macro_expr.span(),
                            expr: macro_expr.span(),
                        });
                        return;
                    }
                };
                self.modules.push(spanned(expr.span(), path.clone()));
                match path.resolve(&self.parent) {
                    Ok(resolved) => {
                        self.db.module_imports_map.insert(macro_expr, resolved);
                    }
                    Err(err) => {
                        todo!("io error: {err}")
                    }
                }
            }
            _ => walk_expr(self, expr),
        }
    }
}
