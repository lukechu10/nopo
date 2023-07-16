use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::{Diagnostics, Report};
use nopo_parser::ast::{BinaryExpr, Expr, LitExpr};
use nopo_parser::lexer::BinOp;
use nopo_parser::visitor::{walk_expr, Visitor};

#[derive(Report)]
#[kind("error")]
#[message("module path must be a string literal or a path")]
struct InvalidImportPath {
    span: Span,
    #[label(message = "Module path must be a string literal or a path")]
    expr: Span,
}

pub enum ModulePath {
    Relative(String),
    Absolute(Vec<String>),
}

/// Get all the import expressions to build the module graph.
pub struct CollectModules {
    modules: Vec<Spanned<ModulePath>>,
    diagnostics: Diagnostics,
}

impl CollectModules {
    pub fn new(diagnostics: Diagnostics) -> Self {
        Self {
            modules: Vec::new(),
            diagnostics,
        }
    }
}

impl ModulePath {
    fn from_expr(expr: &Expr) -> Option<Self> {
        match expr {
            Expr::Lit(Spanned(LitExpr::String(path), _)) => Some(Self::Relative(path.clone())),
            _ => Self::absolute_from_expr(expr).and_then(|path| Some(Self::Absolute(path))),
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
}

impl Visitor for CollectModules {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Macro(macro_expr) if &*macro_expr.ident == "import" => {
                let path = match ModulePath::from_expr(&macro_expr.expr) {
                    Some(path) => path,
                    None => {
                        self.diagnostics.add(InvalidImportPath {
                            span: macro_expr.span(),
                            expr: macro_expr.span(),
                        });
                        return;
                    }
                };
                self.modules.push(spanned(expr.span(), path));
            }
            _ => walk_expr(self, expr),
        }
    }
}
