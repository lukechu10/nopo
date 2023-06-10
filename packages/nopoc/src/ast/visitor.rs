use crate::span::Spanned;

use super::*;

pub trait Visitor {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        walk_expr(self, expr)
    }
    fn visit_item(&mut self, item: &Spanned<Item>) {
        walk_item(self, item)
    }

    fn visit_root(&mut self, root: &Root) {
        for item in &root.items {
            self.visit_item(item)
        }
    }
}

pub fn walk_expr<T: Visitor + ?Sized>(visitor: &mut T, expr: &Expr) {
    match expr {
        Expr::Ident(_) => {}
        Expr::Block(Spanned(BlockExpr { exprs }, _)) => {
            for expr in exprs {
                visitor.visit_expr(expr);
            }
        }
        Expr::Binary(Spanned(BinaryExpr { lhs, op: _, rhs }, _)) => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        Expr::Unary(Spanned(UnaryExpr { op: _, expr }, _)) => visitor.visit_expr(expr),
        Expr::Index(Spanned(IndexExpr { lhs, index }, _)) => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(index);
        }
        Expr::LitBool(_) => {}
        Expr::LitInt(_) => {}
        Expr::LitFloat(_) => {}
        Expr::LitStr(_) => {}
        Expr::LitChar(_) => {}
        Expr::If(Spanned(IfExpr { cond, then, else_ }, _)) => {
            visitor.visit_expr(cond);
            visitor.visit_expr(then);
            if let Some(else_) = else_ {
                visitor.visit_expr(else_);
            }
        }
        Expr::While(Spanned(WhileExpr { cond, body }, _)) => {
            visitor.visit_expr(cond);
            visitor.visit_expr(body);
        }
        Expr::For(Spanned(
            ForExpr {
                binding: _,
                iter,
                body,
            },
            _,
        )) => {
            visitor.visit_expr(iter);
            visitor.visit_expr(body);
        }
        Expr::Loop(Spanned(LoopExpr { body }, _)) => visitor.visit_expr(body),
        Expr::Return(Spanned(ReturnExpr { expr }, _)) => visitor.visit_expr(&expr),
        Expr::Let(Spanned(LetExpr { ident: _, params: _, ret_ty: _, expr, _in }, _)) => {
            visitor.visit_expr(expr);
            visitor.visit_expr(_in);
        }
    }
}

pub fn walk_item<T: Visitor + ?Sized>(visitor: &mut T, item: &Item) {
    match item {
        Item::Let(Spanned(
            LetItem {
                attrs: _,
                vis: _,
                ident: _,
                params: _,
                ret_ty: _,
                expr,
            },
            _,
        )) => visitor.visit_expr(expr),
        Item::Type(_) => {}
        Item::Mod(_) => {}
        Item::Use(_) => {}
    }
}
