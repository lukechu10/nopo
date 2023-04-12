use crate::span::Spanned;

use super::{
    BinaryExpr, BlockExpr, Expr, FnCallExpr, FnItem, ForExpr, IfExpr, Item, LetStmt, LoopExpr,
    ReturnStmt, Stmt, UnaryExpr, WhileExpr, Root,
};

pub trait Visitor {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        walk_expr(self, expr)
    }
    fn visit_stmt(&mut self, stmt: &Spanned<Stmt>) {
        walk_stmt(self, stmt)
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
        Expr::Block(Spanned(BlockExpr { stmts }, _)) => {
            for stmt in stmts {
                visitor.visit_stmt(stmt);
            }
        }
        Expr::Binary(Spanned(BinaryExpr { lhs, op: _, rhs }, _)) => {
            visitor.visit_expr(lhs);
            visitor.visit_expr(rhs);
        }
        Expr::Unary(Spanned(UnaryExpr { op: _, expr }, _)) => visitor.visit_expr(expr),
        Expr::FnCall(Spanned(FnCallExpr { callee, args }, _)) => {
            visitor.visit_expr(callee);
            for arg in &args.args {
                visitor.visit_expr(arg);
            }
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
    }
}

pub fn walk_stmt<T: Visitor + ?Sized>(visitor: &mut T, stmt: &Stmt) {
    match stmt {
        Stmt::ExprStmt(expr) => visitor.visit_expr(expr),
        Stmt::Let(Spanned(LetStmt { binding: _, expr }, _)) => visitor.visit_expr(&expr),
        Stmt::Return(Spanned(ReturnStmt { expr }, _)) => visitor.visit_expr(expr),
    }
}

pub fn walk_item<T: Visitor + ?Sized>(visitor: &mut T, item: &Item) {
    match item {
        Item::Fn(Spanned(
            FnItem {
                attrs: _,
                vis: _,
                ident: _,
                args: _,
                ret_ty: _,
                body,
            },
            _,
        )) => visitor.visit_expr(body),
        Item::ExternFn(_) => {}
        Item::Struct(_) => {}
        Item::Mod(_) => {}
        Item::Use(_) => {}
    }
}
