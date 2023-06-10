use crate::span::Spanned;

use super::*;

pub trait Visitor {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        walk_expr(self, expr)
    }

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        walk_let_item(self, item)
    }
    fn visit_type_item(&mut self, _idx: TypeId, _item: &Spanned<TypeItem>) {}
    fn visit_mod_item(&mut self, _item: &Spanned<ModItem>) {}
    fn visit_use_item(&mut self, _item: &Spanned<UseItem>) {}

    fn visit_root(&mut self, root: &Root) {
        walk_root(self, root)
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
        Expr::Tuple(Spanned(TupleExpr { elements }, _)) => {
            for element in elements {
                visitor.visit_expr(element);
            }
        }
        Expr::Record(Spanned(RecordExpr { fields }, _)) => {
            for field in fields {
                visitor.visit_expr(&field.expr);
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
            visitor.visit_expr(else_);
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
        Expr::Let(Spanned(
            LetExpr {
                ident: _,
                ret_ty: _,
                expr,
                _in,
            },
            _,
        )) => {
            visitor.visit_expr(expr);
            visitor.visit_expr(_in);
        }
    }
}

pub fn walk_root<T: Visitor + ?Sized>(visitor: &mut T, root: &Root) {
    for (idx, let_item) in root.let_items.iter() {
        visitor.visit_let_item(idx, let_item);
    }
    for (idx, type_item) in root.type_items.iter() {
        visitor.visit_type_item(idx, type_item);
    }
    for mod_item in &root.mod_items {
        visitor.visit_mod_item(mod_item);
    }
    for use_item in &root.use_items {
        visitor.visit_use_item(use_item);
    }
}

pub fn walk_let_item<T: Visitor + ?Sized>(visitor: &mut T, item: &LetItem) {
    visitor.visit_expr(&item.expr);
}
