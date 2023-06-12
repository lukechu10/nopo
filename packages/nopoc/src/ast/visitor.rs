use nopo_diagnostics::span::Spanned;

use super::*;

pub trait Visitor {
    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        walk_expr(self, expr)
    }

    fn visit_type(&mut self, _ty: &Spanned<Type>) {}

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        walk_let_item(self, item)
    }
    fn visit_type_item(&mut self, _idx: TypeId, item: &Spanned<TypeItem>) {
        walk_type_item(self, item)
    }
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
                ret_ty,
                expr,
                _in,
            },
            _,
        )) => {
            if let Some(ret_ty) = ret_ty {
                visitor.visit_type(ret_ty);
            }
            visitor.visit_expr(expr);
            visitor.visit_expr(_in);
        }
        Expr::Err => {}
    }
}

pub fn walk_root<T: Visitor + ?Sized>(visitor: &mut T, root: &Root) {
    for mod_item in &root.mod_items {
        visitor.visit_mod_item(mod_item);
    }
    for use_item in &root.use_items {
        visitor.visit_use_item(use_item);
    }

    for id in &root.items {
        match id {
            ItemId::Let(id) => visitor.visit_let_item(*id, &root.let_items[*id]),
            ItemId::Type(id) => visitor.visit_type_item(*id, &root.type_items[*id]),
        }
    }
}

pub fn walk_let_item<T: Visitor + ?Sized>(visitor: &mut T, item: &LetItem) {
    for param in &item.params {
        if let Some(ty) = &param.ty {
            visitor.visit_type(ty);
        }
    }
    if let Some(ret_ty) = &item.ret_ty {
        visitor.visit_type(ret_ty);
    }

    visitor.visit_expr(&item.expr);
}

pub fn walk_type_item<T: Visitor + ?Sized>(visitor: &mut T, item: &TypeItem) {
    match &*item.def {
        TypeDef::Adt(adt) => {
            for data_constructor in &adt.data_constructors {
                for ty in &data_constructor.of {
                    visitor.visit_type(ty);
                }
            }
        },
        TypeDef::Record(record) => {
            for field in &record.fields {
                visitor.visit_type(&field.ty);
            }
        },
        TypeDef::Err => {},
    }
}
