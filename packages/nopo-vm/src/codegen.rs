//! Code generation.

use std::collections::HashMap;
use std::rc::Rc;

use nopo_diagnostics::span::Spanned;
use nopo_parser::ast::{Expr, LetId, LetItem, Root};
use nopo_parser::lexer::BinOp;
use nopo_parser::visitor::{walk_root, Visitor};
use nopo_passes::resolve::{BindingId, BindingsMap, ResolvedType, TypesMap};
use nopo_passes::unify::UnifyTypes;

use crate::types::Instr::*;
use crate::types::{Chunk, ObjClosure, ObjProto, Object, Value};

#[derive(Debug)]
pub struct Codegen {
    bindings_map: BindingsMap,
    /// Contains the type of all the bindings.
    binding_types_map: HashMap<BindingId, ResolvedType>,
    types_map: TypesMap,
    chunks: Vec<Chunk>,
}

impl Codegen {
    pub fn new(unify: UnifyTypes) -> Self {
        Self {
            bindings_map: unify.bindings_map,
            binding_types_map: unify.binding_types_map,
            types_map: unify.types_map,
            chunks: Vec::new(),
        }
    }

    /// Get the last chunk in the chunks stack. This is probably where we want to codegen.
    fn chunk(&mut self) -> &mut Chunk {
        self.chunks.last_mut().unwrap()
    }

    /// Push a chunk with a name onto the chunk stack.
    fn new_chunk(&mut self, name: String) {
        self.chunks.push(Chunk::new(name));
    }

    fn pop_chunk(&mut self) -> Chunk {
        self.chunks.pop().unwrap()
    }

    pub fn root_closure(self) -> ObjClosure {
        assert_eq!(self.chunks.len(), 1);
        ObjClosure {
            func: ObjProto {
                chunk: self.chunks.into_iter().next().unwrap(),
                arity: 0,
                upvalues_count: 0,
            },
            upvalues: Vec::new(),
        }
    }
}

impl Visitor for Codegen {
    fn visit_root(&mut self, root: &Root) {
        self.chunks.push(Chunk::new("<global>".to_string()));
        walk_root(self, root);
    }

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        // If let item has params, generate a closure. Otherwise, just evaluate value and push onto
        // global stack.
        match item.params.len() {
            0 => self.visit_expr(&item.expr),
            _ => {
                let arity = item.params.len();
                self.new_chunk(item.ident.to_string());
                self.visit_expr(&item.expr);
                let chunk = self.pop_chunk();
                let value = Value::Object(Rc::new(Object::Closure(ObjClosure {
                    func: ObjProto {
                        arity: arity as u32,
                        chunk,
                        upvalues_count: 0, // Because this is a top-level function.
                    },
                    upvalues: Vec::new(),
                })));
                let slot = self.chunk().write_const(value);
                self.chunk().write(LoadConst(slot));
            }
        }
    }

    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Ident(_) => todo!(),
            Expr::Block(_) => todo!(),
            Expr::Lambda(_) => todo!(),
            Expr::Tuple(_) => todo!(),
            Expr::Record(_) => todo!(),
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => todo!("dot expr"),
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::FnCall => {
                let (callee, args) = get_fn_call_callee_and_args(expr);
                assert!(!args.is_empty());
                for arg in &args {
                    self.visit_expr(arg);
                }
                self.visit_expr(callee);
                self.chunk().write(Calli {
                    args: args.len() as u32,
                });
            }
            Expr::Binary(bin_expr) => {
                // TODO: support ad-hoc polymorphism for binary operators.
                self.visit_expr(&bin_expr.lhs);
                self.visit_expr(&bin_expr.rhs);
                match &*bin_expr.op {
                    BinOp::Plus => self.chunk().write(IntAdd),
                    BinOp::Minus => self.chunk().write(IntSub),
                    BinOp::Mul => self.chunk().write(IntMul),
                    BinOp::Div => self.chunk().write(IntDiv),
                    BinOp::Mod => self.chunk().write(IntMod),
                    BinOp::And => self.chunk().write(IntAnd),
                    BinOp::Or => self.chunk().write(IntOr),
                    BinOp::Xor => self.chunk().write(IntXor),
                    BinOp::ShiftLeft => self.chunk().write(IntShl),
                    BinOp::ShiftRight => self.chunk().write(IntShr),
                    BinOp::UnsignedShiftRight => self.chunk().write(IntRor),
                    BinOp::Eq => self.chunk().write(ValEq),
                    BinOp::Neq => todo!(),
                    BinOp::Lt => todo!(),
                    BinOp::Gt => todo!(),
                    BinOp::LtEq => todo!(),
                    BinOp::GtEq => todo!(),
                    BinOp::AndAnd => self.chunk().write(BoolAnd),
                    BinOp::OrOr => self.chunk().write(BoolOr),
                    BinOp::Dot => unreachable!(),
                    BinOp::FnCall => unreachable!(),
                };
            }
            Expr::Unary(_) => todo!(),
            Expr::Index(_) => todo!(),
            Expr::LitBool(value) => self.chunk().write(LoadBool(*value)),
            Expr::LitInt(value) => self.chunk().write(LoadInt(*value)),
            Expr::LitFloat(_value) => todo!("load float"),
            Expr::LitStr(_value) => todo!("load string"),
            Expr::LitChar(value) => self.chunk().write(LoadChar(*value)),
            Expr::If(if_expr) => {
                self.visit_expr(&if_expr.cond);
                let then_jump = self.chunk().write_get_offset(CJump(0));
                self.visit_expr(&if_expr.else_);
                let else_jump = self.chunk().write_get_offset(Jump(0));
                self.chunk().patch_jump(then_jump);
                self.visit_expr(&if_expr.then);
                self.chunk().patch_jump(else_jump);
            }
            Expr::While(_) => todo!(),
            Expr::For(_) => todo!(),
            Expr::Loop(_) => todo!(),
            Expr::Return(_) => todo!(),
            Expr::Let(_) => todo!(),
            Expr::Err => todo!(),
        }
    }
}

/// Get a flattened list of function application arguments and the callee.
fn get_fn_call_callee_and_args(expr: &Spanned<Expr>) -> (&Spanned<Expr>, Vec<&Spanned<Expr>>) {
    match &**expr {
        Expr::Binary(bin_expr) if *bin_expr.op == BinOp::FnCall => {
            let (callee, mut args) = get_fn_call_callee_and_args(&bin_expr.lhs);
            args.push(&bin_expr.rhs);
            (callee, args)
        }
        _ => (expr, Vec::new()),
    }
}
