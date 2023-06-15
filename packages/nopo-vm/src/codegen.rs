//! Code generation.

use std::collections::HashMap;
use std::rc::Rc;

use la_arena::ArenaMap;
use nopo_diagnostics::span::Spanned;
use nopo_parser::ast::{Expr, LetId, LetItem, Root, TypeId, TypeItem};
use nopo_parser::lexer::{BinOp, UnaryOp};
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
    offset_map: ArenaMap<BindingId, BindingOffset>,
    chunks: Vec<ChunkWithData>,
}

#[derive(Debug)]
struct ChunkWithData {
    chunk: Chunk,
    /// Temporary data storing the next offset for a variable.
    next_offset: u32,
}

#[derive(Debug, Clone, Copy)]
struct BindingOffset {
    kind: BindingKind,
    offset: u32,
}

#[derive(Debug, Clone, Copy)]
enum BindingKind {
    Global,
    GlobalDataConstructor,
    Local,
    LocalUpValue,
}

impl Codegen {
    pub fn new(unify: UnifyTypes) -> Self {
        Self {
            bindings_map: unify.bindings_map,
            binding_types_map: unify.binding_types_map,
            types_map: unify.types_map,
            offset_map: ArenaMap::new(),
            chunks: Vec::new(),
        }
    }

    /// Get the last chunk in the chunks stack. This is probably where we want to codegen.
    fn chunk(&mut self) -> &mut Chunk {
        &mut self.chunks.last_mut().unwrap().chunk
    }

    /// Push a chunk with a name onto the chunk stack.
    fn new_chunk(&mut self, name: String) {
        self.chunks.push(ChunkWithData {
            chunk: Chunk::new(name),
            next_offset: 0,
        });
    }

    fn pop_chunk(&mut self) -> Chunk {
        self.chunks.pop().unwrap().chunk
    }

    fn new_binding_offset(&mut self, id: BindingId, kind: BindingKind) {
        let offset = self.chunks.last_mut().unwrap().next_offset;
        let binding_data = BindingOffset { kind, offset };
        self.chunks.last_mut().unwrap().next_offset += 1;
        self.offset_map.insert(id, binding_data);
    }

    pub fn root_closure(self) -> ObjClosure {
        assert_eq!(self.chunks.len(), 1);
        ObjClosure {
            func: ObjProto {
                chunk: self.chunks.into_iter().next().unwrap().chunk,
                arity: 0,
                upvalues_count: 0,
            },
            upvalues: Vec::new(),
        }
    }
}

impl Visitor for Codegen {
    fn visit_root(&mut self, root: &Root) {
        self.new_chunk("<global>".to_string());
        walk_root(self, root);
    }

    fn visit_type_item(&mut self, _idx: TypeId, item: &Spanned<TypeItem>) {}

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        let binding = self.bindings_map.let_items[item];
        // If let item has params, generate a closure. Otherwise, just evaluate value and push onto
        // global stack.
        match item.params.len() {
            0 => {
                self.visit_expr(&item.expr);
                self.new_binding_offset(binding, BindingKind::Global);
            }
            arity => {
                self.new_binding_offset(binding, BindingKind::Global);
                self.new_chunk(item.ident.to_string());
                for param in &item.params {
                    let binding = self.bindings_map.params[&*param];
                    self.new_binding_offset(binding, BindingKind::Local);
                }
                self.visit_expr(&item.expr);
                let chunk = self.pop_chunk();
                let value = Value::Object(Rc::new(Object::Closure(Rc::new(ObjClosure {
                    func: ObjProto {
                        arity: arity as u32,
                        chunk,
                        upvalues_count: 0, // Because this is a top-level function.
                    },
                    upvalues: Vec::new(),
                }))));
                let slot = self.chunk().write_const(value);
                self.chunk().write(LoadConst(slot));
            }
        }
    }

    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Ident(ident_expr) => {
                let binding = self.bindings_map.idents[&*ident_expr].unwrap();
                let data = self.offset_map[binding];
                match data.kind {
                    BindingKind::Global => self.chunk().write(LoadGlobal(data.offset)),
                    BindingKind::GlobalDataConstructor => todo!(),
                    BindingKind::Local => self.chunk().write(LoadLocal(data.offset)),
                    BindingKind::LocalUpValue => self.chunk().write(LoadUpValue(data.offset)),
                }
            }
            Expr::Block(_) => todo!(),
            Expr::Lambda(_) => todo!(),
            Expr::Tuple(_) => todo!(),
            Expr::Record(_) => todo!(),
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => todo!("dot expr"),
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::FnCall => {
                let (callee, args) = get_fn_call_callee_and_args(expr);
                assert!(!args.is_empty());
                // See if we can emit a callglobal instead of a calli for performance.
                let global_idx = if let Expr::Ident(ident_expr) = &**callee {
                    let binding = self.bindings_map.idents[&*ident_expr].unwrap();
                    let let_item = self.offset_map[binding];
                    if matches!(
                        let_item.kind,
                        BindingKind::Global | BindingKind::GlobalDataConstructor
                    ) {
                        Some(let_item.offset)
                    } else {
                        None
                    }
                } else {
                    None
                };
                if global_idx.is_none() {
                    self.visit_expr(callee);
                }
                for arg in &args {
                    self.visit_expr(arg);
                }
                if let Some(idx) = global_idx {
                    self.chunk().write(CallGlobal {
                        idx,
                        args: args.len() as u32,
                    });
                } else {
                    self.chunk().write(Calli {
                        args: args.len() as u32,
                    });
                }
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
                    BinOp::Neq => {
                        self.chunk().write(ValEq);
                        self.chunk().write(BoolNot);
                    }
                    BinOp::Lt => self.chunk().write(IntLt),
                    BinOp::Gt => self.chunk().write(IntGt),
                    BinOp::LtEq => self.chunk().write(IntLte),
                    BinOp::GtEq => self.chunk().write(IntGte),
                    BinOp::AndAnd => self.chunk().write(BoolAnd),
                    BinOp::OrOr => self.chunk().write(BoolOr),
                    BinOp::Dot => unreachable!(),
                    BinOp::FnCall => unreachable!(),
                };
            }
            Expr::Unary(unary_expr) => match &*unary_expr.op {
                UnaryOp::Neg => {
                    self.chunk().write(LoadInt(0));
                    self.visit_expr(&unary_expr.expr);
                    self.chunk().write(IntSub);
                }
                UnaryOp::Not => {
                    self.visit_expr(&unary_expr.expr);
                    self.chunk().write(BoolNot);
                }
            },
            Expr::Index(_) => todo!(),
            Expr::LitBool(value) => self.chunk().write(LoadBool(*value)),
            Expr::LitInt(value) => self.chunk().write(LoadInt(*value)),
            Expr::LitFloat(_value) => todo!("load float"),
            Expr::LitStr(value) => {
                let value = Value::Object(Rc::new(Object::String(value.clone())));
                let str_const = self.chunk().write_const(value);
                self.chunk().write(LoadConst(str_const));
            }
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
            Expr::Let(let_expr) => {
                let binding = self.bindings_map.let_exprs[&*let_expr];
                let kind = if self.chunks.len() == 1 {
                    BindingKind::Global
                } else {
                    BindingKind::Local
                };
                self.new_binding_offset(binding, kind);
                self.visit_expr(&let_expr.expr);
                self.visit_expr(&let_expr._in);
                self.chunk().write(Slide(1));
            }
            Expr::Err => unreachable!(),
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
