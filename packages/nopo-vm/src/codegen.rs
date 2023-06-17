//! Code generation.

use std::collections::HashMap;
use std::rc::Rc;

use la_arena::{Arena, ArenaMap};
use nopo_diagnostics::span::Spanned;
use nopo_parser::ast::{Expr, LetId, LetItem, LitExpr, Pattern, Root, TypeDef, TypeId, TypeItem};
use nopo_parser::lexer::{BinOp, UnaryOp};
use nopo_parser::visitor::{walk_root, Visitor};
use nopo_passes::resolve::{Binding, BindingId, BindingsMap, ResolvedType, TypesMap};
use nopo_passes::unify::UnifyTypes;

use crate::print::print_chunk;
use crate::types::Instr::{self, *};
use crate::types::{Chunk, ObjClosure, ObjProto, Object, Value, VmIndex};

#[derive(Debug)]
pub struct Codegen {
    bindings: Arena<Binding>,
    bindings_map: BindingsMap,
    /// Contains the type of all the bindings.
    _binding_types_map: HashMap<BindingId, ResolvedType>,
    _types_map: TypesMap,
    offset_map: ArenaMap<BindingId, BindingOffset>,
    chunks: Vec<ChunkWithData>,
}

#[derive(Debug)]
struct ChunkWithData {
    chunk: Chunk,
    /// Temporary data storing the next offset for a variable.
    next_offset: u32,
    /// List of upvalues that should be captured.
    ///
    /// Stored as the instructions needed to push the upvalue onto the stack.
    upvalues: Vec<Instr>,
}

#[derive(Debug, Clone, Copy)]
struct BindingOffset {
    kind: BindingKind,
    offset: u32,
    /// chunk.len() when this binding was created.
    chunks_depth: usize,
}

#[derive(Debug, Clone, Copy)]
enum BindingKind {
    Global,
    GlobalDataConstructor { tag: VmIndex, arity: VmIndex },
    Local,
}

#[derive(Debug, Clone, Copy)]
struct OffsetState {
    next_offset: u32,
}

impl Codegen {
    pub fn new(unify: UnifyTypes) -> Self {
        Self {
            bindings: unify.bindings,
            bindings_map: unify.bindings_map,
            _binding_types_map: unify.binding_types_map,
            _types_map: unify.types_map,
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
            upvalues: Vec::new(),
        });
    }

    fn pop_chunk(&mut self) -> Rc<Chunk> {
        Rc::new(self.pop_chunk_with_data().chunk)
    }

    fn pop_chunk_with_data(&mut self) -> ChunkWithData {
        let data = self.chunks.pop().unwrap();
        print_chunk(&data.chunk, &mut std::io::stderr()).unwrap(); // TODO: remove this.
        data
    }

    /// Increment the stack offset. This is automatically called by [`Self::new_binding_offset`].
    /// Returns the current offset.
    fn inc_offset(&mut self) -> u32 {
        let last_chunk = self.chunks.last_mut().unwrap();
        let offset = last_chunk.next_offset;
        last_chunk.next_offset += 1;
        offset
    }

    /// Insert a new entry into the offset map.
    fn new_binding_offset(&mut self, id: BindingId, kind: BindingKind) {
        let offset = self.inc_offset();
        let binding_data = BindingOffset {
            kind,
            offset,
            chunks_depth: self.chunks.len() - 1,
        };
        self.offset_map.insert(id, binding_data);
    }

    /// Threads a binding through a stack of closures and returns the upvalue offset.
    fn thread_binding_as_upvalue(&mut self, id: BindingId) -> u32 {
        let offset_data = self.offset_map[id];

        let current_depth = self.chunks.len() - 1;
        let decl_depth = offset_data.chunks_depth;
        assert!(current_depth > decl_depth);

        /// Adds an upvalue to a chunk if not already added. Returns the offset of the upvalue.
        fn add_upvalue_to_chunk(chunk: &mut ChunkWithData, instr: Instr) -> u32 {
            if let Some(pos) = chunk.upvalues.iter().position(|&x| x == instr) {
                pos as u32
            } else {
                chunk.upvalues.push(instr);
                (chunk.upvalues.len() - 1) as u32
            }
        }

        // Bottom most scope should capture a local variable.
        let mut offset = add_upvalue_to_chunk(
            &mut self.chunks[decl_depth + 1],
            Instr::LoadLocal(offset_data.offset),
        );
        // Scopes after that should capture upvalue from previous scope.
        if decl_depth + 2 < current_depth {
            for i in decl_depth + 2..current_depth {
                offset = add_upvalue_to_chunk(&mut self.chunks[i], Instr::LoadUpValue(offset));
            }
        }

        offset
    }

    fn offset_state(&self) -> OffsetState {
        OffsetState {
            next_offset: self.chunks.last().unwrap().next_offset,
        }
    }

    fn restore_state(&mut self, state: OffsetState) {
        self.chunks.last_mut().unwrap().next_offset = state.next_offset;
    }

    pub fn root_closure(mut self) -> ObjClosure {
        assert_eq!(self.chunks.len(), 1);
        ObjClosure {
            proto: ObjProto {
                chunk: self.pop_chunk(),
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

    fn visit_type_item(&mut self, _idx: TypeId, item: &Spanned<TypeItem>) {
        match &*item.def {
            TypeDef::Adt(adt) => {
                for (tag, data_constructor) in adt.data_constructors.iter().enumerate() {
                    let binding = self.bindings_map.data_constructors[&data_constructor];
                    // Create a lambda that calls the data constructor.
                    self.new_chunk(data_constructor.ident.to_string());
                    for i in (0..data_constructor.of.len()).rev() {
                        self.chunk().write(LoadLocal(i as u32));
                    }
                    self.chunk().write(MakeAdt {
                        tag: tag as u32,
                        args: data_constructor.of.len() as u32,
                    });
                    let chunk = self.pop_chunk();
                    let value = Value::Object(Rc::new(Object::Closure(Rc::new(ObjClosure {
                        proto: ObjProto {
                            arity: data_constructor.of.len() as u32,
                            chunk,
                            upvalues_count: 0,
                        },
                        upvalues: Vec::new(),
                    }))));
                    let slot = self.chunk().write_const(value);
                    self.chunk().write(LoadConst(slot));
                    self.new_binding_offset(
                        binding,
                        BindingKind::GlobalDataConstructor {
                            tag: tag as u32,
                            arity: data_constructor.of.len() as u32,
                        },
                    );
                }
            }
            TypeDef::Record(_) => {}
            TypeDef::Err => unreachable!(),
        }
    }

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
                    proto: ObjProto {
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
                    BindingKind::GlobalDataConstructor { tag, arity } if arity == 0 => {
                        self.chunk().write(MakeAdt { tag, args: 0 })
                    }
                    BindingKind::Global | BindingKind::GlobalDataConstructor { .. } => {
                        self.chunk().write(LoadGlobal(data.offset))
                    }
                    BindingKind::Local => {
                        if data.chunks_depth == self.chunks.len() - 1 {
                            self.chunk().write(LoadLocal(data.offset));
                        } else {
                            let offset = self.thread_binding_as_upvalue(binding);
                            self.chunk().write(LoadUpValue(offset));
                        }
                    }
                }
            }
            Expr::Block(_) => todo!(),
            Expr::Lambda(lambda_expr) => {
                let arity = lambda_expr.params.len();

                self.new_chunk("<lambda>".to_string());
                for param in &lambda_expr.params {
                    let binding = self.bindings_map.lambda_params[&*param];
                    self.new_binding_offset(binding, BindingKind::Local);
                }
                self.visit_expr(&lambda_expr.expr);
                let data = self.pop_chunk_with_data();
                let value = Value::Object(Rc::new(Object::Proto(ObjProto {
                    arity: arity as u32,
                    chunk: Rc::new(data.chunk),
                    upvalues_count: data.upvalues.len() as u32,
                })));
                let slot = self.chunk().write_const(value);

                // Load upvalues.
                for instr in data.upvalues.iter().rev() {
                    self.chunk().write(*instr);
                }
                self.chunk().write(MakeClosure {
                    idx: slot,
                    upvalues: data.upvalues.len() as u32,
                });
            }
            Expr::Tuple(tuple_expr) => {
                for expr in tuple_expr.elements.iter().rev() {
                    self.visit_expr(expr);
                }
                self.chunk().write(Instr::MakeTuple {
                    args: tuple_expr.elements.len() as u32,
                });
            }
            Expr::Record(_) => todo!(),
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => todo!("dot expr"),
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::FnCall => {
                let (callee, args) = get_fn_call_callee_and_args(expr);
                assert!(!args.is_empty());

                let data = if let Expr::Ident(ident_expr) = &**callee {
                    let binding = self.bindings_map.idents[&*ident_expr].unwrap();
                    Some(self.offset_map[binding])
                } else {
                    None
                };
                match data.map(|data| data.kind) {
                    Some(BindingKind::Global) => {}
                    Some(BindingKind::GlobalDataConstructor { arity, .. })
                        if arity == args.len() as u32 => {}
                    _ => {
                        self.visit_expr(callee);
                    }
                }
                for arg in &args {
                    self.visit_expr(arg);
                }
                match data {
                    Some(BindingOffset {
                        kind: BindingKind::Global,
                        offset,
                        ..
                    }) => {
                        self.chunk().write(CallGlobal {
                            idx: offset,
                            args: args.len() as u32,
                        });
                    }
                    Some(BindingOffset {
                        kind: BindingKind::GlobalDataConstructor { tag, arity },
                        offset: _,
                        ..
                    }) if arity == args.len() as u32 => {
                        self.chunk().write(MakeAdt { tag, args: arity });
                    }
                    _ => {
                        self.chunk().write(Calli {
                            args: args.len() as u32,
                        });
                    }
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
            Expr::Lit(lit) => match &**lit {
                LitExpr::Bool(value) => self.chunk().write(LoadBool(*value)),
                LitExpr::Int(value) => self.chunk().write(LoadInt(*value)),
                LitExpr::Float(_value) => todo!("load float"),
                LitExpr::String(value) => {
                    let value = Value::Object(Rc::new(Object::String(value.clone())));
                    let str_const = self.chunk().write_const(value);
                    self.chunk().write(LoadConst(str_const));
                }
                LitExpr::Char(value) => self.chunk().write(LoadChar(*value)),
            },
            Expr::If(if_expr) => {
                self.visit_expr(&if_expr.cond);
                let then_jump = self.chunk().write_get_offset(CJump(0));
                self.visit_expr(&if_expr.else_);
                let else_jump = self.chunk().write_get_offset(Jump(0));
                self.chunk().patch_jump(then_jump);
                self.visit_expr(&if_expr.then);
                self.chunk().patch_jump(else_jump);
            }
            Expr::Match(match_expr) => {
                self.visit_expr(&match_expr.matched);
                let mut jumps = Vec::new();
                // Codegen for matching the pattern.
                for arm in &match_expr.arms {
                    self.visit_pattern(&arm.pattern);
                    // Jump to that arm if pattern was matched.
                    jumps.push(self.chunk().write_get_offset(CJump(0)));
                }
                // Codegen for the actual expression.
                let mut jumps_end = Vec::new();
                for (arm, jump) in match_expr.arms.iter().zip(jumps) {
                    self.chunk().patch_jump(jump);

                    let state = self.offset_state();
                    self.visit_pattern_bindings(&arm.pattern);
                    let diff = self.offset_state().next_offset - state.next_offset;

                    self.visit_expr(&arm.expr);

                    // Cleanup pattern bindings.
                    if diff != 0 {
                        self.chunk().write(Slide(diff));
                    }
                    self.restore_state(state);
                    jumps_end.push(self.chunk().write_get_offset(Jump(0)));
                }
                for jump_end in jumps_end {
                    self.chunk().patch_jump(jump_end);
                }
            }
            Expr::While(_) => todo!(),
            Expr::For(_) => todo!(),
            Expr::Loop(_) => todo!(),
            Expr::Return(_) => todo!(),
            Expr::Let(let_expr) => {
                let state = self.offset_state();
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
                self.restore_state(state);
            }
            Expr::Err => unreachable!(),
        }
    }

    /// The result of visitng a pattern should be a boolean value at the top of the stack
    /// representing whether this pattern was successfully matched.
    ///
    /// This does not create any bindings inside the pattern.
    fn visit_pattern(&mut self, pattern: &Spanned<Pattern>) {
        match &**pattern {
            Pattern::Path(_path) => {
                if let Some(symbol) = self.bindings_map.pattern_tags.get(pattern) {
                    let symbol = symbol.unwrap();
                    let tag = self.bindings[symbol].data_constructor_tag;
                    self.chunk().write(HasTag(tag));
                } else {
                    // Bindings match everything.
                    self.chunk().write(LoadBool(true));
                }
            }
            Pattern::Adt(adt) => {
                let symbol = self.bindings_map.pattern_tags[pattern].unwrap();
                let tag = self.bindings[symbol].data_constructor_tag;
                // First check if we have the right tag.
                self.chunk().write(HasTag(tag));

                // If we have the right tag, check all the sub patterns.
                let jump_true = self.chunk().write_get_offset(CJump(0));
                self.chunk().write(LoadBool(false));
                let jump_end = self.chunk().write_get_offset(Jump(0));

                self.chunk().patch_jump(jump_true);
                self.chunk().write(Dup);
                for (field, sub_pattern) in adt.of.iter().enumerate() {
                    self.chunk().write(GetField(field as u32));
                    self.visit_pattern(sub_pattern);
                    // Discard field.
                    self.chunk().write(Slide(1));
                    // Get the original value back on top (it's under `field` number of bools)
                    self.chunk().write(DupRel(field as u32 + 1));
                }
                self.chunk().write(Pop);
                // Get rid of the original value now.
                // Only match if the conjunction of all sub patterns match.
                for _ in 0..adt.of.len() - 1 {
                    self.chunk().write(BoolAnd);
                }

                self.chunk().patch_jump(jump_end);
            }
            Pattern::Lit(lit) => {
                self.chunk().write(Dup);
                // FIXME: code duplication with visit_expr.
                match &**lit {
                    LitExpr::Bool(value) => self.chunk().write(LoadBool(*value)),
                    LitExpr::Int(value) => self.chunk().write(LoadInt(*value)),
                    LitExpr::Float(_value) => todo!("load float"),
                    LitExpr::String(value) => {
                        let value = Value::Object(Rc::new(Object::String(value.clone())));
                        let str_const = self.chunk().write_const(value);
                        self.chunk().write(LoadConst(str_const));
                    }
                    LitExpr::Char(value) => self.chunk().write(LoadChar(*value)),
                }
                self.chunk().write(ValEq);
            }
            Pattern::Err => unreachable!(),
        }
    }
}

impl Codegen {
    // Create the bindings used in this pattern.
    fn visit_pattern_bindings(&mut self, pattern: &Spanned<Pattern>) {
        match &**pattern {
            Pattern::Path(_) => {
                if let Some(&binding) = self.bindings_map.pattern.get(pattern) {
                    let kind = if self.chunks.len() == 1 {
                        BindingKind::Global
                    } else {
                        BindingKind::Local
                    };
                    self.new_binding_offset(binding, kind);
                }
            }
            Pattern::Adt(adt) => {
                self.chunk().write(Dup);
                for (field, sub_pattern) in adt.of.iter().enumerate() {
                    if !matches!(&**sub_pattern, Pattern::Path(_)) {
                        self.inc_offset(); // TODO: do not use up useless stack space.
                    }
                    self.chunk().write(GetField(field as u32));
                    self.visit_pattern_bindings(sub_pattern);
                    self.chunk().write(DupRel(field as u32 + 1));
                }
                self.chunk().write(Pop);
            }
            Pattern::Lit(_) => {}
            Pattern::Err => unreachable!(),
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
