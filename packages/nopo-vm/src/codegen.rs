//! Code generation.

use std::rc::Rc;

use la_arena::ArenaMap;
use nopo_diagnostics::span::Spanned;
use nopo_parser::ast::{Expr, LetId, LetItem, LitExpr, Pattern, Root, TypeDef, TypeId, TypeItem};
use nopo_parser::lexer::{BinOp, UnaryOp};
use nopo_parser::visitor::{walk_root, Visitor};
use nopo_passes::db::{BindingId, Db};

use crate::print::print_chunk;
use crate::types::Instr::*;
use crate::types::{Chunk, ChunkBuilder, Instr, ObjClosure, ObjProto, Object, Value, VmIndex};

#[derive(Debug)]
pub struct Codegen<'a> {
    db: &'a Db,
    offset_map: ArenaMap<BindingId, BindingOffset>,
    chunks: Vec<ChunkBuilder>,
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

impl<'a> Codegen<'a> {
    pub fn new(db: &'a Db) -> Self {
        Self {
            db,
            offset_map: ArenaMap::new(),
            chunks: Vec::new(),
        }
    }

    /// Get the last chunk in the chunks stack. This is probably where we want to codegen.
    fn chunk(&mut self) -> &mut ChunkBuilder {
        self.chunks.last_mut().unwrap()
    }

    /// Push a chunk with a name onto the chunk stack.
    fn new_chunk(&mut self, name: String, arity: u32) {
        self.chunks.push(ChunkBuilder::new(name, arity));
    }

    fn pop_chunk(&mut self) -> Rc<Chunk> {
        Rc::new(self.pop_chunk_builder().chunk)
    }

    fn pop_chunk_builder(&mut self) -> ChunkBuilder {
        let data = self.chunks.pop().unwrap();
        print_chunk(&data.chunk, &mut std::io::stderr()).unwrap(); // TODO: remove this.
        data
    }

    /// Insert a new binding into the offset map. The offset of the binding is the current offset
    /// of the stack.
    ///
    /// This should always be called __before__ the intrusction to load the value of the binding has
    /// been emitted.
    fn new_binding_at_top(&mut self, id: BindingId, kind: BindingKind) {
        let binding_data = BindingOffset {
            kind,
            offset: self.current_offset(),
            chunks_depth: self.chunks.len() - 1,
        };
        self.offset_map.insert(id, binding_data);
    }

    fn new_binding_at_pos(&mut self, id: BindingId, kind: BindingKind, pos: u32) {
        let binding_data = BindingOffset {
            kind,
            offset: pos,
            chunks_depth: self.chunks.len() - 1,
        };
        self.offset_map.insert(id, binding_data);
    }

    fn current_offset(&self) -> u32 {
        self.chunks.last().unwrap().offset
    }

    /// Threads a binding through a stack of closures and returns the upvalue offset.
    fn thread_binding_as_upvalue(&mut self, id: BindingId) -> u32 {
        let offset_data = self.offset_map[id];

        let current_depth = self.chunks.len() - 1;
        let decl_depth = offset_data.chunks_depth;
        assert!(current_depth > decl_depth);

        /// Adds an upvalue to a chunk if not already added. Returns the offset of the upvalue.
        fn add_upvalue_to_chunk(chunk: &mut ChunkBuilder, instr: Instr) -> u32 {
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
            LoadLocal(offset_data.offset),
        );
        // Scopes after that should capture upvalue from previous scope.
        if decl_depth + 2 < current_depth {
            for i in decl_depth + 2..current_depth {
                offset = add_upvalue_to_chunk(&mut self.chunks[i], LoadUpValue(offset));
            }
        }

        offset
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

impl Visitor for Codegen<'_> {
    fn visit_root(&mut self, root: &Root) {
        self.new_chunk("<import>".to_string(), 0);
        walk_root(self, root);
    }

    fn visit_type_item(&mut self, _idx: TypeId, item: &Spanned<TypeItem>) {
        match &*item.def {
            TypeDef::Adt(adt) => {
                for (tag, data_constructor) in adt.data_constructors.iter().enumerate() {
                    let binding = self.db.bindings_map.data_constructors[data_constructor];
                    // Create a lambda that calls the data constructor.
                    self.new_chunk(
                        data_constructor.ident.to_string(),
                        data_constructor.of.len() as u32,
                    );
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
                    self.new_binding_at_top(
                        binding,
                        BindingKind::GlobalDataConstructor {
                            tag: tag as u32,
                            arity: data_constructor.of.len() as u32,
                        },
                    );
                    self.chunk().write(LoadConst(slot));
                }
            }
            TypeDef::Record(_) => {}
            TypeDef::Err => unreachable!(),
        }
    }

    fn visit_let_item(&mut self, _idx: LetId, item: &Spanned<LetItem>) {
        let binding = self.db.bindings_map.let_items[item];
        // If let item has params, generate a closure. Otherwise, just evaluate value and push onto
        // global stack.
        match item.params.len() {
            0 => {
                self.new_binding_at_top(binding, BindingKind::Global);
                self.visit_expr(&item.expr);
            }
            arity => {
                self.new_binding_at_top(binding, BindingKind::Global);
                self.new_chunk(item.ident.to_string(), arity as u32);
                for (i, param) in item.params.iter().enumerate() {
                    let binding = self.db.bindings_map.params[param];
                    self.new_binding_at_pos(binding, BindingKind::Local, i as u32);
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
                let binding = self.db.bindings_map.idents[ident_expr].unwrap();
                let data = self.offset_map[binding];
                match data.kind {
                    BindingKind::GlobalDataConstructor { tag, arity: 0 } => {
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

                self.new_chunk("<lambda>".to_string(), arity as u32);
                for (i, param) in lambda_expr.params.iter().enumerate() {
                    let binding = self.db.bindings_map.lambda_params[param];
                    self.new_binding_at_pos(binding, BindingKind::Local, i as u32);
                }
                self.visit_expr(&lambda_expr.expr);
                let data = self.pop_chunk_builder();
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
                for expr in &tuple_expr.elements {
                    self.visit_expr(expr);
                }
                self.chunk().write(MakeTuple {
                    args: tuple_expr.elements.len() as u32,
                });
            }
            Expr::Record(record_expr) => {
                // Get all the fields and push in order of position in record.
                let mut fields = record_expr.fields.iter().collect::<Vec<_>>();
                fields.sort_by_cached_key(|field| self.db.record_expr_field_map[field]);
                for field in &fields {
                    self.visit_expr(&field.expr);
                }
                self.chunk().write(MakeTuple {
                    args: fields.len() as u32,
                });
            }
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::Dot => {
                let field_pos = self.db.record_field_map[expr];
                
                self.visit_expr(&bin_expr.lhs);
                self.chunk().write(GetField(field_pos));
            }
            Expr::Binary(bin_expr) if *bin_expr.op == BinOp::FnCall => {
                let (callee, args) = get_fn_call_callee_and_args(expr);
                assert!(!args.is_empty());

                let data = if let Expr::Ident(ident_expr) = &**callee {
                    let binding = self.db.bindings_map.idents[ident_expr].unwrap();
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
                let then_jump = self.chunk().write_get_pos(CJump(0));
                let split = self.chunk().split_branch();

                self.visit_expr(&if_expr.else_);
                let else_jump = self.chunk().write_get_pos(Jump(0));

                self.chunk().restore_split(split);

                self.chunk().patch_jump(then_jump);
                self.visit_expr(&if_expr.then);
                self.chunk().patch_jump(else_jump);
            }
            Expr::Match(match_expr) => {
                self.visit_expr(&match_expr.matched);
                let start_offset = self.current_offset();

                let mut jumps = Vec::new();

                // Codegen for matching the pattern.
                for arm in &match_expr.arms {
                    self.visit_pattern(&arm.pattern);
                    // Jump to that arm if pattern was matched.
                    jumps.push(self.chunk().write_get_pos(CJump(0)));
                }
                // Codegen for the actual expression.
                let split = self.chunk().split_branch();
                let mut jumps_end = Vec::new();
                for (arm, jump) in match_expr.arms.iter().zip(jumps) {
                    self.chunk().restore_split(split);
                    self.chunk().patch_jump(jump);
                    assert_eq!(start_offset, self.current_offset());

                    let offset = self.current_offset();
                    self.visit_pattern_bindings(&arm.pattern);
                    let diff = self.current_offset() - offset;

                    self.visit_expr(&arm.expr);

                    // Cleanup pattern bindings.
                    if diff != 0 {
                        self.chunk().write(Slide(diff));
                    }
                    jumps_end.push(self.chunk().write_get_pos(Jump(0)));
                }
                for jump_end in jumps_end {
                    self.chunk().patch_jump(jump_end);
                }
                // Get rid of matched expression.
                self.chunk().write(Slide(1));
            }
            Expr::While(_) => todo!(),
            Expr::For(_) => todo!(),
            Expr::Loop(_) => todo!(),
            Expr::Return(_) => todo!(),
            Expr::Let(let_expr) => {
                let binding = self.db.bindings_map.let_exprs[let_expr];
                let kind = if self.chunks.len() == 1 {
                    BindingKind::Global
                } else {
                    BindingKind::Local
                };
                self.new_binding_at_top(binding, kind);
                self.visit_expr(&let_expr.expr);

                self.visit_expr(&let_expr._in);
                self.chunk().write(Slide(1));
            }
            Expr::Macro(_) => unreachable!(),
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
                if let Some(symbol) = self.db.bindings_map.pattern_tags.get(pattern) {
                    let symbol = symbol.unwrap();
                    let tag = self.db.bindings[symbol].data_constructor_tag;
                    self.chunk().write(HasTag(tag));
                } else {
                    // Bindings match everything.
                    self.chunk().write(LoadBool(true));
                }
            }
            Pattern::Adt(adt) => {
                let symbol = self.db.bindings_map.pattern_tags[pattern].unwrap();
                let tag = self.db.bindings[symbol].data_constructor_tag;
                // First check if we have the right tag.
                self.chunk().write(HasTag(tag));

                // If we have the right tag, check all the sub patterns.
                let jump_true = self.chunk().write_get_pos(CJump(0));
                let split = self.chunk().split_branch();

                self.chunk().write(LoadBool(false));
                let jump_end = self.chunk().write_get_pos(Jump(0));

                self.chunk().restore_split(split);
                self.chunk().patch_jump(jump_true);
                self.chunk().write(Dup);
                let mut conjuncts = 0;
                for (field, sub_pattern) in adt.of.iter().enumerate() {
                    // If the sub-pattern is just a binding, don't even bother checking if it
                    // matches since it matches trivially.
                    if self.db.bindings_map.pattern.get(sub_pattern).is_none() {
                        conjuncts += 1;
                        self.chunk().write(GetField(field as u32));
                        self.visit_pattern(sub_pattern);
                        // Discard field.
                        self.chunk().write(Slide(1));
                        // Get the original value back on top (it's under `field` number of bools)
                        self.chunk().write(DupRel(conjuncts));
                    }
                }
                self.chunk().write(Pop);
                // Get rid of the original value now.
                // Only match if the conjunction of all sub patterns match.
                match conjuncts {
                    0 => self.chunk().write(LoadBool(true)),
                    1 => {}
                    n => {
                        for _ in 0..n - 1 {
                            self.chunk().write(BoolAnd);
                        }
                    }
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

impl Codegen<'_> {
    // Create the bindings used in this pattern.
    // Does not remove the original top value of the stack.
    fn visit_pattern_bindings(&mut self, pattern: &Spanned<Pattern>) {
        match &**pattern {
            Pattern::Path(_) => {
                if let Some(&binding) = self.db.bindings_map.pattern.get(pattern) {
                    let kind = if self.chunks.len() == 1 {
                        BindingKind::Global
                    } else {
                        BindingKind::Local
                    };
                    let offset = self.current_offset();
                    self.new_binding_at_pos(binding, kind, offset - 1);
                }
            }
            Pattern::Adt(adt) => {
                for (field, sub_pattern) in adt.of.iter().enumerate() {
                    self.chunk().write(DupRel(field as u32));
                    self.chunk().write(GetField(field as u32));
                    self.visit_pattern_bindings(sub_pattern);
                }
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
