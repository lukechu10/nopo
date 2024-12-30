use std::cmp::Ordering;
use std::rc::Rc;

use crate::print::print_chunk;
use crate::types::{ChunkBuilder, Instr, ObjClosure, ObjProto, Object, UpValue, Value, ValueArray};

#[derive(Debug)]
pub struct CallFrame {
    /// Instruction pointer.
    ip: usize,
    /// Index of the start of the call frame in the stack.
    frame_pointer: usize,
    /// Whether this function was called using calli or callglobal.
    is_call_global: bool,
    closure: Rc<ObjClosure>,
}

#[derive(Debug)]
pub struct Vm {
    pub stack: ValueArray,
    call_stack: Vec<CallFrame>,
}

impl Vm {
    pub fn new(closure: ObjClosure) -> Self {
        let frame = CallFrame {
            ip: 0,
            frame_pointer: 0,
            is_call_global: false,
            closure: Rc::new(closure),
        };
        Self {
            stack: Vec::new(),
            call_stack: vec![frame],
        }
    }

    fn frame(&self) -> &CallFrame {
        self.call_stack.last().unwrap()
    }
    fn frame_mut(&mut self) -> &mut CallFrame {
        self.call_stack.last_mut().unwrap()
    }

    fn ip(&self) -> usize {
        self.frame().ip
    }
    fn ip_mut(&mut self) -> &mut usize {
        &mut self.frame_mut().ip
    }

    fn code(&self) -> &[Instr] {
        &self.frame().closure.proto.chunk.code
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn cleanup_function(&mut self) {
        let ret_value = self.pop();
        let frame = self.call_stack.pop().unwrap();

        // Cleanup locals created inside function.
        if frame.is_call_global {
            self.stack.truncate(frame.frame_pointer);
        } else {
            self.stack.truncate(frame.frame_pointer - 1);
        }
        self.stack.push(ret_value);
    }

    fn calli(&mut self, args: u32) {
        let callee = &self.stack[self.stack.len() - args as usize - 1];
        let closure = callee.as_object().unwrap().as_closure().unwrap();
        let callee_arity = closure.proto.arity;
        match callee_arity.cmp(&args) {
            Ordering::Less => {
                // Call first with callee_args number of args. Then call that expression
                // again with remaining args.
                let extra_arity = args - callee_arity;
                let extra = (0..extra_arity).map(|_| self.pop()).collect::<Vec<_>>();
                // Get the new closure on the top of the stack.
                // We need to run this new frame to completion to get the value of the closre.
                self.calli(callee_arity);
                self.run_frame();

                for value in extra {
                    self.stack.push(value);
                }
                self.calli(extra_arity);
            }
            Ordering::Equal => {
                self.call_stack.push(CallFrame {
                    ip: 0,
                    frame_pointer: self.stack.len() - callee_arity as usize,
                    is_call_global: true,
                    closure,
                });
            }
            Ordering::Greater => {
                // Generate a lambda on the fly. Capture all arguments as upvalues. Capture the
                // original closure as the lambda_arity-th upvalue.
                let lambda_arity = callee_arity - args;
                let mut chunk = ChunkBuilder::new("<partial>".to_string(), lambda_arity);
                let mut upvalues = (0..args)
                    .map(|_| self.pop())
                    .map(UpValue)
                    .collect::<Vec<_>>();
                upvalues.push(UpValue(self.pop())); // This should be the closure.
                chunk.write(Instr::LoadUpValue(lambda_arity));
                for i in 0..args {
                    chunk.write(Instr::LoadUpValue(i));
                }
                for i in 0..lambda_arity {
                    chunk.write(Instr::LoadLocal(i));
                }
                chunk.write(Instr::Calli { args: callee_arity });
                let chunk = chunk.into_chunk();
                print_chunk(&chunk, &mut std::io::stderr()).unwrap();
                let closure = ObjClosure {
                    proto: ObjProto {
                        chunk: Rc::new(chunk),
                        arity: lambda_arity,
                        upvalues_count: args,
                    },
                    upvalues,
                };
                self.stack
                    .push(Value::Object(Rc::new(Object::Closure(Rc::new(closure)))));
            }
        }
    }
    fn call_global(&mut self, idx: u32, args: u32) {
        let callee = &self.stack[idx as usize];
        let closure = callee.as_object().unwrap().as_closure().unwrap();
        let callee_arity = closure.proto.arity;
        match callee_arity.cmp(&args) {
            Ordering::Less => {
                // Call first with callee_args number of args. Then call that expression
                // again with remaining args.
                let extra_arity = args - callee_arity;
                let extra = (0..extra_arity).map(|_| self.pop()).collect::<Vec<_>>();
                // Get the new closure on the top of the stack.
                // We need to run this new frame to completion to get the value of the closre.
                self.call_global(idx, callee_arity);
                self.run_frame();

                for value in extra {
                    self.stack.push(value);
                }
                self.calli(extra_arity);
            }
            Ordering::Equal => {
                self.call_stack.push(CallFrame {
                    ip: 0,
                    frame_pointer: self.stack.len() - callee_arity as usize,
                    is_call_global: true,
                    closure,
                });
            }
            Ordering::Greater => {
                // Generate a lambda on the fly. Capture all arguments as upvalues.
                let lambda_arity = callee_arity - args;
                let mut chunk = ChunkBuilder::new("<partial>".to_string(), lambda_arity);
                let upvalues = (0..args)
                    .map(|_| self.pop())
                    .map(UpValue)
                    .collect::<Vec<_>>();
                for i in 0..args {
                    chunk.write(Instr::LoadUpValue(i));
                }
                for i in 0..lambda_arity {
                    chunk.write(Instr::LoadLocal(i));
                }
                chunk.write(Instr::CallGlobal {
                    idx,
                    args: callee_arity,
                });
                let chunk = chunk.into_chunk();
                print_chunk(&chunk, &mut std::io::stderr()).unwrap();
                let closure = ObjClosure {
                    proto: ObjProto {
                        chunk: Rc::new(chunk),
                        arity: lambda_arity,
                        upvalues_count: args,
                    },
                    upvalues,
                };
                self.stack
                    .push(Value::Object(Rc::new(Object::Closure(Rc::new(closure)))));
            }
        }
    }

    pub fn run(&mut self) {
        loop {
            self.run_frame();
            if self.call_stack.len() == 1 {
                // We have reached the end of the program.
                return;
            } else {
                // Return from a function.
                self.cleanup_function();
                continue;
            }
        }
    }

    /// Runs the interpreter loop until the end of the call frame has been reached.
    fn run_frame(&mut self) {
        macro_rules! gen_int_op {
            ($op:tt) => {{
                let rhs = self.pop();
                let lhs = self.stack.last().unwrap();
                let value = match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(*lhs $op rhs),
                    _ => unreachable!(),
                };
                *self.stack.last_mut().unwrap() = value;
            }};
        }
        macro_rules! gen_int_relational_op {
            ($op:tt) => {{
                let rhs = self.pop();
                let lhs = self.stack.last().unwrap();
                let value = match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(*lhs $op rhs),
                    _ => unreachable!(),
                };
                *self.stack.last_mut().unwrap() = value;
            }};
        }

        while self.ip() < self.code().len() {
            let instr = self.code()[self.ip()];
            let stack_len = self.stack.len();
            match instr {
                Instr::LoadBool(value) => self.stack.push(Value::Bool(value)),
                Instr::LoadInt(value) => self.stack.push(Value::Int(value)),
                Instr::LoadFloat(value) => self.stack.push(Value::Float(value)),
                Instr::LoadChar(value) => self.stack.push(Value::Char(value)),
                Instr::LoadConst(idx) => self
                    .stack
                    .push(self.frame().closure.proto.chunk.consts[idx as usize].clone()),
                Instr::LoadLocal(offset) => self
                    .stack
                    .push(self.stack[offset as usize + self.frame().frame_pointer].clone()),
                Instr::LoadGlobal(idx) => self.stack.push(self.stack[idx as usize].clone()),
                Instr::LoadUpValue(idx) => {
                    let upvalue = self.frame().closure.upvalues[idx as usize].clone();
                    self.stack.push(upvalue.0);
                }
                Instr::Dup => {
                    self.stack.push(self.stack.last().unwrap().clone());
                }
                Instr::DupRel(n) => {
                    self.stack
                        .push(self.stack[self.stack.len() - 1 - n as usize].clone());
                }
                Instr::Swap => {
                    let stack_len = self.stack.len();
                    self.stack.swap(stack_len - 1, stack_len - 2);
                }
                Instr::Jump(distance) => {
                    *self.ip_mut() += distance as usize;
                }
                Instr::CJump(distance) => {
                    let cond = self.pop().as_bool().unwrap();
                    if cond {
                        *self.ip_mut() += distance as usize;
                    }
                }
                Instr::Calli { args } => {
                    *self.ip_mut() += 1;
                    self.calli(args);
                    // Skip ip increment.
                    continue;
                }
                Instr::CallGlobal { idx, args } => {
                    *self.ip_mut() += 1;
                    self.call_global(idx, args);
                    // Skip ip increment.
                    continue;
                }
                Instr::MakeClosure { idx, upvalues } => {
                    let upvalues = (0..upvalues)
                        .map(|_| self.pop())
                        .map(UpValue)
                        .collect::<Vec<_>>();
                    let proto = self.frame().closure.proto.chunk.consts[idx as usize]
                        .as_object()
                        .unwrap()
                        .as_proto()
                        .unwrap()
                        .clone();
                    self.stack
                        .push(Value::Object(Rc::new(Object::Closure(Rc::new(
                            ObjClosure {
                                proto: proto.clone(),
                                upvalues,
                            },
                        )))));
                }
                Instr::MakeTuple { args } => {
                    let mut values = (0..args).map(|_| self.pop()).collect::<Vec<_>>();
                    values.reverse();
                    self.stack
                        .push(Value::Object(Rc::new(Object::Tuple(values))));
                }
                Instr::MakeAdt { tag, args } => {
                    let mut values = (0..args).map(|_| self.pop()).collect::<Vec<_>>();
                    values.reverse();
                    self.stack
                        .push(Value::Object(Rc::new(Object::Adt(tag, values))));
                }
                Instr::GetField(idx) => {
                    let value = self.pop();
                    let field = match &**value.as_object().unwrap() {
                        Object::Tuple(values) | Object::Adt(_, values) => {
                            values[idx as usize].clone()
                        }
                        _ => unreachable!(),
                    };
                    self.stack.push(field);
                }
                Instr::GetFieldPush(idx) => {
                    let value = self.stack.last().unwrap();
                    let field = match &**value.as_object().unwrap() {
                        Object::Tuple(values) | Object::Adt(_, values) => {
                            values[idx as usize].clone()
                        }
                        _ => unreachable!(),
                    };
                    self.stack.push(field);
                }
                Instr::HasTag(tag) => {
                    let value = self.stack.last().unwrap();
                    let has_tag = *value.as_object().unwrap().as_adt().unwrap().0 == tag;
                    self.stack.push(Value::Bool(has_tag));
                }
                Instr::IntAdd => gen_int_op!(+),
                Instr::IntSub => gen_int_op!(-),
                Instr::IntMul => gen_int_op!(*),
                Instr::IntDiv => gen_int_op!(/),
                Instr::IntMod => gen_int_op!(%),
                Instr::IntAnd => gen_int_op!(&),
                Instr::IntOr => gen_int_op!(|),
                Instr::IntXor => gen_int_op!(^),
                Instr::IntShl => gen_int_op!(<<),
                Instr::IntShr => gen_int_op!(>>),
                Instr::IntRor => {
                    let first = self.pop();
                    let second = self.pop();
                    let value = match (first, second) {
                        (Value::Int(first), Value::Int(second)) => {
                            Value::Int(first.rotate_right(second as u32))
                        }
                        _ => unreachable!(),
                    };
                    self.stack.push(value);
                }
                Instr::IntLt => gen_int_relational_op!(<),
                Instr::IntGt => gen_int_relational_op!(>),
                Instr::IntLte => gen_int_relational_op!(<=),
                Instr::IntGte => gen_int_relational_op!(>=),
                Instr::BoolNot => {
                    let value = self.pop();
                    self.stack.push(Value::Bool(!value.as_bool().unwrap()));
                }
                Instr::BoolAnd => {
                    let first = self.pop().as_bool().unwrap();
                    let second = self.pop().as_bool().unwrap();
                    self.stack.push(Value::Bool(first && second));
                }
                Instr::BoolOr => {
                    let first = self.pop().as_bool().unwrap();
                    let second = self.pop().as_bool().unwrap();
                    self.stack.push(Value::Bool(first || second));
                }
                Instr::ValEq => {
                    let first = self.pop();
                    let second = self.pop();
                    let value = match (first, second) {
                        (Value::Int(first), Value::Int(second)) => first == second,
                        (Value::Bool(first), Value::Bool(second)) => first == second,
                        (Value::Char(first), Value::Char(second)) => first == second,
                        (Value::Object(_first), Value::Object(_second)) => todo!(),
                        (first, second) => unreachable!("cannot compare {first:?} with {second:?}"),
                    };
                    self.stack.push(Value::Bool(value));
                }
                Instr::Pop => {
                    let _ = self.pop();
                }
                Instr::PopN(n) => {
                    for _ in 0..n {
                        let _ = self.pop();
                    }
                }
                Instr::Slide(idx) => {
                    let top = self.pop();
                    for _ in 0..idx {
                        let _ = self.pop();
                    }
                    self.stack.push(top);
                }
            }
            debug_assert_eq!(self.stack.len() as i32, stack_len as i32 + instr.adjust());
            *self.ip_mut() += 1;
        }
    }
}

impl Drop for Vm {
    fn drop(&mut self) {
        if std::thread::panicking() {
            // VM has crashed. Print some debugging info.
            eprintln!("== VM Crashed ==");
            eprintln!("== Chunk name: {}", self.frame().closure.proto.chunk.name);
            eprintln!("== IP: {}", self.frame().ip);
            eprintln!("== FP: {}", self.frame().frame_pointer);
            eprintln!("== STACK");
            for (i, value) in self.stack.iter().enumerate() {
                println!("{i}: {value}");
            }
        }
    }
}
