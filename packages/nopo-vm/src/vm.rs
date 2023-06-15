use std::rc::Rc;

use crate::types::{Instr, ObjClosure, UpValue, Value, ValueArray};

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
    upvalues: Vec<UpValue>,
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
            upvalues: Vec::new(),
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
        &self.frame().closure.func.chunk.code
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn cleanup_function(&mut self) {
        let ret_value = self.pop();
        let frame = self.call_stack.pop().unwrap();

        // TODO: close upvalues.

        // Cleanup locals created inside function.
        if frame.is_call_global {
            self.stack.truncate(frame.frame_pointer);
        } else {
            self.stack.truncate(frame.frame_pointer - 1);
        }
        self.stack.push(ret_value);
    }

    pub fn run(&mut self) {
        macro_rules! gen_int_op {
            ($op:tt) => {{
                let rhs = self.pop();
                let lhs = self.pop();
                let value = match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs $op rhs),
                    _ => unreachable!(),
                };
                self.stack.push(value);
            }};
        }
        macro_rules! gen_int_relational_op {
            ($op:tt) => {{
                let rhs = self.pop();
                let lhs = self.pop();
                let value = match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => Value::Bool(lhs $op rhs),
                    _ => unreachable!(),
                };
                self.stack.push(value);
            }};
        }

        loop {
            if self.ip() >= self.code().len() {
                if self.call_stack.len() == 1 {
                    // We have reached the end of the program.
                    return;
                } else {
                    // Return from a function.
                    self.cleanup_function();
                    continue;
                }
            }

            let instr = self.code()[self.ip()];
            match instr {
                Instr::LoadBool(value) => self.stack.push(Value::Bool(value)),
                Instr::LoadInt(value) => self.stack.push(Value::Int(value)),
                Instr::LoadFloat(value) => self.stack.push(Value::Float(value)),
                Instr::LoadChar(value) => self.stack.push(Value::Char(value)),
                Instr::LoadConst(idx) => self
                    .stack
                    .push(self.frame().closure.func.chunk.consts[idx as usize].clone()),
                Instr::LoadLocal(offset) => self
                    .stack
                    .push(self.stack[offset as usize + self.frame().frame_pointer].clone()),
                Instr::LoadGlobal(idx) => self.stack.push(self.stack[idx as usize].clone()),
                Instr::LoadUpValue(idx) => todo!(),
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
                    let callee = &self.stack[self.stack.len() - args as usize - 1];
                    let closure = callee.as_object().unwrap().as_closure().unwrap();
                    let callee_arity = closure.func.arity;
                    if callee_arity < args {
                        // Generate a lambda on the fly.
                        todo!("partial application");
                    } else if callee_arity == args {
                        self.call_stack.push(CallFrame {
                            ip: 0,
                            frame_pointer: self.stack.len() - callee_arity as usize,
                            is_call_global: false,
                            closure,
                        });
                    } else {
                        todo!("call closure first then call result with remaining args");
                    }

                    // Skip ip increment.
                    continue;
                }
                Instr::CallGlobal { idx, args } => {
                    *self.ip_mut() += 1;
                    let callee = &self.stack[idx as usize];
                    let closure = callee.as_object().unwrap().as_closure().unwrap();
                    let callee_arity = closure.func.arity;
                    if callee_arity < args {
                        // Generate a lambda on the fly.
                        todo!("partial application");
                    } else if callee_arity == args {
                        self.call_stack.push(CallFrame {
                            ip: 0,
                            frame_pointer: self.stack.len() - callee_arity as usize,
                            is_call_global: true,
                            closure,
                        });
                    } else {
                        todo!("call closure first then call result with remaining args");
                    }

                    // Skip ip increment.
                    continue;
                }
                Instr::MakeClosure { args } => todo!(),
                Instr::MakeTuple { args } => todo!(),
                Instr::MakeAdt { tag, args } => todo!(),
                Instr::GetField(_) => todo!(),
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
                Instr::Slide(idx) => {
                    let top = self.pop();
                    for _ in 0..idx {
                        let _ = self.pop();
                    }
                    self.stack.push(top);
                }
            }
            *self.ip_mut() += 1;
        }
    }
}
