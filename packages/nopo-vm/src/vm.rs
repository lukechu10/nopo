use crate::types::{Instr, ObjClosure, UpValue, Value, ValueArray};

#[derive(Debug)]
pub struct CallFrame {
    /// Instruction pointer.
    ip: usize,
    /// Index of the start of the call frame in the stack.
    frame_pointer: usize,
    closure: ObjClosure,
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
            closure,
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

    pub fn run(&mut self) {
        macro_rules! gen_int_op {
            ($op:tt) => {{
                let first = self.pop();
                let second = self.pop();
                let value = match (first, second) {
                    (Value::Int(first), Value::Int(second)) => Value::Int(first $op second),
                    _ => unreachable!(),
                };
                self.stack.push(value);
            }};
        }

        while self.ip() < self.code().len() {
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
                Instr::Jump(distance) => {
                    *self.ip_mut() += distance as usize;
                }
                Instr::CJump(distance) => {
                    let cond = self.pop().as_bool().unwrap();
                    if cond {
                        *self.ip_mut() += distance as usize;
                    }
                }
                Instr::Calli { args } => todo!(),
                Instr::MakeClosure { args } => todo!(),
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
                Instr::IntRor => todo!(),
                Instr::BoolNot => todo!(),
                Instr::BoolAnd => todo!(),
                Instr::BoolOr => todo!(),
                Instr::ValEq => {
                    let first = self.pop();
                    let second = self.pop();
                    let value = match (first, second) {
                        (Value::Int(first), Value::Int(second)) => first == second,
                        (Value::Bool(first), Value::Bool(second)) => first == second,
                        (Value::Char(first), Value::Char(second)) => first == second,
                        (Value::Object(_first), Value::Object(_second)) => todo!(),
                        _ => todo!(),
                    };
                    self.stack.push(Value::Bool(value));
                }
                Instr::Pop => todo!(),
            }
            *self.ip_mut() += 1;
        }
    }
}
