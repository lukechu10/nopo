use std::marker::PhantomData;
use std::rc::Rc;

pub type VmIndex = u32;
pub type VmBool = bool;
pub type VmInt = i64;
pub type VmChar = char;

#[derive(Debug, Clone, Copy)]
pub struct VmFloat(f64);
impl From<f64> for VmFloat {
    fn from(value: f64) -> Self {
        Self(value)
    }
}
impl From<VmFloat> for f64 {
    fn from(value: VmFloat) -> Self {
        value.0
    }
}
impl PartialEq for VmFloat {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}
impl Eq for VmFloat {}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Instr {
    /// Load a bool onto the stack.
    LoadBool(VmBool),
    /// Load an int onto the stack.
    LoadInt(VmInt),
    /// Load a float onto the stack.
    LoadFloat(VmFloat),
    /// Load a char onto the stack.
    LoadChar(VmChar),
    /// Push the value that is at index in the constant table.
    LoadConst(VmIndex),
    /// Load a local variable (index relative to frame pointer).
    LoadLocal(VmIndex),
    /// Load a global variable (absolute index in stack).
    LoadGlobal(VmIndex),
    /// Jump to the relative index in the current calling frame.
    Jump(VmIndex),
    /// Branched jump to the relative index in the current calling frame, if and only if the top
    /// value of the stack is `true`. Pops the top of the stack.
    CJump(VmIndex),
    /// Call the function that is at the top of the stack.
    Calli {
        /// How many args.
        args: VmIndex,
    },
    /// Make a new closure.
    MakeClosure {
        /// How many args.
        args: VmIndex,
    },
    /// Get a field of a tuple that is at the top of the stack. Replaces the top of the stack with
    /// the value of the field.
    GetField(VmIndex),

    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,

    IntAnd,
    IntOr,
    IntXor,
    /// Shift int left.
    IntShl,
    /// Shift int right.
    IntShr,
    /// Rotate int right.
    IntRor,

    BoolNot,
    BoolAnd,
    BoolOr,

    /// Compares the top two values on the stack for equality.
    /// Replaces these two values with a new value of type bool.
    ValEq,

    /// Pop a value of the stack and discard it.
    Pop,
}

/// A block of bytecode.
#[derive(Debug)]
pub struct Chunk {
    pub code: Vec<Instr>,
    pub consts: ValueArray,
    /// The name of the chunk.
    pub name: String,
}

impl Chunk {
    pub fn new(name: String) -> Self {
        Self {
            code: Vec::new(),
            consts: Vec::new(),
            name,
        }
    }

    /// Writes a new instruction to the code buffer. Returns the offset of the instruction.
    pub fn write_get_offset(&mut self, instr: Instr) -> usize {
        let offset = self.code.len();
        self.code.push(instr);
        offset
    }

    pub fn write(&mut self, instr: Instr) {
        let _ = self.write_get_offset(instr);
    }
    ///
    /// Patch a jump instruction to jump to the current offset.
    pub fn patch_jump(&mut self, offset: usize) {
        let current = self.code.len();
        let distance = current - offset - 1; // -1 for the jump instruction itself.
        match &mut self.code[offset] {
            Instr::Jump(x) | Instr::CJump(x) => *x = distance as u32,
            _ => panic!("instruction at {offset} is not a jump"),
        }
    }

    pub fn write_const(&mut self, value: Value) -> u32 {
        let idx = self.consts.len();
        self.consts.push(value);
        idx as u32
    }

    pub fn patch_const(&mut self, slot: u32) -> &mut Value {
        &mut self.consts[slot as usize]
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Bool(VmBool),
    Int(VmInt),
    Float(VmFloat),
    Char(VmChar),
    Object(Rc<Object>),
}

impl Value {
    pub fn as_bool(&self) -> Option<VmBool> {
        if let Self::Bool(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<VmInt> {
        if let Self::Int(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub fn as_float(&self) -> Option<VmFloat> {
        if let Self::Float(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub fn as_char(&self) -> Option<VmChar> {
        if let Self::Char(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub fn as_object(&self) -> Option<&Rc<Object>> {
        if let Self::Object(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub enum UpValue {
    Open(VmIndex),
    Closed(Value),
}

#[derive(Debug)]
pub enum Object {
    String(String),
    Tuple(Vec<Value>),
    Fn(ObjProto),
    Closure(ObjClosure),
}

#[derive(Debug)]
pub struct ObjProto {
    /// The number of arguments that this function takes.
    pub arity: VmIndex,
    pub chunk: Chunk,
    /// The number of captured upvalues.
    pub upvalues_count: VmIndex,
}

#[derive(Debug)]
pub struct ObjClosure {
    pub func: ObjProto,
    pub upvalues: Vec<UpValue>,
}

pub type ValueArray = Vec<Value>;
