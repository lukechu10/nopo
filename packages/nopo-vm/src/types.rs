use std::fmt;
use std::rc::Rc;

pub type VmIndex = u32;
pub type VmBool = bool;
pub type VmInt = i64;
pub type VmChar = char;

#[derive(Debug, Clone, Copy)]
pub struct VmFloat(pub f64);
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
impl fmt::Display for VmFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

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
    /// Load an upvalue.
    LoadUpValue(VmIndex),
    /// Duplicate the top value.
    Dup,
    /// Duplicate the value that is a certain number of indices below the top.
    /// An index of `0` is equivalent to `Dup`.
    DupRel(VmIndex),
    /// Swap the top two values.
    Swap,
    /// Jump to the relative index in the current calling frame.
    Jump(VmIndex),
    /// Branched jump to the relative index in the current calling frame, if and only if the top
    /// value of the stack is `true`. Pops the top of the stack.
    CJump(VmIndex),
    /// Calls a function with `args` number of arguments. The function should be below all the
    /// arguments.
    Calli {
        /// How many args.
        args: VmIndex,
    },
    /// Calls a global directly with `args` number of arguments.
    CallGlobal {
        /// Global index of function to call.
        idx: VmIndex,
        /// How many args.
        args: VmIndex,
    },
    /// Make a new closure.
    MakeClosure {
        /// Index of proto object in constants table.
        idx: VmIndex,
        /// How many upvalues.
        upvalues: VmIndex,
    },
    MakeTuple {
        /// How many args.
        args: VmIndex,
    },
    MakeAdt {
        /// Tag of the ADT.
        tag: VmIndex,
        /// How many args.
        args: VmIndex,
    },
    /// Get a field of a tuple or adt that is at the top of the stack. Replaces the top of the
    /// stack with the value of the field.
    GetField(VmIndex),
    /// Get a field of a tuple or adt that is at the top of the stack. Pushes, instead of replacing
    /// the top.
    GetFieldPush(VmIndex),
    /// Pushes a boolean representing whether the current top value is an ADT with the specified
    /// tag.
    HasTag(VmIndex),

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

    IntLt,
    IntGt,
    IntLte,
    IntGte,

    BoolNot,
    BoolAnd,
    BoolOr,

    /// Compares the top two values on the stack for equality.
    /// Replaces these two values with a new value of type bool.
    ValEq,

    /// Pop a value of the stack and discard it.
    Pop,
    /// Pop n values of the stack and discard them.
    PopN(VmIndex),
    /// Pops the top value. Then pops index number of values. Finally pushes the top value back on.
    Slide(VmIndex),
}

impl Instr {
    /// How much this instruction adjusts the stack.
    pub fn adjust(self) -> i32 {
        match self {
            Instr::LoadBool(_)
            | Instr::LoadInt(_)
            | Instr::LoadFloat(_)
            | Instr::LoadChar(_)
            | Instr::LoadConst(_)
            | Instr::LoadLocal(_)
            | Instr::LoadGlobal(_)
            | Instr::LoadUpValue(_) => 1,
            Instr::Dup | Instr::DupRel(_) => 1,
            Instr::Swap => 0,
            Instr::Jump(_) => 0,
            Instr::CJump(_) => -1,
            Instr::Calli { args } => -(args as i32),
            Instr::CallGlobal { idx: _, args } => -(args as i32) + 1,
            Instr::MakeClosure { idx: _, upvalues } => -(upvalues as i32) + 1,
            Instr::MakeTuple { args } => -(args as i32) + 1,
            Instr::MakeAdt { tag: _, args } => -(args as i32) + 1,
            Instr::GetField(_) => 0,
            Instr::GetFieldPush(_) => 1,
            Instr::HasTag(_) => 1,
            Instr::IntAdd
            | Instr::IntSub
            | Instr::IntMul
            | Instr::IntDiv
            | Instr::IntMod
            | Instr::IntAnd
            | Instr::IntOr
            | Instr::IntXor
            | Instr::IntShl
            | Instr::IntShr
            | Instr::IntRor
            | Instr::IntLt
            | Instr::IntGt
            | Instr::IntLte
            | Instr::IntGte => -1,
            Instr::BoolNot => 0,
            Instr::BoolAnd | Instr::BoolOr | Instr::ValEq => -1,
            Instr::Pop => -1,
            Instr::PopN(n) => -(n as i32),
            Instr::Slide(n) => -(n as i32),
        }
    }
}

/// A block of bytecode.
#[derive(Debug)]
pub struct Chunk {
    pub code: Vec<Instr>,
    pub consts: ValueArray,
    /// The name of the chunk.
    pub name: String,
}

#[derive(Debug)]
pub struct ChunkBuilder {
    pub chunk: Chunk,
    /// The current stack offset.
    /// Should be initialized to the arity of the function.
    pub offset: u32,
    /// Instructions for capturing upvalues.
    pub upvalues: Vec<Instr>,
}

/// Stores the offset before the branching.
/// THis can be used to restore the offset when doing codegen for the other branch.
#[derive(Debug, Clone, Copy)]
#[must_use]
pub struct ChunkSplit(u32);

impl ChunkBuilder {
    pub fn new(name: String, arity: u32) -> Self {
        Self {
            chunk: Chunk {
                code: Vec::new(),
                consts: Vec::new(),
                name,
            },
            offset: arity,
            upvalues: Vec::new(),
        }
    }

    /// Writes a new instruction to the code buffer. Returns the byte position of the instruction.
    pub fn write_get_pos(&mut self, instr: Instr) -> usize {
        let pos = self.chunk.code.len();
        self.offset = (self.offset as i32 + instr.adjust()) as u32;
        self.chunk.code.push(instr);
        pos
    }

    pub fn write(&mut self, instr: Instr) {
        let _ = self.write_get_pos(instr);
    }

    /// Patch a jump instruction to jump to the current offset.
    pub fn patch_jump(&mut self, offset: usize) {
        let current = self.chunk.code.len();
        let distance = current - offset - 1; // -1 for the jump instruction itself.
        match &mut self.chunk.code[offset] {
            Instr::Jump(x) | Instr::CJump(x) => *x = distance as u32,
            _ => panic!("instruction at {offset} is not a jump"),
        }
    }

    pub fn write_const(&mut self, value: Value) -> u32 {
        let idx = self.chunk.consts.len();
        self.chunk.consts.push(value);
        idx as u32
    }

    pub fn patch_const(&mut self, slot: u32) -> &mut Value {
        &mut self.chunk.consts[slot as usize]
    }

    /// Should be called right after branch instruction but before anything in the branch itself.
    pub fn split_branch(&mut self) -> ChunkSplit {
        ChunkSplit(self.offset)
    }

    /// Should be called when moving to codegen of other branch.
    pub fn restore_split(&mut self, split: ChunkSplit) {
        self.offset = split.0;
    }

    pub fn into_chunk(self) -> Chunk {
        self.chunk
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

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(value) => value.fmt(f),
            Value::Int(value) => value.fmt(f),
            Value::Float(value) => value.0.fmt(f),
            Value::Char(value) => value.fmt(f),
            Value::Object(obj) => match obj.as_ref() {
                Object::String(value) => value.fmt(f),
                Object::Tuple(values) => {
                    // FIXME: type-aware printing.
                    write!(f, "<tuple> (")?;
                    if let Some(first) = values.first() {
                        write!(f, "{first}")?;
                    }
                    for value in values.iter().skip(1) {
                        write!(f, ", {value}")?;
                    }
                    write!(f, ")")?;
                    Ok(())
                }
                Object::Adt(tag, values) => {
                    // FIXME: type-aware printing.
                    write!(f, "<tag={tag}> (")?;
                    if let Some(first) = values.first() {
                        write!(f, "{first}")?;
                    }
                    for value in values.iter().skip(1) {
                        write!(f, ", {value}")?;
                    }
                    write!(f, ")")?;
                    Ok(())
                }
                Object::Proto(proto) => write!(f, "<proto {}>", proto.chunk.name),
                Object::Closure(closure) => write!(f, "<closure {}>", closure.proto.chunk.name),
            },
        }
    }
}

/// Represents a captured value in a closure.
#[derive(Debug, Clone)]
pub struct UpValue(pub Value);

#[derive(Debug)]
pub enum Object {
    String(String),
    Tuple(Vec<Value>),
    Adt(VmIndex, Vec<Value>),
    Proto(ObjProto),
    Closure(Rc<ObjClosure>),
}

impl Object {
    pub fn as_string(&self) -> Option<&String> {
        if let Self::String(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_tuple(&self) -> Option<&Vec<Value>> {
        if let Self::Tuple(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_adt(&self) -> Option<(&VmIndex, &Vec<Value>)> {
        if let Self::Adt(idx, values) = self {
            Some((idx, values))
        } else {
            None
        }
    }

    pub fn as_proto(&self) -> Option<&ObjProto> {
        if let Self::Proto(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_closure(&self) -> Option<Rc<ObjClosure>> {
        if let Self::Closure(v) = self {
            Some(v.clone())
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct ObjProto {
    /// The number of arguments that this function takes.
    pub arity: VmIndex,
    pub chunk: Rc<Chunk>,
    /// The number of captured upvalues.
    pub upvalues_count: VmIndex,
}

#[derive(Debug)]
pub struct ObjClosure {
    pub proto: ObjProto,
    pub upvalues: Vec<UpValue>,
}

pub type ValueArray = Vec<Value>;
