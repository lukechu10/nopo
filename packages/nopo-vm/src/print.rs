//! Print bytecode.

use std::{fmt, io};

use yansi::Paint;

use crate::types::{Chunk, Instr};

pub fn print_chunk(chunk: &Chunk, f: &mut dyn io::Write) -> io::Result<()> {
    writeln!(f, "== {} ==", chunk.name)?;
    writeln!(f, "== CODE")?;
    for (offset, instr) in chunk.code.iter().enumerate() {
        writeln!(f, "{:>4} {instr}", Paint::rgb(150, 150, 150, offset))?;
    }
    writeln!(f, "== CONSTS")?;
    for (idx, value) in chunk.consts.iter().enumerate() {
        writeln!(f, "{:>4} {value}", Paint::rgb(150, 150, 150, idx))?;
    }
    writeln!(f, "")?;
    Ok(())
}

impl fmt::Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instr::LoadBool(value) => write!(f, "{:<15} {value}", "load.bool"),
            Instr::LoadInt(value) => write!(f, "{:<15} {value}", "load.int"),
            Instr::LoadFloat(value) => write!(f, "{:<15} {value}", "load.float"),
            Instr::LoadChar(value) => write!(f, "{:<15} {value}", "load.char"),
            Instr::LoadConst(value) => write!(f, "{:<15} {value}", "load.const"),
            Instr::LoadLocal(value) => write!(f, "{:<15} {value}", "load.local"),
            Instr::LoadGlobal(value) => write!(f, "{:<15} {value}", "load.global"),
            Instr::LoadUpValue(value) => write!(f, "{:<15} {value}", "load.upvalue"),
            Instr::Jump(value) => write!(f, "{:<15} {value}", "jump"),
            Instr::CJump(value) => write!(f, "{:<15} {value}", "cjump"),
            Instr::Calli { args } => write!(f, "{:<15} args: {args}", "calli"),
            Instr::CallGlobal { idx, args } => {
                write!(f, "{:<15} args: {args}, idx: {idx}", "call.global")
            }
            Instr::MakeClosure { idx, upvalues } => write!(
                f,
                "{:<15} args: {idx}, upvalues: {upvalues}",
                "make.closure"
            ),
            Instr::MakeTuple { args } => write!(f, "{:<15} args: {args}", "make.tuple"),
            Instr::MakeAdt { tag, args } => {
                write!(f, "{:<15} tag: {tag}, args: {args}", "make.adt")
            }
            Instr::GetField(value) => write!(f, "{:<15} {value}", "get.field"),
            Instr::IntAdd => write!(f, "{:<15}", "int.add"),
            Instr::IntSub => write!(f, "{:<15}", "int.sub"),
            Instr::IntMul => write!(f, "{:<15}", "int.mul"),
            Instr::IntDiv => write!(f, "{:<15}", "int.div"),
            Instr::IntMod => write!(f, "{:<15}", "int.mod"),
            Instr::IntAnd => write!(f, "{:<15}", "int.and"),
            Instr::IntOr => write!(f, "{:<15}", "int.or"),
            Instr::IntXor => write!(f, "{:<15}", "int.xor"),
            Instr::IntShl => write!(f, "{:<15}", "int.shl"),
            Instr::IntShr => write!(f, "{:<15}", "int.shr"),
            Instr::IntRor => write!(f, "{:<15}", "int.ror"),
            Instr::IntLt => write!(f, "{:<15}", "int.lt"),
            Instr::IntGt => write!(f, "{:<15}", "int.gt"),
            Instr::IntLte => write!(f, "{:<15}", "int.lte"),
            Instr::IntGte => write!(f, "{:<15}", "int.gte"),
            Instr::BoolNot => write!(f, "{:<15}", "bool.not"),
            Instr::BoolAnd => write!(f, "{:<15}", "bool.and"),
            Instr::BoolOr => write!(f, "{:<15}", "bool.or"),
            Instr::ValEq => write!(f, "{:<15}", "eq"),
            Instr::Pop => write!(f, "{:<15}", "pop"),
            Instr::Slide(n) => write!(f, "{:<15} {n}", "slide"),
        }
    }
}
