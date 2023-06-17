//! Print bytecode.

use std::{fmt, io};

use yansi::Paint;

use crate::types::{Chunk, Instr};

pub fn print_chunk(chunk: &Chunk, f: &mut dyn io::Write) -> io::Result<()> {
    writeln!(f, "== {} ==", chunk.name)?;
    writeln!(f, "== CODE")?;
    for (offset, instr) in chunk.code.iter().copied().enumerate() {
        writeln!(
            f,
            "{:>4} {}",
            Paint::rgb(150, 150, 150, offset),
            InstrOffset(offset, instr)
        )?;
    }
    writeln!(f, "== CONSTS")?;
    for (idx, value) in chunk.consts.iter().enumerate() {
        writeln!(f, "{:>4} {value}", Paint::rgb(150, 150, 150, idx))?;
    }
    writeln!(f, "")?;
    Ok(())
}

struct InstrOffset(usize, Instr);

impl fmt::Display for InstrOffset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let &Self(byte_pos, instr) = self;
        match instr {
            Instr::LoadBool(value) => write!(f, "{:<15} value: {value}", "load.bool"),
            Instr::LoadInt(value) => write!(f, "{:<15} value: {value}", "load.int"),
            Instr::LoadFloat(value) => write!(f, "{:<15} value: {value}", "load.float"),
            Instr::LoadChar(value) => write!(f, "{:<15} value: {value}", "load.char"),
            Instr::LoadConst(idx) => write!(f, "{:<15} idx: {idx}", "load.const"),
            Instr::LoadLocal(idx) => write!(f, "{:<15} idx: {idx}", "load.local"),
            Instr::LoadGlobal(idx) => write!(f, "{:<15} idx: {idx}", "load.global"),
            Instr::LoadUpValue(idx) => write!(f, "{:<15} idx: {idx}", "load.upvalue"),
            Instr::Dup => write!(f, "{:<15}", "dup"),
            Instr::Jump(offset) => write!(
                f,
                "{:<15} offset: {offset} (target: {})",
                "jump",
                byte_pos as u32 + offset + 1
            ),
            Instr::CJump(offset) => write!(
                f,
                "{:<15} offset: {offset} (target: {})",
                "cjump",
                byte_pos as u32 + offset + 1
            ),
            Instr::Calli { args } => write!(f, "{:<15} args: {args}", "calli"),
            Instr::CallGlobal { idx, args } => {
                write!(f, "{:<15} idx: {idx}, args: {args}", "call.global")
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
            Instr::GetField(idx) => write!(f, "{:<15} idx: {idx}", "get.field"),
            Instr::GetFieldPush(idx) => write!(f, "{:<15} idx: {idx}", "get.field.push"),
            Instr::HasTag(tag) => write!(f, "{:<15} tag: {tag}", "has.tag"),
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
            Instr::PopN(n) => write!(f, "{:<15} {n}", "pop.n"),
            Instr::Slide(n) => write!(f, "{:<15} {n}", "slide"),
        }
    }
}
