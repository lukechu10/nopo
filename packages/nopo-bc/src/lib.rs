//! Definition for nopo bytecode.

pub struct FnDef {
    pub ident: String,
    pub blocks: Vec<BasicBlock>,
}

pub struct BasicBlock {
    pub label: String,
    pub bc: Vec<u8>,
}

/// # Bytecode instructions
pub mod instr {
    /// Register index.
    pub type Reg = u8;

    /// Instruction opcode.
    #[repr(u8)]
    pub enum Op {
        /// MOVE A B => R(A) := R(B)
        MOVE { a: Reg, b: Reg },
        /* TODO */
    }
}
