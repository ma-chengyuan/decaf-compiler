use std::fmt::Display;

use crate::inter::ir::Program;

pub struct Assembler {}

impl Assembler {
    pub fn new(program: Program) -> Self {
        Self {}
    }

    pub fn assemble() -> AssemblyOutput {
        AssemblyOutput { code: vec![] }
    }
}

pub struct AssemblyOutput {
    pub code: Vec<AssemblyInst>,
}

impl Display for AssemblyOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for inst in &self.code {
            writeln!(f, "{}", inst)?;
        }
        Ok(())
    }
}

pub enum Operand {
    Imm(i64),
    Reg(Reg),
    Mem(Mem),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Reg {
    Rax, // Volatile        (Return value)
    Rbx, // Preserved
    Rcx, // Volatile        (Parameter 4)
    Rdx, // Volatile        (Parameter 3)
    Rsi, // Volatile        (Parameter 2)
    Rdi, // Volatile        (Parameter 1)
    Rsp, // Volatile        (Stack pointer)
    Rbp, // Preserved       (Base pointer)
    R8,  // Volatile        (Parameter 5)
    R9,  // Volatile        (Parameter 6)
    R10, // Volatile
    R11, // Volatile
    R12, // Preserved
    R13, // Preserved
    R14, // Preserved
    R15, // Preserved
}

impl Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Reg::Rax => write!(f, "%rax"),
            Reg::Rbx => write!(f, "%rbx"),
            Reg::Rcx => write!(f, "%rcx"),
            Reg::Rdx => write!(f, "%rdx"),
            Reg::Rsi => write!(f, "%rsi"),
            Reg::Rdi => write!(f, "%rdi"),
            Reg::Rsp => write!(f, "%rsp"),
            Reg::Rbp => write!(f, "%rbp"),
            Reg::R8 => write!(f, "%r8"),
            Reg::R9 => write!(f, "%r9"),
            Reg::R10 => write!(f, "%r10"),
            Reg::R11 => write!(f, "%r11"),
            Reg::R12 => write!(f, "%r12"),
            Reg::R13 => write!(f, "%r13"),
            Reg::R14 => write!(f, "%r14"),
            Reg::R15 => write!(f, "%r15"),
        }
    }
}

impl Reg {
    fn get_suffix(&self) -> &str {
        return "q";
    }
}

pub struct Mem {
    base: Reg,
    offset: Reg,
    displacement: i64,
    scale: i64,
}

pub enum AssemblyInst {
    Add(Operand, Operand),
    Sub(Operand, Operand),
}

impl Display for AssemblyInst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AssemblyInst::Add(op1, op2) => write!(f, "add{} {}, {}", op2.get_suffix(), op1, op2),
            AssemblyInst::Sub(op1, op2) => write!(f, "sub{} {}, {}", op2.get_suffix(), op1, op2),
        }
    }
}
