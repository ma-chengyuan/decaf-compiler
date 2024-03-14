use core::fmt;
use std::collections::HashMap;

use crate::{
    parse::ast::{Ident, IdentStr},
    scan::location::Span,
    utils::formatting::{Table, TableRow},
};

use super::{constant::Const, types::Type};

/// An opaque reference to an SSA instruction.
/// Instructions represent primitive types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstRef(usize);

impl InstRef {
    pub const fn invalid() -> Self {
        InstRef(usize::MAX)
    }
}

impl fmt::Display for InstRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0)
    }
}

/// An opaque reference to a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockRef(usize);

impl fmt::Display for BlockRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "block_{}", self.0)
    }
}

/// An opaque reference to a stack slot.
/// Stack slots are used to represent local variables and function parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StackSlotRef(usize);

impl fmt::Display for StackSlotRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "stack:{}", self.0)
    }
}

/// An address in memory. This is used for loads and stores.
/// We don't support pointer arithmetic, so we don't need to support arbitrary
/// addresses.
#[derive(Debug, Clone)]
pub enum Address {
    Global(IdentStr),
    Local(StackSlotRef),
}

impl fmt::Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Address::Global(ident) => write!(f, "global:{}", ident),
            Address::Local(slot) => write!(f, "{}", slot),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Inst {
    /// For debugging purposes, probably corresponds to nop in x86.
    Illegal,
    /// The infamous phi node.
    Phi(HashMap<BlockRef, InstRef>),

    Add(InstRef, InstRef),
    Sub(InstRef, InstRef),
    Mul(InstRef, InstRef),
    Div(InstRef, InstRef),
    Mod(InstRef, InstRef),
    Neg(InstRef),
    Not(InstRef),

    // Comparison
    Eq(InstRef, InstRef),
    // Neq can technically be expressed in terms of Eq and Not, but it's more
    // efficient to have it as a separate instruction.
    Neq(InstRef, InstRef),
    Less(InstRef, InstRef),
    LessEq(InstRef, InstRef),
    // No need for Greater and GreaterEq, as they can be expressed in terms of
    // Less and LessEq.

    // Memory operations
    /// Load a constant value (primitive type only!)
    LoadConst(Const),

    // Loads and stores are designed to not take arbitrary addresses, because
    // Decaf does not support pointer arithmetic. This is a design decision to
    // simplify the language and the compiler.
    /// Load a variable from memory. Used for primitive types only for most cases.
    /// For array: loads the base address of the array (should only be used in external calls).
    Load(Address),
    /// Store a variable to memory.
    Store {
        addr: Address,
        value: InstRef,
    },
    // Loads and stores to arrays use separate instructions from loads and
    // stores, because they need to take an index and need to be bounds-checked.
    // No need to take in the element size, because that can be resolved by
    // looking up Address in the symbol table.
    /// Load an element from an array.
    LoadArray {
        addr: Address,
        index: InstRef, // Future extension: support multi-dimensional arrays.
    },
    /// Store an element to an array.
    StoreArray {
        addr: Address,
        index: InstRef,
        value: InstRef,
    },
    /// Initialize a stack slot with a value.
    Initialize {
        stack_slot: StackSlotRef,
        value: Const,
    },
    /// Call a method.
    Call {
        method: IdentStr,
        args: Vec<InstRef>,
    },
    /// Loads a string literal from the data section, only used in external calls.
    LoadStringLiteral(String),
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Inst::Illegal => write!(f, "illegal"),
            Inst::Phi(map) => {
                write!(f, "phi {{")?;
                for (block, inst) in map {
                    write!(f, " {} -> {},", block, inst)?;
                }
                write!(f, " }}")
            }
            Inst::Add(lhs, rhs) => write!(f, "add {}, {}", lhs, rhs),
            Inst::Sub(lhs, rhs) => write!(f, "sub {}, {}", lhs, rhs),
            Inst::Mul(lhs, rhs) => write!(f, "mul {}, {}", lhs, rhs),
            Inst::Div(lhs, rhs) => write!(f, "div {}, {}", lhs, rhs),
            Inst::Mod(lhs, rhs) => write!(f, "mod {}, {}", lhs, rhs),
            Inst::Neg(operand) => write!(f, "neg {}", operand),
            Inst::Not(operand) => write!(f, "not {}", operand),
            Inst::Eq(lhs, rhs) => write!(f, "eq {}, {}", lhs, rhs),
            Inst::Neq(lhs, rhs) => write!(f, "neq {}, {}", lhs, rhs),
            Inst::Less(lhs, rhs) => write!(f, "less {}, {}", lhs, rhs),
            Inst::LessEq(lhs, rhs) => write!(f, "less_eq {}, {}", lhs, rhs),
            Inst::LoadConst(c) => write!(f, "load_const {}", c),
            Inst::Load(addr) => write!(f, "load {}", addr),
            Inst::Store { addr, value } => write!(f, "store {} {}", addr, value),
            Inst::LoadArray { addr, index } => write!(f, "load_array {}[{}]", addr, index),
            Inst::StoreArray { addr, index, value } => {
                write!(f, "store_array {}[{}] {}", addr, index, value)
            }
            Inst::Initialize { stack_slot, value } => {
                write!(f, "initialize {} {}", stack_slot, value)
            }
            Inst::Call { method, args } => {
                write!(f, "call {}(", method)?;
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            Inst::LoadStringLiteral(lit) => write!(f, "load_string_literal {:?}", lit),
        }
    }
}

/// Some metadata to help debugging?
#[derive(Debug, Clone, Default)]
pub struct Annotation {
    pub str: Option<String>,
    pub span: Option<Span>, // Maybe an instruction is associated with a span?
    pub ident: Option<Ident>, // Maybe an instruction is associated with an identifier?
}

impl fmt::Display for Annotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(str) = &self.str {
            write!(f, "{} ", str)?;
        }
        if let Some(span) = &self.span {
            write!(f, "{:?} ", span.source_str())?;
        }
        if let Some(ident) = &self.ident {
            write!(f, "{:?} ", ident.inner)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Return(Option<InstRef>),
    Jump(BlockRef),
    CondJump {
        cond: InstRef,
        true_: BlockRef,
        false_: BlockRef,
    },
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Return(None) => write!(f, "return"),
            Terminator::Return(Some(inst)) => write!(f, "return {}", inst),
            Terminator::Jump(block) => write!(f, "jump {}", block),
            Terminator::CondJump {
                cond,
                true_,
                false_,
            } => write!(f, "cond_jump {} {} {}", cond, true_, false_),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub insts: Vec<InstRef>,
    pub term: Terminator,
}

#[derive(Debug, Clone)]
pub struct StackSlot {
    /// The type of data in stack slot. Needed to determine the size of the slot.
    pub ty: Type,
    /// The name of the stack slot. This is used for debugging purposes.
    pub name: Ident,
}

#[derive(Debug, Clone)]
pub struct Method {
    pub name: Ident,
    blocks: Vec<Block>,
    insts: Vec<Inst>,
    stack_slots: Vec<StackSlot>,

    inst_annotations: HashMap<InstRef, Annotation>,
    block_annotations: HashMap<BlockRef, Annotation>,

    pub entry: BlockRef,
    pub return_ty: Type,
    pub params: Vec<(Ident, Type)>,
}

impl Method {
    pub fn new(name: Ident, return_ty: Type, params: Vec<(Ident, Type)>) -> Self {
        let entry = BlockRef(0);
        Self {
            name,
            blocks: vec![Block {
                insts: Vec::new(),
                term: Terminator::Return(None),
            }],
            insts: Vec::new(),
            stack_slots: Vec::new(),
            inst_annotations: HashMap::new(),
            block_annotations: HashMap::new(),
            entry,
            return_ty,
            params,
        }
    }

    pub fn next_block(&mut self) -> BlockRef {
        let block_ref = BlockRef(self.blocks.len());
        self.blocks.push(Block {
            insts: Vec::new(),
            term: Terminator::Return(None),
        });
        block_ref
    }

    pub fn block(&self, block_ref: BlockRef) -> &Block {
        &self.blocks[block_ref.0]
    }

    pub fn block_mut(&mut self, block_ref: BlockRef) -> &mut Block {
        &mut self.blocks[block_ref.0]
    }

    pub fn next_inst(&mut self, block: BlockRef, inst: Inst) -> InstRef {
        let inst_ref = InstRef(self.insts.len());
        self.insts.push(inst);
        self.block_mut(block).insts.push(inst_ref);
        inst_ref
    }

    pub fn inst(&self, inst_ref: InstRef) -> &Inst {
        &self.insts[inst_ref.0]
    }

    pub fn inst_mut(&mut self, inst_ref: InstRef) -> &mut Inst {
        &mut self.insts[inst_ref.0]
    }

    pub fn annotate_inst_mut(&mut self, inst_ref: InstRef) -> &mut Annotation {
        self.inst_annotations.entry(inst_ref).or_default()
    }

    pub fn get_inst_annotation(&self, inst_ref: &InstRef) -> Option<&Annotation> {
        self.inst_annotations.get(inst_ref)
    }

    pub fn annotate_block_mut(&mut self, block_ref: BlockRef) -> &mut Annotation {
        self.block_annotations.entry(block_ref).or_default()
    }

    pub fn get_block_annotation(&self, block_ref: &BlockRef) -> Option<&Annotation> {
        self.block_annotations.get(block_ref)
    }

    pub fn next_stack_slot(&mut self, ty: Type, name: Ident) -> StackSlotRef {
        let slot_ref = StackSlotRef(self.stack_slots.len());
        self.stack_slots.push(StackSlot { ty, name });
        slot_ref
    }

    pub fn stack_slot(&self, slot_ref: StackSlotRef) -> &StackSlot {
        &self.stack_slots[slot_ref.0]
    }

    pub fn block_of_inst(&self, inst_ref: InstRef) -> BlockRef {
        // This is inefficient, but it's not a big deal. Hopefully we won't need
        // this function often.
        for (block_ref, block) in self.blocks.iter().enumerate() {
            if block.insts.contains(&inst_ref) {
                return BlockRef(block_ref);
            }
        }
        panic!("instruction not found in any block");
    }

    pub fn iter_slack_slots(&self) -> SlackSlotIter {
        SlackSlotIter {
            method: self,
            iter: self.stack_slots.iter().enumerate(),
        }
    }

    pub fn iter_insts(&self) -> InstIter {
        InstIter {
            method: self,
            iter: self.insts.iter().enumerate(),
        }
    }

    pub fn iter_blocks(&self) -> BlockIter {
        BlockIter {
            method: self,
            iter: self.blocks.iter().enumerate(),
        }
    }
}

pub struct SlackSlotIter<'a> {
    method: &'a Method,
    iter: std::iter::Enumerate<std::slice::Iter<'a, StackSlot>>,
}

impl<'a> Iterator for SlackSlotIter<'a> {
    type Item = (StackSlotRef, &'a StackSlot);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, slot)| (StackSlotRef(i), slot))
    }
}

pub struct InstIter<'a> {
    method: &'a Method,
    iter: std::iter::Enumerate<std::slice::Iter<'a, Inst>>,
}

impl<'a> Iterator for InstIter<'a> {
    type Item = (InstRef, &'a Inst);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, inst)| (InstRef(i), inst))
    }
}

pub struct BlockIter<'a> {
    method: &'a Method,
    iter: std::iter::Enumerate<std::slice::Iter<'a, Block>>,
}

impl<'a> Iterator for BlockIter<'a> {
    type Item = (BlockRef, &'a Block);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, block)| (BlockRef(i), block))
    }
}

const INDENT: &str = "   ";

impl fmt::Display for Method {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}(", self.return_ty, self.name.inner)?;
        for (i, (name, ty)) in self.params.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} {}", ty, name.inner)?;
        }
        writeln!(f, ") {{")?;
        writeln!(f, "stack:")?;
        let mut stack_slots = Table::new();
        for (i, stack_slot) in self.stack_slots.iter().enumerate() {
            stack_slots.add_row(
                TableRow::new()
                    .add(INDENT)
                    .add(StackSlotRef(i))
                    .add(&stack_slot.ty)
                    .add(&stack_slot.name.inner),
            );
        }
        write!(f, "{}", stack_slots)?;
        for (i, block) in self.blocks.iter().enumerate() {
            write!(f, "{}:", BlockRef(i))?;
            if let Some(annotation) = self.block_annotations.get(&BlockRef(i)) {
                write!(f, " ; {}", annotation)?;
            }
            writeln!(f)?;
            let mut insts = Table::new();
            for inst in &block.insts {
                if *inst == InstRef::invalid() {
                    continue;
                }
                let mut row = TableRow::new()
                    .add(INDENT)
                    .add(inst)
                    .add('=')
                    .add(self.inst(*inst));
                if let Some(annotation) = self.inst_annotations.get(inst) {
                    row = row.add(format!("; {}", annotation));
                }
                insts.add_row(row);
            }
            write!(f, "{}", insts)?;
            writeln!(f, "{} {}", INDENT, block.term)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone)]
pub struct GlobalVar {
    pub name: Ident,
    pub ty: Type,
    pub init: Const,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub imports: HashMap<String, Ident>,
    pub methods: HashMap<String, Method>,
    pub globals: HashMap<String, GlobalVar>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "imports:")?;
        for import in self.imports.keys() {
            writeln!(f, "{} {}", INDENT, import)?;
        }
        writeln!(f, "globals:")?;
        let mut globals = Table::new();
        for global in self.globals.values() {
            globals.add_row(
                TableRow::new()
                    .add(INDENT)
                    .add(&global.name.inner)
                    .add(&global.ty)
                    .add('=')
                    .add(&global.init),
            );
        }
        write!(f, "{}", globals)?;
        for method in self.methods.values() {
            writeln!(f, "{}", method)?;
        }
        Ok(())
    }
}
