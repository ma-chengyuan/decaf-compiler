use std::collections::HashMap;

use crate::{
    parse::ast::{Ident, IdentStr},
    scan::location::Span,
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

/// An opaque reference to a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockRef(usize);

/// An opaque reference to a stack slot.
/// Stack slots are used to represent local variables and function parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StackSlotRef(usize);

/// An address in memory. This is used for loads and stores.
/// We don't support pointer arithmetic, so we don't need to support arbitrary
/// addresses.
#[derive(Debug, Clone)]
pub enum Address {
    Global(IdentStr),
    Local(StackSlotRef),
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

/// Some metadata to help debugging?
#[derive(Debug, Clone)]
struct InstAnnotation {
    span: Option<Span>,   // Maybe an instruction is associated with a span?
    ident: Option<Ident>, // Maybe an instruction is associated with an identifier?
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

#[derive(Debug, Clone)]
pub struct Block {
    pub insts: Vec<InstRef>,
    pub term: Terminator,
}

#[derive(Debug, Clone)]
pub struct StackSlot {
    /// The type of data in stack slot. Needed to determine the size of the slot.
    ty: Type,
    /// The name of the stack slot. This is used for debugging purposes.
    name: Ident,
}

#[derive(Debug, Clone)]
pub struct Method {
    pub name: Ident,
    blocks: Vec<Block>,
    insts: Vec<Inst>,
    stack_slots: Vec<StackSlot>,
    annotations: HashMap<InstRef, InstAnnotation>,

    pub return_ty: Type,
    pub params: Vec<(Ident, Type)>,
}

impl Method {
    pub fn new(name: Ident, return_ty: Type, params: Vec<(Ident, Type)>) -> Self {
        Self {
            name,
            blocks: Vec::new(),
            insts: Vec::new(),
            stack_slots: Vec::new(),
            annotations: HashMap::new(),
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
}

pub struct GlobalVar {
    name: Ident,
    ty: Type,
}

#[derive(Debug, Clone)]
pub struct Program {
    imports: HashMap<String, Ident>,
    methods: HashMap<String, Method>,
}
