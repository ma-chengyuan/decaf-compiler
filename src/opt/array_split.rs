//! Array-splitter.
//!
//! If a local array in only indexed by constants, split it into multiple scalars

use im::HashMap;

use crate::{
    inter::{
        constant::Const,
        ir::{Address, Inst, InstRef, Method, StackSlotRef},
        types::Type,
    },
    utils,
};

use super::ssa::construct_ssa;

pub fn split_arrays(m: &mut Method) {
    let mut eligibles: HashMap<StackSlotRef, (i64, Type)> = HashMap::new();
    for (slot_ref, slot) in m.iter_slack_slots() {
        match &slot.ty {
            Type::Array { length, base } if *length <= 20 => {
                eligibles.insert(slot_ref, (*length as i64, (**base).clone()));
            }
            _ => continue,
        }
    }
    let mut accesses = HashMap::new();
    for (inst_ref, inst) in m.iter_insts() {
        match inst {
            Inst::StoreArray {
                addr: Address::Local(slot_ref),
                index,
                ..
            }
            | Inst::LoadArray {
                addr: Address::Local(slot_ref),
                index,
            } if eligibles.contains_key(slot_ref) => match m.inst(*index) {
                Inst::LoadConst(Const::Int(i)) => {
                    let length = eligibles[slot_ref].0;
                    if *i < 0 || *i >= length {
                        // Don't split if the index is out of bounds, let the
                        // assembler emit a bounds check
                        eligibles.remove(slot_ref);
                    }
                    accesses.insert(inst_ref, *i as usize);
                }
                _ => {
                    eligibles.remove(slot_ref);
                }
            },
            _ => continue,
        }
    }
    if eligibles.is_empty() {
        return;
    }
    let mut splits: HashMap<StackSlotRef, Vec<StackSlotRef>> = HashMap::new();
    for (array_ref, (length, ty)) in &eligibles {
        let name = m.stack_slot(*array_ref).name.clone();
        let mut split = vec![];
        for i in 0..*length {
            let mut new_name = utils::make_internal_ident(&format!("{}[{}]", name.inner, i));
            new_name.span = name.span.clone();
            let slot = m.next_stack_slot(ty.clone(), new_name);
            split.push(slot);
        }
        splits.insert(*array_ref, split);
    }
    for inst_ref in (0..m.n_insts()).map(InstRef) {
        let inst = m.inst_mut(inst_ref);
        match inst {
            Inst::StoreArray {
                addr: Address::Local(slot_ref),
                value,
                ..
            } if splits.contains_key(slot_ref) => {
                *inst = Inst::Store {
                    addr: Address::Local(splits[slot_ref][accesses[&inst_ref]]),
                    value: *value,
                };
            }
            Inst::LoadArray {
                addr: Address::Local(slot_ref),
                ..
            } if splits.contains_key(slot_ref) => {
                *inst = Inst::Load(Address::Local(splits[slot_ref][accesses[&inst_ref]]));
            }
            Inst::Initialize { stack_slot, value } if splits.contains_key(stack_slot) => {
                let split = &splits[stack_slot];
                match value.clone() {
                    Const::Array(elements) => {
                        let block = m.block_of_inst(inst_ref);
                        for (i, v) in elements.into_iter().enumerate() {
                            let const_ref = m.next_inst_after(block, Inst::LoadConst(v), inst_ref);
                            m.next_inst_after(
                                block,
                                Inst::Store {
                                    addr: Address::Local(split[i]),
                                    value: const_ref,
                                },
                                const_ref,
                            );
                        }
                        m.block_mut(block).insts.retain(|&i| i != inst_ref);
                    }
                    Const::Repeat(v, _) => {
                        *inst = Inst::LoadConst(*v);
                        let block = m.block_of_inst(inst_ref);
                        for s in split {
                            m.next_inst_after(
                                block,
                                Inst::Store {
                                    addr: Address::Local(*s),
                                    value: inst_ref,
                                },
                                inst_ref,
                            );
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => continue,
        }
    }
    m.remove_unreachable();
    m.remove_unused_stack_slots();
    // crate::utils::show_graphviz(&m.dump_graphviz());
    *m = construct_ssa(m);
    // crate::utils::show_graphviz(&m.dump_graphviz());
}
