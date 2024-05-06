use im::HashMap;

use crate::{
    inter::{
        ir::{Address, BlockRef, Inst, InstRef, Method, Program, StackSlotRef, Terminator},
        types::Type,
    },
    parse::ast::Ident,
};

fn can_inline(method: &Method) -> bool {
    const MAX_INSTRUCTION_CT: usize = 25;
    // don't allow too many instructions
    if method.n_insts() > MAX_INSTRUCTION_CT {
        return false;
    }
    // don't allow recurisve calls
    // for (_, inst) in method.iter_insts() {
    //     if let Inst::Call {
    //         method: method_name,
    //         ..
    //     } = inst
    //     {
    //         if method_name.as_ref() == method.name.inner.as_ref() {
    //             return false;
    //         }
    //     }
    // }
    // don't allow functions that occasionally do not return a value
    if method.return_ty != Type::Void {
        for (_, block) in method.iter_blocks() {
            if let Terminator::Return(ret_val) = block.term {
                if ret_val.is_none() {
                    return false;
                }
            }
        }
    }
    true
}

pub fn inline_functions(program: &mut Program) {
    let mut functions_to_inline = HashMap::new();
    for (method_name, method) in program.methods.iter() {
        if method_name == "main" {
            continue;
        }
        if can_inline(method) {
            functions_to_inline.insert(method_name.clone(), method.clone());
        }
    }

    for method in program.methods.values_mut() {
        let n_blocks = method.n_blocks(); // don't inline more than once
        for block_ref in 0..n_blocks {
            let block_ref = BlockRef(block_ref);

            for inst_ref in method.block(block_ref).insts.clone().into_iter() {
                let inst = method.inst(inst_ref).clone();
                let Inst::Call {
                    method: method_name,
                    args: method_args,
                } = inst
                else {
                    continue;
                };

                if let Some(method_to_copy) = functions_to_inline.get(method_name.as_ref()) {
                    // inline this function
                    let return_stack_slot_ref = if method_to_copy.return_ty != Type::Void {
                        Some(method.next_stack_slot(
                            method_to_copy.return_ty.clone(),
                            Ident {
                                span: method.span.clone(),  // random span for now
                                inner: method_name.clone(), // for now name the return variable the same as the function being called
                            },
                        ))
                    } else {
                        None
                    };

                    let function_entry_block_ref = block_ref;
                    let function_exit_block_ref = method.next_block();

                    let mut new_inst_refs = vec![InstRef(usize::MAX); method_to_copy.n_insts()];
                    let mut new_block_refs = vec![BlockRef(usize::MAX); method_to_copy.n_blocks()];
                    let mut new_stack_slot_refs =
                        vec![StackSlotRef(usize::MAX); method_to_copy.n_stack_slots()];

                    // copy over blocks and instructions
                    for (to_copy_block_ref, to_copy_block) in method_to_copy.iter_blocks() {
                        let target_block_ref = method.next_block();
                        new_block_refs[to_copy_block_ref.0] = target_block_ref;
                        for &to_copy_inst_ref in to_copy_block.insts.iter() {
                            let new_inst = method_to_copy.inst(to_copy_inst_ref).clone();
                            let new_inst_ref = method.next_inst(target_block_ref, new_inst);
                            new_inst_refs[to_copy_inst_ref.0] = new_inst_ref;
                        }
                        method.block_mut(target_block_ref).term = to_copy_block.term.clone();
                    }

                    // copy over stack slots
                    for stack_slot_ref in (0..method_to_copy.n_stack_slots()).map(StackSlotRef) {
                        let stack_slot = method_to_copy.stack_slot(stack_slot_ref);
                        new_stack_slot_refs[stack_slot_ref.0] =
                            method.next_stack_slot(stack_slot.ty.clone(), stack_slot.name.clone());
                    }

                    // update all instructions
                    for &new_inst_ref in new_inst_refs.iter() {
                        if new_inst_ref.0 != usize::MAX {
                            let mut new_inst = method.inst_mut(new_inst_ref);
                            new_inst.for_each_inst_ref(|inst_ref| {
                                *inst_ref = new_inst_refs[inst_ref.0]
                            });
                            new_inst.for_each_stack_slot_ref(|stack_slot_ref| {
                                *stack_slot_ref = new_stack_slot_refs[stack_slot_ref.0]
                            });
                            if let Inst::Phi(map) = &mut new_inst {
                                *map = std::mem::take(map)
                                    .into_iter()
                                    .map(|(block, inst)| (new_block_refs[block.0], inst))
                                    .collect();
                            }
                        }
                    }

                    // update all block terminators
                    for &new_block_ref in new_block_refs.iter() {
                        if new_block_ref.0 != usize::MAX {
                            let current_term = method.block(new_block_ref).term.clone();
                            method.block_mut(new_block_ref).term = match current_term {
                                Terminator::Return(return_inst_ref) => {
                                    if let Some(return_inst_ref) = return_inst_ref {
                                        method.next_inst(
                                            new_block_ref,
                                            Inst::Store {
                                                addr: Address::Local(
                                                    return_stack_slot_ref.unwrap(),
                                                ),
                                                value: new_inst_refs[return_inst_ref.0],
                                            },
                                        );
                                    }
                                    Terminator::Jump(function_exit_block_ref)
                                }
                                Terminator::Jump(old_block_ref) => {
                                    Terminator::Jump(new_block_refs[old_block_ref.0])
                                }
                                Terminator::CondJump {
                                    cond,
                                    true_,
                                    false_,
                                } => Terminator::CondJump {
                                    cond: new_inst_refs[cond.0],
                                    true_: new_block_refs[true_.0],
                                    false_: new_block_refs[false_.0],
                                },
                            }
                        }
                    }

                    // todo: consider copying inst and block annotations

                    // move everything after the call() statement into a new block
                    let call_inst_pos = method
                        .block(function_entry_block_ref)
                        .insts
                        .iter()
                        .position(|&inst| inst == inst_ref)
                        .unwrap();
                    let remaining_instructions =
                        method.block_mut(block_ref).insts.split_off(call_inst_pos);

                    method.block_mut(function_exit_block_ref).insts = remaining_instructions;
                    method.block_mut(function_exit_block_ref).term =
                        method.block_mut(function_entry_block_ref).term.clone();
                    method.block_mut(function_entry_block_ref).term =
                        Terminator::Jump(new_block_refs[method_to_copy.entry.0]);

                    // either replace call() with Load() from the return stack slot, or remove the call() instruction
                    if let Some(stack_slot_ref) = return_stack_slot_ref {
                        *method.inst_mut(inst_ref) = Inst::Load(Address::Local(stack_slot_ref));
                    } else {
                        // remove the call() instruction
                        method.block_mut(function_exit_block_ref).insts.remove(0);
                    }

                    // handle arguments: every argument must be moved to the stack slot
                    for (arg_idx, &method_arg) in method_args.iter().enumerate() {
                        method.next_inst(
                            function_entry_block_ref,
                            Inst::Store {
                                addr: Address::Local(new_stack_slot_refs[arg_idx]),
                                value: method_arg,
                            },
                        );
                    }

                    // update all phi instructions referencing the entry block to now reference the exit block
                    for (_, mut inst) in method.iter_insts_mut() {
                        if let Inst::Phi(map) = &mut inst {
                            *map = std::mem::take(map)
                                .into_iter()
                                .map(|(block, inst)| {
                                    (
                                        if block == function_entry_block_ref {
                                            function_exit_block_ref
                                        } else {
                                            block
                                        },
                                        inst,
                                    )
                                })
                                .collect();
                        }
                    }

                    break;
                }
            }
        }

        method.remove_unreachable();
        method.merge_blocks();
    }
}
