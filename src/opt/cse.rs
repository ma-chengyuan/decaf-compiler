use std::collections::HashMap;

use crate::{
    inter::ir::{BlockRef, Inst, InstRef, Method},
    opt::copy_prop::propagate_copies,
};

use super::dom::compute_dominance;

pub fn eliminate_common_subexpressions(method: &mut Method) {
    let dom = compute_dominance(method);
    let dom_tree = dom.dominator_tree();

    fn dfs(
        method: &mut Method,
        dom_tree: &[Vec<BlockRef>],
        block: BlockRef,
        canonical_forms: &mut [Option<String>],
        available_exprs: &mut Vec<HashMap<String, InstRef>>,
    ) {
        for inst in method.block(block).insts.clone() {
            let canonical_form = match method.inst(inst) {
                op @ (Inst::Add(lhs, rhs)
                | Inst::Sub(lhs, rhs)
                | Inst::Mul(lhs, rhs)
                | Inst::Div(lhs, rhs)
                | Inst::Mod(lhs, rhs)
                | Inst::Eq(lhs, rhs)
                | Inst::Neq(lhs, rhs)
                | Inst::Less(lhs, rhs)
                | Inst::LessEq(lhs, rhs)) => {
                    let mut lhs = canonical_forms[lhs.0]
                        .as_ref()
                        .expect("lhs used before defined");
                    let mut rhs = canonical_forms[rhs.0]
                        .as_ref()
                        .expect("rhs used before defined");
                    let (op_str, commutative) = match op {
                        Inst::Add(..) => ("+", true),
                        Inst::Sub(..) => ("-", false),
                        Inst::Mul(..) => ("*", true),
                        Inst::Div(..) => ("/", false),
                        Inst::Mod(..) => ("%", false),
                        Inst::Eq(..) => ("==", true),
                        Inst::Neq(..) => ("!=", true),
                        Inst::Less(..) => ("<", false),
                        Inst::LessEq(..) => ("<=", false),
                        _ => unreachable!(),
                    };
                    if commutative && lhs > rhs {
                        std::mem::swap(&mut lhs, &mut rhs);
                    }
                    format!("({} {} {})", op_str, lhs, rhs)
                }
                op @ (Inst::Neg(operand) | Inst::Not(operand)) => {
                    let operand = canonical_forms[operand.0]
                        .as_ref()
                        .expect("operand used before defined");
                    let op_str = match op {
                        Inst::Neg(..) => "-",
                        Inst::Not(..) => "!",
                        _ => unreachable!(),
                    };
                    format!("({} {})", op_str, operand)
                }
                Inst::Copy(src) => canonical_forms[src.0]
                    .as_ref()
                    .expect("src used before defined")
                    .clone(),
                Inst::LoadConst(c) => format!("{}", c),
                Inst::LoadStringLiteral(lit) => format!("{:?}", lit),
                _ => format!("{}", inst),
            };
            canonical_forms[inst.0] = Some(canonical_form.clone());

            let mut eliminated = false;
            for map in available_exprs.iter().rev() {
                if let Some(&prev_inst) = map.get(&canonical_form) {
                    *method.inst_mut(inst) = Inst::Copy(prev_inst);
                    eliminated = true;
                    break;
                }
            }
            if !eliminated {
                available_exprs
                    .last_mut()
                    .unwrap()
                    .insert(canonical_form, inst);
            }
        }
        for child in dom_tree[block.0].iter() {
            available_exprs.push(HashMap::new());
            dfs(method, dom_tree, *child, canonical_forms, available_exprs);
            available_exprs.pop();
        }
    }

    let mut canonical_forms = vec![None; method.n_insts()];
    let mut available_exprs = vec![HashMap::new()];
    dfs(
        method,
        &dom_tree,
        method.entry,
        &mut canonical_forms,
        &mut available_exprs,
    );
    // Do copy propagation after CSE to eliminate redundant copies.
    propagate_copies(method);
}
