use crate::{
    inter::{
        constant::Const,
        ir::{BlockRef, Inst, InstRef, Method, Terminator},
    },
    opt::dom::compute_dominance,
};
use std::{
    collections::{HashMap, HashSet, LinkedList},
    hash::Hash,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Value(pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression {
    Add(Value, Value),
    Sub(Value, Value),
    Mul(Value, Value),
    Div(Value, Value),
    Mod(Value, Value),
    Neg(Value),
    Not(Value),
    Copy(Value),
    LoadConst(Const),

    Eq(Value, Value),
    Neq(Value, Value),
    Less(Value, Value),
    LessEq(Value, Value),

    Reg(InstRef),
    Phi(HashMap<BlockRef, InstRef>),
}

impl Expression {
    fn depends_on(&self) -> Vec<Value> {
        match self {
            Expression::Add(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Sub(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Mul(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Div(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Mod(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Neg(operand) => vec![operand.clone()],
            Expression::Not(operand) => vec![operand.clone()],
            Expression::Copy(src) => vec![src.clone()],
            Expression::LoadConst(_) => vec![],
            Expression::Eq(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Neq(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Less(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::LessEq(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Expression::Reg(_) => vec![],
            Expression::Phi(_) => vec![],
        }
    }

    fn is_simple(&self) -> bool {
        match self {
            Expression::Add(..) => false,
            Expression::Sub(..) => false,
            Expression::Mul(..) => false,
            Expression::Div(..) => false,
            Expression::Mod(..) => false,
            Expression::Neg(..) => false,
            Expression::Not(..) => false,
            Expression::Copy(..) => false,
            Expression::LoadConst(_) => false,
            Expression::Eq(..) => false,
            Expression::Neq(..) => false,
            Expression::Less(..) => false,
            Expression::LessEq(..) => false,
            Expression::Reg(_) => true,
            Expression::Phi(_) => false,
        }
    }
}

impl Expression {
    fn new_add(lhs: Value, rhs: Value) -> Self {
        Expression::Add(
            std::cmp::min(lhs.clone(), rhs.clone()),
            std::cmp::max(lhs.clone(), rhs.clone()),
        )
    }
    fn new_sub(lhs: Value, rhs: Value) -> Self {
        Expression::Sub(lhs, rhs)
    }
    fn new_mul(lhs: Value, rhs: Value) -> Self {
        Expression::Mul(
            std::cmp::min(lhs.clone(), rhs.clone()),
            std::cmp::max(lhs.clone(), rhs.clone()),
        )
    }
    fn new_div(lhs: Value, rhs: Value) -> Self {
        Expression::Div(lhs, rhs)
    }
    fn new_mod(lhs: Value, rhs: Value) -> Self {
        Expression::Mod(lhs, rhs)
    }
    fn new_neg(value: Value) -> Self {
        Expression::Neg(value)
    }
    fn new_not(value: Value) -> Self {
        Expression::Not(value)
    }
    fn new_copy(value: Value) -> Self {
        Expression::Copy(value)
    }
    fn new_load_const(value: Const) -> Self {
        Expression::LoadConst(value)
    }
    fn new_eq(lhs: Value, rhs: Value) -> Self {
        Expression::Eq(
            std::cmp::min(lhs.clone(), rhs.clone()),
            std::cmp::max(lhs.clone(), rhs.clone()),
        )
    }
    fn new_neq(lhs: Value, rhs: Value) -> Self {
        Expression::Neq(
            std::cmp::min(lhs.clone(), rhs.clone()),
            std::cmp::max(lhs.clone(), rhs.clone()),
        )
    }
    fn new_less(lhs: Value, rhs: Value) -> Self {
        Expression::Less(lhs, rhs)
    }
    fn new_lesseq(lhs: Value, rhs: Value) -> Self {
        Expression::LessEq(lhs, rhs)
    }
    fn new_reg(value: InstRef) -> Self {
        Expression::Reg(value)
    }
    fn new_phi(value: HashMap<BlockRef, InstRef>) -> Self {
        Expression::Phi(value)
    }
}

// Can make value table arbitrarily intelligent, but for now this is good enough
#[derive(Clone, Debug)]
pub struct ValueTable {
    values: LinkedList<(Expression, Value)>,
    _next_value: usize,
    map: HashMap<InstRef, Value>,
}
impl ValueTable {
    pub fn new() -> Self {
        Self {
            values: LinkedList::new(),
            _next_value: 0,
            map: HashMap::new(),
        }
    }

    pub fn next_value(&mut self) -> Value {
        let ans = Value(self._next_value);
        self._next_value += 1;
        ans
    }

    pub fn insert(&mut self, inst: InstRef, value: Expression) -> (Value, bool) {
        let (value_index, inserted) = self.lookup_expr(&value);
        self.map.insert(inst, value_index.clone());
        (value_index, inserted)
    }

    pub fn lookup_inst(&self, inst: &InstRef) -> Value {
        // Must exist, otherwise panic!
        self.map.get(inst).unwrap().clone()
    }

    pub fn lookup_inst_create(&mut self, inst: &InstRef) -> (Value, bool) {
        if let Some(value) = self.map.get(inst) {
            return (value.clone(), false);
        }
        let ans = self.next_value();
        self.map.insert(*inst, ans.clone());
        (ans, true)
    }

    pub fn expr_eq(&self, lhs: &Expression, rhs: &Expression) -> bool {
        lhs == rhs
    }

    pub fn lookup_expr(&mut self, expr: &Expression) -> (Value, bool) {
        if let Expression::Copy(src) = expr {
            debug_assert!(src.0 < self._next_value);
            return (src.clone(), false);
        }
        if let Expression::Reg(inst) = expr {
            return self.lookup_inst_create(inst);
        }
        match self
            .values
            .iter()
            .find_map(|(k, v)| if self.expr_eq(k, expr) { Some(v) } else { None })
        {
            Some(index) => (index.clone(), false),
            None => {
                let ans = self.next_value();
                self.values.push_back((expr.clone(), ans.clone()));
                (ans, true)
            }
        }
    }

    pub fn maybe_insert_inst(
        &mut self,
        inst: InstRef,
        inst_value: &Inst,
    ) -> (Value, Expression, bool) {
        let mut okay = true;
        let expr = match inst_value {
            Inst::Add(lhs, rhs) => {
                Expression::new_add(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::Sub(lhs, rhs) => {
                Expression::new_sub(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::Mul(lhs, rhs) => {
                Expression::new_mul(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::Div(lhs, rhs) => {
                Expression::new_div(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::Mod(lhs, rhs) => {
                Expression::new_mod(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::Neg(operand) => Expression::new_neg(self.lookup_inst(operand)),
            Inst::Not(operand) => Expression::new_not(self.lookup_inst(operand)),
            Inst::Copy(src) => Expression::new_copy(self.lookup_inst(src)),
            Inst::LoadConst(value) => Expression::new_load_const(value.clone()),
            Inst::Eq(lhs, rhs) => Expression::new_eq(self.lookup_inst(lhs), self.lookup_inst(rhs)),
            Inst::Neq(lhs, rhs) => {
                Expression::new_neq(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::Less(lhs, rhs) => {
                Expression::new_less(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::LessEq(lhs, rhs) => {
                Expression::new_lesseq(self.lookup_inst(lhs), self.lookup_inst(rhs))
            }
            Inst::Phi(values) => Expression::new_phi(values.clone()),
            _ => {
                // not considered in optimization
                okay = false;
                Expression::new_reg(inst)
            }
        };
        let (value, _) = self.insert(inst, expr.clone());
        (value, expr, okay)
    }

    // pub fn get_value(&self, inst: InstRef) -> Option<&Value> {
    //     self.map.get(&inst)
    // }

    pub fn tie_expr(&mut self, expr: Expression, value: Value) {
        if let Some(index) = self.values.iter().find_map(|(k, v)| {
            if self.expr_eq(k, &expr) {
                Some(v)
            } else {
                None
            }
        }) {
            assert!(*index == value);
        } else {
            self.values.push_back((expr.clone(), value.clone()));
        }
    }

    pub fn tie_inst(&mut self, inst: InstRef, value: Value) {
        if let Some(val) = self.map.get(&inst) {
            assert!(*val == value);
        } else {
            self.map.insert(inst, value);
        }
    }
}

type LeaderSet = Vec<HashMap<Value, InstRef>>;
type AntileaderSet = Vec<LinkedList<(Value, Expression)>>;
type PhiGen = Vec<HashMap<Value, InstRef>>;

#[allow(clippy::too_many_arguments)]
pub fn build_sets_phase1(
    method: &mut Method,
    current_block: BlockRef,
    dom_tree: &[Vec<BlockRef>],
    exp_gen: &mut [LinkedList<(Value, Expression)>],
    phi_gen: &mut [HashMap<Value, InstRef>],
    tmp_gen: &mut [HashSet<InstRef>],
    leaders: &mut [HashMap<Value, InstRef>],
    value_table: &mut ValueTable,
) {
    // Do logic stuff
    let mut added_vals = HashSet::new();
    for inst in method.block(current_block).insts.clone() {
        let (value, expr, okay) = value_table.maybe_insert_inst(inst, method.inst(inst));
        if okay {
            leaders[current_block.0]
                .entry(value.clone())
                .or_insert(inst);
            if let Expression::Phi(_) = expr {
                phi_gen[current_block.0]
                    .entry(value.clone())
                    .or_insert(inst);
            }
        } else {
            if let Expression::Reg(iref) = expr {
                leaders[current_block.0]
                    .entry(value.clone())
                    .or_insert(iref);
            }
            tmp_gen[current_block.0].insert(inst);
        }
        if let Expression::Phi(_) = expr {
            // Phi: change to Reg
            if added_vals.insert(value.clone()) {
                exp_gen[current_block.0].push_back((value.clone(), Expression::Reg(inst)));
            }
        } else {
            // Handle non-Phi expressions
            if added_vals.insert(value.clone()) {
                exp_gen[current_block.0].push_back((value.clone(), expr.clone()));
            }
        }
    }
    // Recurse
    for child in dom_tree[current_block.0].iter() {
        leaders[child.0] = leaders[current_block.0].clone();
        build_sets_phase1(
            method,
            *child,
            dom_tree,
            exp_gen,
            phi_gen,
            tmp_gen,
            leaders,
            value_table,
        );
    }
}

fn phi_translate(
    method: &Method,
    block: BlockRef,
    phi_gen: &HashMap<Value, InstRef>,
    values_to_translate: &LinkedList<(Value, Expression)>,
    value_table: &mut ValueTable,
) -> LinkedList<(Value, Expression)> {
    let mut result = LinkedList::new();
    let mut translated: HashMap<Value, Value> = HashMap::new();
    for (value, expr) in values_to_translate.iter() {
        if let Some(phi_val) = phi_gen.get(value) {
            let phi_inst = method.inst(*phi_val);
            let Inst::Phi(phi) = phi_inst else {
                unreachable!()
            };

            let above_inst = phi[&block];
            let translated_val = value_table.lookup_inst(&above_inst);
            // let (translated_val, _) = value_table.lookup_expr(&Expression::Reg(above_inst));
            translated.insert(value.clone(), translated_val.clone());
            result.push_back((translated_val, Expression::Reg(above_inst)));
        } else {
            macro_rules! try_trans {
                ($t:path, $($x:expr), +) => {
                    $t($(if let Some(new) = translated.get($x) { new.clone() } else { $x.clone() }), +)
                }
            }
            // If it's from a Phi, it will necessarily be in translated map. Otherwise, it must have existed before as well.
            let new_expr = match expr {
                Expression::Add(lhs, rhs) => try_trans!(Expression::new_add, lhs, rhs),
                Expression::Sub(lhs, rhs) => try_trans!(Expression::new_sub, lhs, rhs),
                Expression::Mul(lhs, rhs) => try_trans!(Expression::new_mul, lhs, rhs),
                Expression::Div(lhs, rhs) => try_trans!(Expression::new_div, lhs, rhs),
                Expression::Mod(lhs, rhs) => try_trans!(Expression::new_mod, lhs, rhs),
                Expression::Neg(operand) => try_trans!(Expression::new_neg, operand),
                Expression::Not(operand) => try_trans!(Expression::new_not, operand),
                Expression::Copy(src) => try_trans!(Expression::new_copy, src),
                Expression::Eq(lhs, rhs) => try_trans!(Expression::new_eq, lhs, rhs),
                Expression::Neq(lhs, rhs) => try_trans!(Expression::new_neq, lhs, rhs),
                Expression::Less(lhs, rhs) => try_trans!(Expression::new_less, lhs, rhs),
                Expression::LessEq(lhs, rhs) => try_trans!(Expression::new_lesseq, lhs, rhs),
                Expression::Phi(_) => continue, // I have no idea why we continue. Shouldn't it be unreachable?
                e => e.clone(),
            };
            let (new_val, _) = value_table.lookup_expr(&new_expr);
            translated.insert(value.clone(), new_val.clone());
            result.push_back((new_val, new_expr));
        }
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn build_sets_phase2(
    method: &Method,
    block: BlockRef,
    succs: &[Vec<BlockRef>],
    exp_gen: &[LinkedList<(Value, Expression)>],
    phi_gen: &[HashMap<Value, InstRef>],
    tmp_gen: &[HashSet<InstRef>],
    antic_in: &mut AntileaderSet,
    value_table: &mut ValueTable,
) -> bool {
    let succs = &succs[block.0];
    let mut result = LinkedList::new();
    #[allow(clippy::comparison_chain)]
    if succs.len() == 1 {
        // Phi translate and propagate
        let succ = succs[0];
        result = phi_translate(
            method,
            block,
            &phi_gen[succ.0],
            &antic_in[succ.0],
            value_table,
        );
    } else if succs.len() > 1 {
        // Compute intersection of exprs. Assert no children have phi nodes.
        let mut exprs = antic_in[succs[0].0].clone();
        for succ in succs.iter().skip(1) {
            // Perform intersection one by one
            let mut hashset = HashSet::new();
            for (value, _) in antic_in[succ.0].iter() {
                hashset.insert(value);
            }

            let mut new_exprs = LinkedList::new();
            for (value, expr) in exprs.iter() {
                if hashset.contains(&value) {
                    new_exprs.push_back((value.clone(), expr.clone()));
                }
            }
            exprs = new_exprs;
        }
        result = exprs;
    }

    // Currently, result = antic_out
    let mut killed_values = HashSet::new();
    let cleaned = exp_gen[block.0]
        .iter()
        .chain(result.iter())
        .filter_map(|(value, expr)| {
            for dependency in expr.depends_on().into_iter() {
                if killed_values.contains(&dependency) {
                    // println!("Killing value: {:?} due to dependency on {:?}", value, dependency);
                    killed_values.insert(value.clone());
                    return None;
                }
            }
            if let Expression::Reg(inst) = expr {
                if tmp_gen[block.0].contains(inst) {
                    // println!("Killing value: {:?}", value);
                    killed_values.insert(value.clone());
                    return None;
                }
            }
            Some((value.clone(), expr.clone()))
        });

    let mut added = HashSet::new();
    let mut result = LinkedList::new(); // reset
    for (value, expr) in cleaned {
        if added.insert(value.clone()) {
            result.push_back((value.clone(), expr.clone()));
        }
    }

    if result == antic_in[block.0] {
        return false;
    }
    antic_in[block.0] = result;
    true
}

#[allow(clippy::type_complexity)]
fn build_sets(
    method: &mut Method,
) -> (
    Vec<Vec<BlockRef>>,
    Vec<Vec<BlockRef>>,
    LeaderSet,
    AntileaderSet,
    PhiGen,
    ValueTable,
) {
    let dom = compute_dominance(method);
    let dom_tree = dom.dominator_tree();

    let mut value_table = ValueTable::new();
    let num_blocks = method.n_blocks();

    let mut exp_gen: Vec<LinkedList<(Value, Expression)>> = vec![LinkedList::default(); num_blocks];
    let mut tmp_gen: Vec<HashSet<InstRef>> = vec![HashSet::default(); num_blocks];
    let mut phi_gen: Vec<HashMap<Value, InstRef>> = vec![HashMap::default(); num_blocks];
    let mut leaders: LeaderSet = vec![HashMap::default(); num_blocks];
    build_sets_phase1(
        method,
        method.entry,
        &dom_tree,
        &mut exp_gen,
        &mut phi_gen,
        &mut tmp_gen,
        &mut leaders,
        &mut value_table,
    );
    /*
    {
        println! {"exp_gens: \n{:?}\n", exp_gen};
        println! {"tmp_gen: \n{:?}\n", tmp_gen};
        println! {"phi_gens: \n{:?}\n", phi_gen};
        println! {"leaders: \n{:?}\n", leaders};
        println! {"value_table: \n{:?}\n", value_table};
    }
    */

    // Build sets phase 2
    // REQUIRES: NO CRITICAL EDGES

    let mut preds: Vec<Vec<BlockRef>> = vec![vec![]; num_blocks];
    let mut succs: Vec<Vec<BlockRef>> = vec![vec![]; num_blocks];
    for (block, block_data) in method.iter_blocks() {
        match &block_data.term {
            Terminator::Jump(nxt) => {
                preds[nxt.0].push(block);
                succs[block.0].push(*nxt);
            }
            Terminator::CondJump {
                cond: _,
                true_: b1,
                false_: b2,
            } => {
                preds[b1.0].push(block);
                preds[b2.0].push(block);
                succs[block.0].push(*b1);
                succs[block.0].push(*b2);
            }
            _ => {}
        }
    }
    let mut antic_in: AntileaderSet = vec![LinkedList::new(); num_blocks];
    let mut block_queue: Vec<BlockRef> = vec![];
    for block in method.iter_blocks() {
        block_queue.push(block.0);
    }
    let mut in_queue: Vec<bool> = vec![true; num_blocks];

    let mut qidx = 0;
    while qidx < block_queue.len() {
        let block = block_queue[qidx];
        in_queue[block.0] = false;
        qidx += 1;

        let changed = build_sets_phase2(
            method,
            block,
            &succs,
            &exp_gen,
            &phi_gen,
            &tmp_gen,
            &mut antic_in,
            &mut value_table,
        );

        if changed {
            for pred in preds[block.0].iter() {
                if !in_queue[pred.0] {
                    block_queue.push(*pred);
                    in_queue[pred.0] = true;
                }
            }
        }
    }
    (preds, succs, leaders, antic_in, phi_gen, value_table)
}

fn expr_to_inst(expr: Expression, leader_map: &HashMap<Value, InstRef>) -> Inst {
    match expr {
        Expression::Add(lhs, rhs) => Inst::Add(leader_map[&lhs], leader_map[&rhs]),
        Expression::Sub(lhs, rhs) => Inst::Sub(leader_map[&lhs], leader_map[&rhs]),
        Expression::Mul(lhs, rhs) => Inst::Mul(leader_map[&lhs], leader_map[&rhs]),
        Expression::Div(lhs, rhs) => Inst::Div(leader_map[&lhs], leader_map[&rhs]),
        Expression::Mod(lhs, rhs) => Inst::Mod(leader_map[&lhs], leader_map[&rhs]),
        Expression::Neg(operand) => Inst::Neg(leader_map[&operand]),
        Expression::Not(operand) => Inst::Not(leader_map[&operand]),
        Expression::Copy(src) => Inst::Copy(leader_map[&src]),
        Expression::LoadConst(value) => Inst::LoadConst(value),
        Expression::Eq(lhs, rhs) => Inst::Eq(leader_map[&lhs], leader_map[&rhs]),
        Expression::Neq(lhs, rhs) => Inst::Neq(leader_map[&lhs], leader_map[&rhs]),
        Expression::Less(lhs, rhs) => Inst::Less(leader_map[&lhs], leader_map[&rhs]),
        Expression::LessEq(lhs, rhs) => Inst::LessEq(leader_map[&lhs], leader_map[&rhs]),
        Expression::Reg(_) => panic!("No instruction for Reg value"),
        Expression::Phi(_) => panic!("No instruction for Phi value"),
    }
}

fn perform_insert(
    preds: &Vec<Vec<BlockRef>>,
    succs: &Vec<Vec<BlockRef>>,
    method: &mut Method,
    value_table: &mut ValueTable,
    leaders: &mut LeaderSet,
    phi_gen: &mut PhiGen,
    antic_in: &mut AntileaderSet,
) {
    let num_blocks = method.n_blocks();
    let dom = compute_dominance(method);
    let dom_tree = dom.dominator_tree();

    #[allow(clippy::too_many_arguments)]
    fn insert_recursive(
        block: BlockRef,
        dom_tree: &Vec<Vec<BlockRef>>,
        preds: &Vec<Vec<BlockRef>>,
        _succs: &Vec<Vec<BlockRef>>,
        method: &mut Method,
        value_table: &mut ValueTable,
        leaders: &mut LeaderSet,
        added_leaders: &mut Vec<HashMap<Value, InstRef>>,
        phi_gen: &mut PhiGen,
        antic_in: &mut AntileaderSet,
        _changed: &mut bool,
    ) {
        for (value, inst) in added_leaders[block.0].iter() {
            // Override
            leaders[block.0].insert(value.clone(), *inst);
        }

        if preds[block.0].len() > 1 {
            let translated_values = preds[block.0]
                .iter()
                .map(|pred| {
                    (
                        *pred,
                        phi_translate(
                            method,
                            *pred,
                            &phi_gen[block.0],
                            &antic_in[block.0],
                            value_table,
                        ),
                    )
                })
                .collect::<Vec<(BlockRef, LinkedList<(Value, Expression)>)>>();
            let to_hoist = translated_values
                .iter()
                .flat_map(|(pred, ll)| {
                    ll.iter().zip(&antic_in[block.0]).enumerate().filter_map(
                        |(i, ((val, expr), (orig_val, _)))| {
                            if leaders[pred.0].contains_key(val)
                                && !expr.is_simple()
                                && !added_leaders[pred.0].contains_key(orig_val)
                            {
                                Some(i)
                            } else {
                                None
                            }
                        },
                    )
                })
                .collect::<HashSet<usize>>();

            // println!("Method Name: {:?}", method.name);
            // for (pred, values) in translated_values.iter() {
            //     println!("Predecessor: {:?}", pred);
            //     println!("Leader Table for Block {:?}:", pred);
            //     for (leader_val, leader_inst) in leaders[pred.0].iter() {
            //         println!("  Value: {:?}, InstRef: {:?}", leader_val, leader_inst);
            //     }
            //     for (val, expr) in values {
            //         println!("Value: {:?}, Expression: {:?}", val, expr);
            //     }
            // }

            let mut new_phis = vec![Vec::new(); to_hoist.len()];
            for (pred, exprs) in translated_values.into_iter() {
                let mut i = 0;
                for (k, (val, expr)) in exprs.into_iter().enumerate() {
                    if !to_hoist.contains(&k) {
                        continue;
                    }
                    let leaders = &mut leaders[pred.0];
                    let instref = match leaders.get(&val) {
                        Some(inst) => *inst,
                        None => {
                            // println!("Inserting {:?} ({:?}) into {:?}", expr, val, pred);
                            // println!("Current leaders before insertion:");
                            // for (leader_val, leader_inst) in leaders.iter() {
                            //     println!("  Leader Value: {:?}, InstRef: {:?}", leader_val, leader_inst);
                            // }
                            let inst = expr_to_inst(expr.clone(), leaders);
                            let instref = method.next_inst(pred, inst.clone());
                            let (value, _, _) = value_table.maybe_insert_inst(instref, &inst);
                            assert!(
                                value.0 == val.0,
                                "Value table and leader set disagree on instref"
                            );
                            assert!(
                                !leaders.contains_key(&value),
                                "Leader set unexpectedly contains the value."
                            );
                            leaders.insert(value.clone(), instref);
                            added_leaders[pred.0].insert(value.clone(), instref);
                            instref
                        }
                    };

                    new_phis[i].push(instref);
                    i += 1;
                }
            }
            debug_assert_eq!(new_phis.len(), to_hoist.len());

            let phis_to_insert = new_phis
                .into_iter()
                .map(|phi| {
                    Inst::Phi(
                        phi.into_iter()
                            .zip(preds[block.0].iter())
                            .map(|(instref, pred)| (*pred, instref))
                            .collect(),
                    )
                })
                .collect::<Vec<Inst>>();

            let mut i = 0;
            for (k, (val, _)) in antic_in[block.0].iter().enumerate() {
                if !to_hoist.contains(&k) {
                    continue;
                }
                let instref = method.next_inst_prepend(block, phis_to_insert[i].clone());
                let Inst::Phi(phi) = phis_to_insert[i].clone() else {
                    unreachable!()
                };
                value_table.tie_expr(Expression::new_phi(phi), val.clone());
                value_table.tie_inst(instref, val.clone());

                if leaders[block.0].contains_key(val) {
                    let old_instref = leaders[block.0].remove(val).unwrap();
                    if let Some(annot) = method.get_inst_annotation(&old_instref) {
                        *method.annotate_inst_mut(instref) = annot.clone();
                    }
                }
                leaders[block.0].insert(val.clone(), instref);
                added_leaders[block.0].insert(val.clone(), instref);
                i += 1;
            }
        }

        for child in dom_tree[block.0].iter() {
            for (k, v) in added_leaders[block.0].clone().iter() {
                added_leaders[child.0].insert(k.clone(), *v);
            }
            insert_recursive(
                *child,
                dom_tree,
                preds,
                _succs,
                method,
                value_table,
                leaders,
                added_leaders,
                phi_gen,
                antic_in,
                _changed,
            );
        }
    }

    let mut rounds = 0;
    loop {
        if rounds > 10 {
            panic!("Too many rounds. Should have converged in at most 3 rounds");
        }
        rounds += 1;
        let mut changed = false;

        let mut added_leaders: Vec<HashMap<Value, InstRef>> = vec![HashMap::new(); num_blocks];
        insert_recursive(
            method.entry,
            &dom_tree,
            preds,
            succs,
            method,
            value_table,
            leaders,
            &mut added_leaders,
            phi_gen,
            antic_in,
            &mut changed,
        );

        if !changed {
            break;
        }
    }
}

fn perform_eliminate(method: &mut Method, leaders: &mut LeaderSet, value_table: &mut ValueTable) {
    // First, collect all necessary changes
    let mut changes: Vec<(InstRef, Inst)> = Vec::new();
    for (block, block_data) in method.iter_blocks() {
        for inst in block_data.insts.iter() {
            let val = value_table.lookup_inst(inst);
            let mut ok = false;
            let leader = leaders[block.0].get(&val).unwrap();
            if leader != inst {
                changes.push((*inst, Inst::Copy(*leader)));
                ok = true;
            }
            // if let Some(leader) = leaders[block.0].get(&val) {
            //     if leader != inst {
            //         changes.push((*inst, Inst::Copy(*leader)));
            //         ok = true;
            //     }
            // }

            if !ok {
                if let Inst::Phi(phi) = method.inst(*inst) {
                    let new_phi = phi
                        .iter()
                        .map(|(pred, instref)| {
                            let val = value_table.lookup_inst(instref);
                            let leader = leaders[pred.0].get(&val).unwrap();
                            (*pred, *leader)
                        })
                        .collect::<HashMap<BlockRef, InstRef>>();
                    if new_phi.ne(phi) {
                        changes.push((*inst, Inst::Phi(new_phi)));
                    }
                }
            }
        }
    }

    // Now apply the changes
    for (inst_ref, new_inst) in changes {
        *method.inst_mut(inst_ref) = new_inst;
    }
}

pub fn perform_gvnpre(method: &mut Method) {
    // show_graphviz(&method.dump_graphviz());
    let (preds, succs, mut leaders, mut antic_in, mut phi_gen, mut value_table) =
        build_sets(method);

    // println! {"leaders"};
    // for (block_index, leader_map) in leaders.iter().enumerate() {
    //     println!("Block {}: {:?}", block_index, leader_map);
    // }
    // println!("antic_in:");
    // for (block_index, antic_values) in antic_in.iter().enumerate() {
    //     println!("Block {}: {:?}", block_index, antic_values);
    // }
    // println! {"phi_gen: \n{:?}\n", phi_gen};
    // println! {"value_table: \n{:?}\n", value_table};

    perform_insert(
        &preds,
        &succs,
        method,
        &mut value_table,
        &mut leaders,
        &mut phi_gen,
        &mut antic_in,
    );

    // println! {"After insertion"};
    // println! {"leaders: \n{:?}\n", leaders};
    // println! {"value_table: \n{:?}\n", value_table};

    perform_eliminate(method, &mut leaders, &mut value_table);
    // println!("Finished perform_gvnpre");
    // show_graphviz(&method.dump_graphviz());
}
