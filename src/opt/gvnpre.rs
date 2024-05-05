pub mod gvnpre {
    use crate::{
        inter::{
            constant::Const,
            ir::{Block, BlockRef, Inst, InstRef, Method, Terminator},
        },
        opt::dom::compute_dominance,
    };
    use std::collections::{HashMap, HashSet, LinkedList};

    #[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct Value(pub usize);

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Expression {
        Add(Value, Value),
        Sub(Value, Value),
        Mul(Value, Value),
        Div(Value, Value),
        Neg(Value),
        Not(Value),
        Copy(Value),
        LoadConst(Const),

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
                Expression::Neg(operand) => vec![operand.clone()],
                Expression::Not(operand) => vec![operand.clone()],
                Expression::Copy(src) => vec![src.clone()],
                Expression::LoadConst(_) => vec![],
                Expression::Reg(_) => vec![],
                Expression::Phi(phi) => vec![],
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
        values: Vec<Expression>,
        map: HashMap<InstRef, Value>,
    }
    impl ValueTable {
        pub fn new() -> Self {
            Self {
                values: vec![],
                map: HashMap::new(),
            }
        }

        pub fn insert(&mut self, inst: InstRef, value: Expression) -> (Value, bool) {
            let (value_index, inserted) = self.lookup_expr(&value);
            self.map.insert(inst, value_index.clone());
            (value_index, inserted)
        }

        pub fn lookup_inst(&self, inst: InstRef) -> Value {
            // Must exist, otherwise panic!
            self.map.get(&inst).unwrap().clone()
        }

        pub fn lookup_expr(&mut self, expr: &Expression) -> (Value, bool) {
            if let Expression::Copy(src) = expr {
               if src.0 < self.values.len() {
                   return (src.clone(), false);
               }
            }
            match self.values.iter().position(|v| v == expr) {
                Some(index) => (Value(index), false),
                None => {
                    let ans = self.values.len();
                    self.values.push(expr.clone());
                    (Value(ans), true)
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
                    Expression::new_add(self.lookup_inst(*lhs), self.lookup_inst(*rhs))
                }
                Inst::Sub(lhs, rhs) => {
                    Expression::new_sub(self.lookup_inst(*lhs), self.lookup_inst(*rhs))
                }
                Inst::Mul(lhs, rhs) => {
                    Expression::new_mul(self.lookup_inst(*lhs), self.lookup_inst(*rhs))
                }
                Inst::Div(lhs, rhs) => {
                    Expression::new_div(self.lookup_inst(*lhs), self.lookup_inst(*rhs))
                }
                Inst::Neg(operand) => Expression::new_neg(self.lookup_inst(*operand)),
                Inst::Not(operand) => Expression::new_not(self.lookup_inst(*operand)),
                Inst::Copy(src) => Expression::new_copy(self.lookup_inst(*src)),
                Inst::LoadConst(value) => Expression::new_load_const(value.clone()),
                Inst::Phi(values) => {
                    let phi = Expression::new_phi(values.clone());
                    phi
                }
                _ => {
                    // not considered in optimization
                    okay = false;
                    Expression::new_reg(inst)
                }
            };
            let (value, _) = self.insert(inst, expr.clone());
            (value, expr, okay)
        }

        pub fn get_value(&self, inst: InstRef) -> Option<&Value> {
            self.map.get(&inst)
        }
        pub fn get_expr(&mut self, value: Value) -> Option<&Expression> {
            self.values.get(value.0)
        }
    }

    type LeaderSet = Vec<HashMap<Value, InstRef>>;
    type AntileaderSet = Vec<LinkedList<(Value, Expression)>>;
    type PhiGen = Vec<HashMap<Value, InstRef>>;

    pub fn build_sets_phase1(
        method: &mut Method,
        current_block: BlockRef,
        dom_tree: &[Vec<BlockRef>],
        exp_gen: &mut Vec<LinkedList<(Value, Expression)>>,
        phi_gen: &mut Vec<HashMap<Value, InstRef>>,
        tmp_gen: &mut Vec<HashSet<InstRef>>,
        leaders: &mut Vec<HashMap<Value, InstRef>>,
        value_table: &mut ValueTable,
    ) {
        // Do logic stuff
        let mut added_vals = HashSet::new();
        for inst in method.block(current_block).insts.clone() {
            let (value, expr, okay) = value_table.maybe_insert_inst(inst, method.inst(inst));
            leaders[current_block.0].insert(value.clone(), inst);
            if okay {
                if let Expression::Phi(_) = expr {
                    phi_gen[current_block.0].insert(value.clone(), inst);
                }

                if added_vals.insert(value.clone()) {
                    exp_gen[current_block.0].push_back((value.clone(), expr.clone()));
                }
            } else {
                tmp_gen[current_block.0].insert(inst);
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
        block: BlockRef,
        phi_gen: LinkedList<(Value, Expression)>,
        value_table: &mut ValueTable,
    ) -> LinkedList<(Value, Expression)> {
        let mut result = LinkedList::new();
        for (value, expr) in phi_gen.iter() {
            if let Expression::Phi(phi) = expr {
                let translated_value = phi[&block];
                result.push_back((
                    value.clone(),
                    Expression::new_copy(value_table.lookup_inst(translated_value)),
                ));
            } else {
                result.push_back((value.clone(), expr.clone()));
            }
        }
        result
    }

    fn build_sets_phase2(
        method: &mut Method,
        block: BlockRef,
        preds: &Vec<Vec<BlockRef>>,
        succs: &Vec<Vec<BlockRef>>,
        exp_gen: &Vec<LinkedList<(Value, Expression)>>,
        tmp_gen: &Vec<HashSet<InstRef>>,
        antic_in: &mut AntileaderSet,
        value_table: &mut ValueTable,
    ) -> bool {
        let preds = &preds[block.0];
        let succs = &succs[block.0];
        let mut result = LinkedList::new();
        if succs.len() == 1 {
            // Phi translate and propagate
            let succ = succs[0];
            result = phi_translate(block.clone(), antic_in[succ.0].clone(), value_table);
        } else if succs.len() > 1 {
            // Compute intersection of exprs. Assert no children have phi nodes.
            let mut exprs = antic_in[succs[0].0].clone();
            for succ in succs.iter().skip(1) {
                // Perform intersection one by one
                let mut hashset = HashSet::new();
                for (value, expr) in antic_in[succ.0].iter() {
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
                for dependency in expr.depends_on().iter() {
                    if killed_values.contains(dependency) {
                        killed_values.insert(value.clone());
                        return None;
                    }
                }
                if let Expression::Reg(inst) = expr {
                    if tmp_gen[block.0].contains(inst) {
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

        let mut exp_gen: Vec<LinkedList<(Value, Expression)>> =
            vec![LinkedList::default(); num_blocks];
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
                    preds[nxt.0].push(block.clone());
                    succs[block.0].push(nxt.clone());
                }
                Terminator::CondJump {
                    cond: _,
                    true_: b1,
                    false_: b2,
                } => {
                    preds[b1.0].push(block.clone());
                    preds[b2.0].push(block.clone());
                    succs[block.0].push(b1.clone());
                    succs[block.0].push(b2.clone());
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
                &preds,
                &succs,
                &exp_gen,
                &tmp_gen,
                &mut antic_in,
                &mut value_table,
            );

            if changed {
                for pred in preds[block.0].iter() {
                    if !in_queue[pred.0] {
                        block_queue.push(pred.clone());
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
            Expression::Neg(operand) => Inst::Neg(leader_map[&operand]),
            Expression::Not(operand) => Inst::Not(leader_map[&operand]),
            Expression::Copy(src) => Inst::Copy(leader_map[&src]),
            Expression::LoadConst(value) => Inst::LoadConst(value),
            _ => unreachable!(),
        }
    }


    fn block_insert(
        method: &mut Method,
        block: BlockRef,
        preds: &Vec<Vec<BlockRef>>,
        succs: &Vec<Vec<BlockRef>>,
        leaders: &mut LeaderSet,
        antic_in: &mut AntileaderSet,
        value_table: &mut ValueTable,
    ) -> bool {
        if preds[block.0].len() == 1 {
            return true; // Propagate to parent
        } else if preds[block.0].len() > 1 {
            for (value, expr) in antic_in[block.0].iter() {
                let hoist = preds[block.0]
                    .iter()
                    .any(|succ| leaders[succ.0].contains_key(&value));
                if hoist {
                    // 1. Insert the expression into each predecessor
                    // 2. Create a new temporary in the current block -- set it to PHI(all expr in each predecessor)
                    // 3. Set leader of value in current block to new temporary

                    let mut phi_map = HashMap::new();
                    for pred in preds[block.0].iter() {
                        if let Some(inst) = leaders[pred.0].get(&value) {
                            phi_map.insert(pred.clone(), inst.clone());
                        } else {
                            let inst = expr_to_inst(expr.clone(), &leaders[pred.0]);
                            let instref = method.next_inst(pred.clone(), inst.clone());
                            phi_map.insert(pred.clone(), instref);
                            value_table.maybe_insert_inst(instref, &inst);
                        }
                    }
                    let inst = Inst::Phi(phi_map);
                    let instref = method.next_inst_prepend(block, inst.clone());
                    leaders[block.0].insert(value.clone(), instref);
                    value_table.maybe_insert_inst(instref, &inst);
                }
            }
        }
        false
    }


    fn perform_insert(
        preds: &Vec<Vec<BlockRef>>,
        succs: &Vec<Vec<BlockRef>>,
        method: &mut Method,
        value_table: &mut ValueTable,
        leaders: &mut LeaderSet,
        antic_in: &mut AntileaderSet,
    ) {
        let num_blocks = method.n_blocks();
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

            let changed = block_insert(method, block, preds, succs, leaders, antic_in, value_table);

            if changed {
                for pred in preds[block.0].iter() {
                    if !in_queue[pred.0] {
                        block_queue.push(pred.clone());
                        in_queue[pred.0] = true;
                    }
                }
            }
        }
    }

    fn perform_eliminate(
        method: &mut Method,
        leaders: &mut LeaderSet,
        value_table: &mut ValueTable,
    ) {
        // First, collect all necessary changes
        let mut changes: Vec<(InstRef, Inst)> = Vec::new();
        for (block, block_data) in method.iter_blocks() {
            for inst in block_data.insts.iter() {
                let val = value_table.lookup_inst(*inst);
                if let Some(leader) = leaders[block.0].get(&val) {
                    if leader != inst {
                        changes.push((*inst, Inst::Copy(*leader)));
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
        let (preds, succs, mut leaders, mut antic_in, phi_gen, mut value_table) = build_sets(method);

        println! {"leaders: \n{:?}\n", leaders};
        println! {"antic_in: \n{:?}\n", antic_in};
        println! {"phi_gen: \n{:?}\n", phi_gen};
        println! {"value_table: \n{:?}\n", value_table};

        perform_insert(&preds, &succs, method, &mut value_table, &mut leaders, &mut antic_in);

        println! {"After insertion"};
        println! {"leaders: \n{:?}\n", leaders};
        println! {"value_table: \n{:?}\n", value_table};

        perform_eliminate(method, &mut leaders, &mut value_table)
    }
}
