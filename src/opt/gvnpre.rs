pub mod gvnpre {
    use crate::{
        inter::{
            constant::Const,
            ir::{BlockRef, Inst, InstRef, Method, Terminator},
        },
        opt::dom::compute_dominance, utils::show_graphviz,
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
                Expression::Phi(_) => vec![],
            }
        }

        fn is_simple(&self) -> bool {
            match self {
                Expression::Add(..) => false,
                Expression::Sub(..) => false,
                Expression::Mul(..) => false,
                Expression::Div(..) => false,
                Expression::Neg(..) => false,
                Expression::Not(..) => false,
                Expression::Copy(..) => false,
                Expression::LoadConst(_) => false,
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

        pub fn lookup_inst(&self, inst: InstRef) -> Value {
            // Must exist, otherwise panic!
            self.map.get(&inst).unwrap().clone()
        }

        pub fn lookup_expr(&mut self, expr: &Expression) -> (Value, bool) {
            if let Expression::Copy(src) = expr {
                debug_assert!(src.0 < self._next_value);
                return (src.clone(), false);
            }
            match self
                .values
                .iter()
                .find_map(|(k, v)| if k == expr { Some(v) } else { None })
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

        // pub fn get_value(&self, inst: InstRef) -> Option<&Value> {
        //     self.map.get(&inst)
        // }

        pub fn tie_expr(&mut self, expr: Expression, value: Value) {
            if let Some(index) =
                self.values
                    .iter()
                    .find_map(|(k, v)| if *k == expr { Some(v) } else { None })
            {
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
            leaders[current_block.0].entry(value.clone()).or_insert(inst);
            if okay {
                if let Expression::Phi(_) = expr {
                    phi_gen[current_block.0].insert(value.clone(), inst);
                }
            } else {
                tmp_gen[current_block.0].insert(inst);
            }

            if added_vals.insert(value.clone()) {
                exp_gen[current_block.0].push_back((value.clone(), expr.clone()));
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
        phi_gen: &LinkedList<(Value, Expression)>,
        value_table: &mut ValueTable,
    ) -> LinkedList<(Value, Expression)> {
        let mut result = LinkedList::new();
        for (value, expr) in phi_gen.iter() {
            if let Expression::Phi(phi) = expr {
                let translated_value = phi[&block];
                let new_expr = Expression::new_copy(value_table.lookup_inst(translated_value));
                let (new_val, _) = value_table.lookup_expr(&new_expr);
                result.push_back((new_val, new_expr));
            } else {
                result.push_back((value.clone(), expr.clone()));
            }
        }
        result
    }

    fn build_sets_phase2(
        block: BlockRef,
        succs: &Vec<Vec<BlockRef>>,
        exp_gen: &Vec<LinkedList<(Value, Expression)>>,
        tmp_gen: &Vec<HashSet<InstRef>>,
        antic_in: &mut AntileaderSet,
        value_table: &mut ValueTable,
    ) -> bool {
        let succs = &succs[block.0];
        let mut result = LinkedList::new();
        if succs.len() == 1 {
            // Phi translate and propagate
            let succ = succs[0];
            result = phi_translate(block.clone(), &antic_in[succ.0], value_table);
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
                block,
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
        antic_in: &mut AntileaderSet,
    ) {
        let num_blocks = method.n_blocks();
        let dom = compute_dominance(method);
        let dom_tree = dom.dominator_tree();

        fn insert_recursive(
            block: BlockRef,
            dom_tree: &Vec<Vec<BlockRef>>,
            preds: &Vec<Vec<BlockRef>>,
            succs: &Vec<Vec<BlockRef>>,
            method: &mut Method,
            value_table: &mut ValueTable,
            leaders: &mut LeaderSet,
            added_leaders: &mut Vec<HashMap<Value, InstRef>>,
            antic_in: &mut AntileaderSet,
            changed: &mut bool,
        ) {
            for (value, inst) in added_leaders[block.0].iter() {
                // Override
                leaders[block.0].insert(value.clone(), inst.clone());
            }

            if preds[block.0].len() > 1 {
                let translated_values = preds[block.0]
                    .iter()
                    .map(|pred| {
                        (
                            pred.clone(),
                            phi_translate(*pred, &antic_in[block.0], value_table),
                        )
                    })
                    .collect::<Vec<(BlockRef, LinkedList<(Value, Expression)>)>>();
                let to_hoist = translated_values
                    .iter()
                    .flat_map(|(pred, ll)| {
                        ll.iter().zip(&antic_in[block.0]).enumerate().filter_map(
                            |(i, ((val, expr), (orig_val, _)))| {
                                if leaders[pred.0].contains_key(&val)
                                    && !expr.is_simple()
                                    && !added_leaders[pred.0].contains_key(&orig_val)
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
                                let inst = expr_to_inst(expr.clone(), leaders);
                                let instref = method.next_inst(pred.clone(), inst.clone());
                                let (value, _, _) = value_table.maybe_insert_inst(instref, &inst);
                                assert!(value.0 == val.0, "Value table and leader set disagree on instref");
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
                                .map(|(instref, pred)| (pred.clone(), instref))
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

                    if leaders[block.0].contains_key(&val) {
                        let old_instref = leaders[block.0].remove(&val).unwrap();
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
                    added_leaders[child.0].insert(k.clone(), v.clone());
                }
                insert_recursive(
                    child.clone(),
                    dom_tree,
                    preds,
                    succs,
                    method,
                    value_table,
                    leaders,
                    added_leaders,
                    antic_in,
                    changed,
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
                antic_in,
                &mut changed,
            );

            if !changed {
                break;
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
        // show_graphviz(&method.dump_graphviz());
        let (preds, succs, mut leaders, mut antic_in, _phi_gen, mut value_table) =
            build_sets(method);

        // println! {"leaders: \n{:?}\n", leaders};
        // println! {"antic_in: \n{:?}\n", antic_in};
        // // println! {"phi_gen: \n{:?}\n", phi_gen};
        // println! {"value_table: \n{:?}\n", value_table};

        perform_insert(
            &preds,
            &succs,
            method,
            &mut value_table,
            &mut leaders,
            &mut antic_in,
        );

        // println! {"After insertion"};
        // println! {"leaders: \n{:?}\n", leaders};
        // println! {"value_table: \n{:?}\n", value_table};

        perform_eliminate(method, &mut leaders, &mut value_table);
        // println!("Finished perform_gvnpre");
        // show_graphviz(&method.dump_graphviz());
    }
}
