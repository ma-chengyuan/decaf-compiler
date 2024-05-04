
pub mod gvnpre {
    use std::collections::{HashMap, HashSet, LinkedList};
    use crate::{
        inter::{constant::Const, ir::{BlockRef, Inst, InstRef, Method}},
        opt::dom::compute_dominance,
    };

    #[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct Value(pub usize);

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Expression {
        Add(Value, Value),
        Sub(Value, Value),
        Mult(Value, Value),
        Div(Value, Value),
        Neg(Value),
        Not(Value),
        Copy(Value),
        LoadConst(Const),

        Reg(InstRef),
        Phi(HashMap<BlockRef, Value>),
    }

    impl Expression {
        fn new_add(lhs: Value, rhs: Value) -> Self {
            Expression::Add(std::cmp::min(lhs.clone(), rhs.clone()), std::cmp::max(lhs.clone(), rhs.clone()))
        }
        fn new_sub(lhs: Value, rhs: Value) -> Self {
            Expression::Sub(lhs, rhs)
        }
        fn new_mult(lhs: Value, rhs: Value) -> Self {
            Expression::Mult(std::cmp::min(lhs.clone(), rhs.clone()), std::cmp::max(lhs.clone(), rhs.clone()))
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
        fn new_phi(value: HashMap<BlockRef, Value>) -> Self {
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
            let value_index = self.values.iter().position(|v| v == &value);
            let mut inserted = false;
            let ret = match value_index {
                Some(index) => Value(index),
                None => {
                    inserted = true;
                    let new_index = self.values.len();
                    self.values.push(value);
                    Value(new_index)
                }
            };
            self.map.insert(inst, ret.clone());
            (ret, inserted)
        }

        pub fn lookup(&self, inst: InstRef) -> Value {
            // Must exist, otherwise panic!
            self.map.get(&inst).unwrap().clone()
        }

        pub fn maybe_insert_inst(&mut self, inst: InstRef, inst_value: &Inst) -> (Value, bool) {
            if self.map.contains_key(&inst) {
                (self.map.get(&inst).unwrap().clone(), false)
            } else {
                let expr = match inst_value {
                    Inst::Add(lhs, rhs) => Expression::new_add(self.lookup(*lhs), self.lookup(*rhs)),
                    Inst::Sub(lhs, rhs) => Expression::new_sub(self.lookup(*lhs), self.lookup(*rhs)),
                    Inst::Mul(lhs, rhs) => Expression::new_mult(self.lookup(*lhs), self.lookup(*rhs)),
                    Inst::Div(lhs, rhs) => Expression::new_div(self.lookup(*lhs), self.lookup(*rhs)),
                    Inst::Neg(operand) => Expression::new_neg(self.lookup(*operand)),
                    Inst::Not(operand) => Expression::new_not(self.lookup(*operand)),
                    Inst::Copy(src) => Expression::new_copy(self.lookup(*src)),
                    Inst::LoadConst(value) => Expression::new_load_const(value.clone()),
                    Inst::Phi(values) => {
                        let phi = Expression::new_phi(values.iter().map(|(block, value)| (block.clone(), self.lookup(*value))).collect());
                        phi
                    }
                    _ => Expression::new_reg(inst), // Not considered in optimization
                };
                self.insert(inst, expr)
            }
        }

        pub fn get_value(&self, inst: InstRef) -> Option<&Value> {
            self.map.get(&inst)
        }
        pub fn get_expr(&mut self, value: Value) -> Option<&Expression> {
            self.values.get(value.0)
        }
    }

    type LeaderSet = Vec<HashMap<Value, InstRef>>;
    type AntileaderSet = Vec<HashMap<Value, Expression>>;
    type PhiGen = Vec<HashMap<Value, InstRef>>;

    pub fn build_sets_phase1(method: &mut Method,
    current_block: BlockRef,
    dom_tree: &[Vec<BlockRef>],
    exp_gen: &mut Vec<LinkedList<(Value, Expression)>>,
    phi_gen: &mut Vec<HashMap<Value, InstRef>>,
    tmp_gen: &mut Vec<HashSet<InstRef>>,
    leaders: &mut Vec<HashMap<Value, InstRef>>,
    value_table: &mut ValueTable,
    ) {
        // Do logic stuff
        for inst in method.block(current_block).insts.clone() {
            match value_table.maybe_insert_inst(inst, method.inst(inst)) {
                (value, true) => {
                    // Add to leaders
                    let expr = value_table.get_expr(value.clone()).unwrap();

                    leaders[current_block.0].insert(value.clone(), inst);
                    exp_gen[current_block.0].push_back((value.clone(), expr.clone()));

                    if let Expression::Phi(_) = expr {
                        phi_gen[current_block.0].insert(value, inst);
                    } else {
                        tmp_gen[current_block.0].insert(inst);
                    }
                }
                _ => {}
            }
        }
        // Recurse
        for child in dom_tree[current_block.0].iter() {
            leaders[child.0] = leaders[current_block.0].clone();
            build_sets_phase1(method, *child, dom_tree, exp_gen, phi_gen, tmp_gen, leaders, value_table);
        }
    }

    fn build_sets(method: &mut Method) -> (LeaderSet, AntileaderSet, PhiGen, ValueTable) {
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
        {
            println! {"exp_gens: \n{:?}\n", exp_gen};
            println! {"tmp_gen: \n{:?}\n", tmp_gen};
            println! {"phi_gens: \n{:?}\n", phi_gen};
            println! {"leaders: \n{:?}\n", leaders};
            println! {"value_table: \n{:?}\n", value_table};
        }
        // let mut changed = true;
        // let mut antic_out = vec![LinkedList::default(); cfg.len()];
        // let mut antic_in = vec![LinkedList::default(); cfg.len()];
        // while changed {
        //     changed = false;
        //     build_sets_phase2(
        //         cfg,
        //         cfg.get_entry(),
        //         &mut changed,
        //         &mut antic_out,
        //         &mut antic_in,
        //         &exp_gen,
        //         &tmp_gen,
        //         &phi_gen,
        //         &mut value_table,
        //     );
        // }
        // #[cfg(feature = "print-gvn")]
        // {
        //     println! {"antic_in: \n{:?}\n", antic_in};
        // }
        (leaders, AntileaderSet::new(), phi_gen, value_table)
    }

    pub fn perform_gvnpre(method: &mut Method) {
        let (leaders, antic_in, phi_gen, value_table) = build_sets(method);
    }
}

