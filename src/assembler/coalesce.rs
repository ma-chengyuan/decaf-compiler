use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap, HashSet},
    fmt::Debug,
};

#[cfg(feature = "ilp")]
use good_lp::{
    constraint, highs, variable, Expression, ProblemVariables, Solution, SolverModel, Variable,
};
use lazy_static::lazy_static;
use petgraph::{
    algo::tarjan_scc,
    graphmap::{NodeTrait, UnGraphMap},
};

use crate::{
    inter::ir::{Address, Inst, InstRef, ProgPt, StackSlotRef},
    opt::for_each_successor,
    utils::cli::Optimization,
};

use super::{
    identify_fast_arg_insts, LoweredMethod, NonMaterializedArgMapExt, ARG_REGS, CALLEE_SAVE_REGS,
};

/// The time limit for the ILP solver in seconds.
const HIGHS_TIME_LIMIT: f64 = 60.0; // 10 seconds / per function is pretty generous.
lazy_static! {
    static ref HIGHS_VERBOSE: bool = std::env::var("HIGHS_VERBOSE").is_ok();
}

pub trait CoalescingNode: NodeTrait {
    /// Makes a new auxiliary node. Auxillary node must satisfy the following
    /// properties:
    /// - An auxilliary node must not conflict with normal nodes.
    /// - Auxilliary nodes with different i s are distinct.
    fn new_aux(i: usize) -> Self;
}

impl CoalescingNode for InstRef {
    fn new_aux(i: usize) -> Self {
        assert!(i < usize::MAX / 2);
        InstRef(usize::MAX - i)
    }
}

impl CoalescingNode for StackSlotRef {
    fn new_aux(i: usize) -> Self {
        assert!(i < usize::MAX / 2);
        StackSlotRef(usize::MAX - i)
    }
}

pub struct Coalescer<T: CoalescingNode> {
    /// The interference graph.
    gi: UnGraphMap<T, ()>,
    /// The affinity graph.
    ga: UnGraphMap<T, f64>,
    /// Constant affinity preferences: (node, color) -> bonus (or penalty) if
    /// node gets that color.
    pref: HashMap<(T, usize), f64>,

    max_color: usize,
    initial_solution: Option<HashMap<T, usize>>,
    colors: HashMap<T, usize>,

    /// The nodes that have been fixed to a color. Used for heuristic.
    fixed: HashSet<T>,
    /// Old colors of the nodes. Used for heuristic.
    old_colors: HashMap<T, usize>,
}

/// Find a minimum clique edge cover of a chordal graph. Returns None if the
/// graph is not chordal.
///
/// See "On the Fractional Intersection Number of a Graph" by Scheinerman and
/// Trenk (1999).
fn chordal_mcc<N, E>(g: &UnGraphMap<N, E>) -> Option<Vec<HashSet<N>>>
where
    N: NodeTrait + Debug,
    E: Clone,
{
    let mut removed: HashSet<N> = HashSet::new();
    let mut covered: HashSet<(N, N)> = HashSet::new();
    let mut mcc = vec![];
    while g.node_count() > removed.len() {
        let mut result: Option<(N, Vec<N>, bool)> = None;
        'outer: for v in g.nodes().filter(|v| !removed.contains(v)) {
            let n_v = g
                .neighbors(v)
                .filter(|n| !removed.contains(n))
                .collect::<Vec<_>>();
            let mut covers_new = false;
            for i in 0..n_v.len() {
                for j in i + 1..n_v.len() {
                    if !g.contains_edge(n_v[i], n_v[j]) {
                        continue 'outer;
                    }
                }
                if !covered.contains(&(v, n_v[i])) && !covered.contains(&(n_v[i], v)) {
                    covers_new = true;
                }
            }
            result = Some((v, n_v, covers_new));
            break;
        }
        let (v, n_v, covers_new) = result?;
        if covers_new {
            for i in 0..n_v.len() {
                covered.insert((v, n_v[i]));
                for j in i + 1..n_v.len() {
                    covered.insert((n_v[i], n_v[j]));
                }
            }
            mcc.push(n_v.iter().copied().chain(std::iter::once(v)).collect());
        }
        removed.insert(v);
    }
    Some(mcc)
}

/// Computes a clique edge cover of a graph. If the graph is cordal then the
/// result is guaranteed to be a minimum clique edge cover. Otherwise it's just
/// a clique edge cover.
fn clique_cover<N, E>(g: &UnGraphMap<N, E>) -> Vec<HashSet<N>>
where
    N: NodeTrait + Debug,
    E: Clone + Debug,
{
    if let Some(mcc) = chordal_mcc(g) {
        // // Sanity check.
        let mut edges = g
            .all_edges()
            .map(|(a, b, _)| (a, b))
            .collect::<HashSet<_>>();
        for clique in &mcc {
            let clique = clique.iter().copied().collect::<Vec<_>>();
            for i in 0..clique.len() {
                for j in i + 1..clique.len() {
                    edges.remove(&(clique[i], clique[j]));
                    edges.remove(&(clique[j], clique[i]));
                }
            }
        }
        assert!(edges.is_empty());
        mcc
    } else {
        // A very primitive implementation that just returns all edges.
        g.all_edges()
            .map(|(a, b, _)| HashSet::from([a, b]))
            .collect()
    }
}

impl Coalescer<InstRef> {
    pub fn new_reg(l: &LoweredMethod, regs: &[&'static str]) -> Self {
        let mut gi = UnGraphMap::<InstRef, ()>::default();
        for live_set in l.live_at.values() {
            for inst_ref in live_set {
                gi.add_node(*inst_ref);
            }
            let nodes = live_set.iter().cloned().collect::<Vec<_>>();
            for i in 0..nodes.len() {
                for j in i + 1..nodes.len() {
                    gi.add_edge(nodes[i], nodes[j], ());
                }
            }
        }
        let mut ga = UnGraphMap::<InstRef, f64>::default();
        for (inst_ref, inst) in l.method.iter_insts() {
            if !gi.contains_node(inst_ref) {
                continue;
            }
            if let Inst::Phi(map) = inst {
                for (src_block, src_ref) in map.iter() {
                    if !gi.contains_node(*src_ref) {
                        continue;
                    }
                    ga.add_edge(
                        inst_ref,
                        *src_ref,
                        1.0 * l.loops.get_freq(*src_block) as f64,
                    );
                }
            }
        }
        let mut pref: HashMap<(InstRef, usize), f64> = HashMap::new();
        if let Some(arg_loading_insts) = identify_fast_arg_insts(l) {
            for inst_ref in arg_loading_insts {
                match l.method.inst(inst_ref) {
                    Inst::Load(Address::Local(slot_ref)) => {
                        let best_reg = ARG_REGS[slot_ref.0];
                        if let Some(pos) = regs.iter().position(|&r| r == best_reg) {
                            // Prefer the argument to be allocated the argument register,
                            // so we don't need that extra move.
                            pref.insert((inst_ref, pos), 1.0);
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
        // Calling
        for block_ref in l.method.iter_block_refs() {
            let insts = &l.method.block(block_ref).insts;
            let freq = l.loops.get_freq(block_ref);
            for (i, inst_ref) in insts.iter().copied().enumerate() {
                if let Inst::Call { args, .. } = l.method.inst(inst_ref) {
                    let next_pt = if i == insts.len() - 1 {
                        ProgPt::BeforeTerm(block_ref)
                    } else {
                        ProgPt::BeforeInst(insts[i + 1])
                    };
                    let saving_regs = l.live_at[&next_pt]
                        .iter()
                        .copied()
                        .filter(|v| *v != inst_ref)
                        .collect::<Vec<_>>();
                    for (i, arg_ref) in args.iter().copied().take(6).enumerate() {
                        if l.nm_args.is_materialized(inst_ref, arg_ref) {
                            if let Some(pos) = regs.iter().position(|&r| r == ARG_REGS[i]) {
                                // Prefer the argument to be allocated the argument register!
                                pref.insert((arg_ref, pos), 1.0 * freq as f64);
                            }
                        }
                    }
                    for saving_ref in saving_regs {
                        for reg in CALLEE_SAVE_REGS {
                            if let Some(pos) = regs.iter().position(|&r| r == reg) {
                                // Prefer the saving register to be allocated the callee-save register.
                                // Reward is slightly higher. Because saving in caller-saved register.
                                // incurs a push + pop.
                                pref.insert((saving_ref, pos), 2.0 * freq as f64);
                            }
                        }
                    }
                }
            }
        }

        Self {
            gi,
            ga,
            pref,
            fixed: HashSet::new(),
            max_color: l.max_reg,
            colors: HashMap::new(),
            old_colors: HashMap::new(),
            initial_solution: Some(l.reg.clone()),
        }
    }

    pub fn solve_and_apply(mut self, l: &mut LoweredMethod, opts: &HashSet<Optimization>) {
        // Sanity check!
        assert!(self.max_color == l.max_reg);
        let fallback = if self.initial_solution.is_some() {
            if *HIGHS_VERBOSE {
                self.colors = l.reg.clone();
                println!("init cost: {}", self.current_solution_cost());
            }
            self.solve_heuristic();
            // println!("heur cost: {}", self.current_solution_cost());
            self.colors.clone()
        } else {
            l.reg.clone()
        };
        #[allow(clippy::collapsible_if)]
        if opts.contains(&Optimization::CoalesceRegistersILP) {
            if self.solve().is_err() {
                self.colors = fallback;
            }
        }
        for (a, b, _) in self.gi.all_edges() {
            assert!(self.colors[&a] != self.colors[&b]);
        }
        assert!(self.colors.len() == l.reg.len());
        // println!(" ilp cost: {}", self.current_solution_cost());
        for (inst_ref, color) in &self.colors {
            assert!(l.reg.contains_key(inst_ref));
            l.reg.insert(*inst_ref, *color);
        }
    }
}

impl Coalescer<StackSlotRef> {
    #[allow(dead_code)]
    pub fn new_spill_slot(l: &LoweredMethod) {
        let mut gi = UnGraphMap::<StackSlotRef, ()>::default();
        let spill_slots = l.spill_slots.values().collect::<HashSet<_>>();
        let mut out: Vec<HashSet<StackSlotRef>> = vec![HashSet::new(); l.method.n_blocks()];
        // in[b]: the set of stack slots that are live at the beginning of block b.
        let mut in_: Vec<HashSet<StackSlotRef>> = vec![HashSet::new(); l.method.n_blocks()];
        let rev_postorder = crate::opt::reverse_postorder(&l.method);
        let mut changed = true;
        while changed {
            changed = false;
            for block_ref in rev_postorder.iter().rev() {
                let mut live: HashSet<StackSlotRef> = HashSet::new();
                for_each_successor(&l.method, *block_ref, |succ| {
                    live.extend(in_[succ.0].iter())
                });
                if live != out[block_ref.0] {
                    changed = true;
                    out[block_ref.0] = live.clone();
                }
                let consider_nm = |live: &mut HashSet<StackSlotRef>, nm: &HashSet<InstRef>| {
                    for inst_ref in nm {
                        if !matches!(l.method.inst(*inst_ref), Inst::LoadConst(_)) {
                            live.insert(l.spill_slots[inst_ref]);
                        }
                    }
                };
                if let Some((_, nm)) = l.nm_terms.get(block_ref) {
                    consider_nm(&mut live, nm);
                }
                let mut add_clique = |live: &mut HashSet<StackSlotRef>| {
                    for (i, slot) in live.iter().enumerate() {
                        for other in live.iter().skip(i + 1) {
                            gi.add_edge(*slot, *other, ());
                        }
                    }
                };
                add_clique(&mut live);
                for inst_ref in l.method.block(*block_ref).insts.iter().rev() {
                    if let Some(nm) = l.nm_args.get(inst_ref) {
                        consider_nm(&mut live, nm);
                    }
                    match l.method.inst(*inst_ref) {
                        Inst::Load(Address::Local(target)) if spill_slots.contains(&target) => {
                            live.insert(*target);
                        }
                        Inst::Store {
                            addr: Address::Local(target),
                            ..
                        } if spill_slots.contains(&target) => {
                            live.remove(target);
                        }
                        _ => {}
                    }
                    add_clique(&mut live);
                }
                if live != in_[block_ref.0] {
                    changed = true;
                    in_[block_ref.0] = live;
                }
            }
        }
        // TODO: Compute the affinity graph and complete this.
    }
}

impl<T: CoalescingNode + Debug> Coalescer<T> {
    /// Finds all affinity-violating paths between two interfering nodes (a, b).
    ///
    /// "We call two nodes a, b affinity violating if a and b interfere and
    /// there exists a path P = (V_P, A_P), V_P = {a,...,b} of affinity edges
    /// such that the only interference of nodes in the path is between a and
    /// b". (Definition 4.6 in Hack's thesis)
    fn find_affinity_violating_paths(&self, a: T, b: T) -> Vec<im::Vector<T>> {
        fn dfs<T: CoalescingNode>(
            c: &Coalescer<T>,
            cur: T,
            goal: T,
            path: im::Vector<T>,
            taboo: im::HashSet<T>,
            all_paths: &mut Vec<im::Vector<T>>,
        ) {
            if cur == goal {
                all_paths.push(path);
                return;
            }
            for nbor in c.ga.neighbors(cur) {
                if !taboo.contains(&nbor) {
                    let mut new_path = path.clone();
                    new_path.push_back(nbor);
                    let mut new_taboo = taboo.clone();
                    // Can't visit this neighbor again.
                    new_taboo.insert(nbor);
                    // Can't visit all interfering neighbors of that neighbor.
                    new_taboo.extend(c.gi.neighbors(nbor));
                    dfs(c, nbor, goal, new_path, new_taboo, all_paths);
                }
            }
        }
        let mut all_paths = vec![];
        let path = im::Vector::from(vec![a]);
        // Can't visit the starting node a again.
        let mut taboo = im::HashSet::from(vec![a]);
        // Can't visit all interfering neighbors of a, except b. a - b is the
        // only allowed interference.
        taboo.extend(self.gi.neighbors(a).filter(|n| *n != b));
        dfs(self, a, b, path, taboo, &mut all_paths);
        all_paths
    }

    // Finds all maximal cliques in the interference sub graph induced by the
    // nodes in `vs` using the Bron-Kerbosch algorithm.
    //
    // The found maximal cliques are non trivial, i.e. they contain at least 3
    // nodes.
    fn find_maximal_cliques(&self, vs: &HashSet<T>) -> Vec<im::HashSet<T>> {
        fn bron_kerbosch<N, E>(
            g: &UnGraphMap<N, E>,
            vs: &HashSet<N>,
            r: im::HashSet<N>,
            mut p: im::HashSet<N>,
            mut x: im::HashSet<N>,
            results: &mut Vec<im::HashSet<N>>,
        ) where
            N: NodeTrait,
        {
            if p.len() + r.len() < 3 {
                return; // Prune
            }
            if p.is_empty() && x.is_empty() {
                if r.len() >= 3 {
                    results.push(r);
                }
                return;
            }
            // let pivot = *p.iter().chain(x.iter()).next().unwrap();
            // for u in p.clone().difference(g.neighbors(pivot).collect()) {
            for u in p.clone() {
                p.remove(&u);
                let mut r_new = r.clone();
                r_new.insert(u);
                let nbor_u = g
                    .neighbors(u)
                    .filter(|n| vs.contains(n))
                    .collect::<im::HashSet<_>>();
                let p_new = p.clone().intersection(nbor_u.clone());
                let x_new = x.clone().intersection(nbor_u);
                bron_kerbosch(g, vs, r_new, p_new, x_new, results);
                x.insert(u);
            }
        }

        let mut results = vec![];
        bron_kerbosch(
            &self.gi,
            vs,
            im::HashSet::new(),
            vs.iter().cloned().collect(),
            im::HashSet::new(),
            &mut results,
        );
        results
    }

    #[cfg(not(feature = "ilp"))]
    fn solve_ilp(&mut self) -> Result<i64, ()> {
        Err(())
    }

    #[cfg(feature = "ilp")]
    fn solve_ilp(&mut self) -> Result<f64, ()> {
        if self.gi.node_count() == 0 {
            return Ok(0.0);
        }
        let mut problem = ProblemVariables::new();
        let mut x: HashMap<T, Vec<Variable>> = HashMap::new();
        for u in self.gi.nodes() {
            x.insert(u, problem.add_vector(variable().binary(), self.max_color));
        }
        let mut y: HashMap<(T, T), Variable> = HashMap::new();
        let mut objective = Expression::from(0.0);
        for (i, j, w_ij) in self.ga.all_edges() {
            // Convert node index from ga to gi.
            let y_ij = problem.add(variable().binary());
            objective += *w_ij * y_ij;
            y.insert((i, j), y_ij);
        }
        for ((i, c), w) in self.pref.iter() {
            if self.colors.contains_key(i) {
                objective -= *w * x[i][*c];
            }
        }
        let mut model = problem.minimise(objective.clone()).using(highs);
        for (_, v) in x.iter() {
            let sum: Expression = v.iter().sum();
            model = model.with(constraint!(sum == 1));
        }
        // Clique constraints to ensure coloring is valid.
        for clique in clique_cover(&self.gi) {
            for c in 0..self.max_color {
                let sum: Expression = clique.iter().map(|ix| x[ix][c]).sum();
                model = model.with(constraint!(sum <= 1));
            }
        }
        // Affinity constraints to ensure that y_ij is 1 iff x_i and x_j are colored differently.
        for ((i, j), y_ij) in y.iter() {
            for c in 0..self.max_color {
                model = model.with(constraint!(y_ij >= x[i][c] - x[j][c]));
                model = model.with(constraint!(y_ij >= x[j][c] - x[i][c]));
            }
        }
        // Path-cut constraints to speed up the solving process.
        // Idea: if interference a - b is connected with a path of affinity
        // edges, then at least one of the affinity edges can't be satisfied.
        for (a, b, _) in self.gi.all_edges() {
            if !self.ga.contains_node(a) || !self.ga.contains_node(b) {
                continue;
            }
            for path in self.find_affinity_violating_paths(a, b) {
                let sum: Expression = path
                    .iter()
                    .zip(path.iter().skip(1))
                    .map(|(i, j)| y.get(&(*i, *j)).or_else(|| y.get(&(*j, *i))).unwrap())
                    .sum();
                model = model.with(constraint!(sum >= 1));
            }
        }
        // Clique-ray-cut constraints
        for u in self.ga.nodes() {
            let nbors = self.ga.neighbors(u).collect::<HashSet<_>>();
            if nbors.len() < 3 {
                // Don't bother with cliques of size less than 3.
                continue;
            }
            if nbors.len() > 18 {
                // Don't bother with cliques of size more than 15.
                // Bron-Kerbosch is too slow.
                // The worst-case running time for BK is O(3^n/3)
                // 3^(18/3) = 729 seems to be a reasonable limit.
                continue;
            }
            for clique in self.find_maximal_cliques(&nbors) {
                let sum: Expression = clique
                    .iter()
                    .map(|v| y.get(&(u, *v)).or_else(|| y.get(&(*v, u))).unwrap())
                    .sum();
                model = model.with(constraint!(sum >= (clique.len() - 1) as i32));
            }
        }

        model = model.set_time_limit(HIGHS_TIME_LIMIT);
        if self.initial_solution.is_some() {
            // solve_heuristic() must have been called before this. So we have a
            // heuristic solution.
            let solution = &self.colors;
            let mut ilp_soln = HashMap::new();
            for (v, color) in solution {
                if let Some(vs) = x.get(v) {
                    for (c, v) in vs.iter().enumerate() {
                        ilp_soln.insert(*v, if c == *color { 1.0 } else { 0.0 });
                    }
                }
            }
            for ((i, j), y_ij) in y.iter() {
                ilp_soln.insert(*y_ij, if solution[i] != solution[j] { 1.0 } else { 0.0 });
            }
            model = model.set_solution(ilp_soln.into_iter());
        }
        model.set_verbose(*HIGHS_VERBOSE);
        let start = std::time::Instant::now();
        let solution = model.solve().map_err(|_| ())?;
        if *HIGHS_VERBOSE {
            println!("ILP took {:?}", start.elapsed());
        }
        let mut colors = HashMap::new();
        for (k, v) in x.iter() {
            let color = v.iter().position(|x| solution.value(*x) > 0.5).ok_or(())?;
            colors.insert(*k, color);
        }
        for (a, b, _) in self.gi.all_edges() {
            if colors[&a] == colors[&b] {
                return Err(());
            }
        }
        if *HIGHS_VERBOSE {
            println!("validated ILP solution");
        }
        self.colors = colors;
        Ok(solution.eval(&objective))
    }

    fn solve(&mut self) -> Result<(), ()> {
        let mut removed: Vec<(T, Vec<T>)> = vec![];
        let with_prefs = self.pref.keys().map(|(x, _)| *x).collect::<HashSet<_>>();
        loop {
            let Some(v) = self.gi.nodes().find(|v| {
                // If a node has less than max_color neighbors then it can always be colored.
                // ... but only if it has no affinity edges
                self.gi.neighbors(*v).count() < self.max_color
                    && !self.ga.contains_node(*v)
                    && !with_prefs.contains(v)
            }) else {
                break;
            };
            let neighbors = self.gi.neighbors(v).collect::<Vec<_>>();
            self.gi.remove_node(v);
            removed.push((v, neighbors));
        }
        self.solve_ilp()?;
        while let Some((v, neighbors)) = removed.pop() {
            self.gi.add_node(v);
            let colors = neighbors
                .iter()
                .map(|n| self.colors[n])
                .collect::<HashSet<_>>();
            let color = (0..self.max_color).find(|c| !colors.contains(c)).unwrap();
            self.colors.insert(v, color);
            for n in neighbors {
                self.gi.add_edge(v, n, ());
            }
        }
        Ok(())
    }

    #[allow(dead_code)]
    fn current_solution_cost(&mut self) -> f64 {
        let mut cost = 0.0;
        for (i, j, w) in self.ga.all_edges() {
            if self.colors[&i] != self.colors[&j] {
                cost += w;
            }
        }
        for ((i, c), w) in self.pref.iter() {
            if self.colors[i] == *c {
                cost -= w;
            }
        }
        cost
    }

    // Heuristic solver. Faster but probably less optimal.
    fn solve_heuristic(&mut self) {
        // Heuristic must be run with a valid initial solution.
        self.colors = self.initial_solution.as_ref().unwrap().clone();
        // Preferences are implemented as fixed aux node.
        let mut aux_nodes = vec![];
        for (i, ((x, c), w)) in self.pref.iter().enumerate() {
            if !self.colors.contains_key(x) {
                continue;
            }
            let aux_node = T::new_aux(i);
            aux_nodes.push(aux_node);
            self.gi.add_node(aux_node);
            self.ga.add_node(aux_node);
            self.ga.add_edge(*x, aux_node, *w);
            self.colors.insert(aux_node, *c);
            self.fixed.insert(aux_node);
        }
        let mut q = BinaryHeap::new();
        for chunk_with_weight in self.build_chunks() {
            q.push(chunk_with_weight);
        }
        while let Some(ChunkWithWeight { chunk, .. }) = q.pop() {
            self.recolor_chunk(&chunk, &mut q);
        }
        for aux_node in aux_nodes {
            self.gi.remove_node(aux_node);
            self.ga.remove_node(aux_node);
            self.colors.remove(&aux_node);
            self.fixed.remove(&aux_node);
        }
    }

    fn recolor(&mut self, x: T, c: usize) {
        if self.fixed.contains(&x) {
            return;
        }
        if self
            .gi
            .neighbors(x)
            .any(|n| self.fixed.contains(&n) && self.colors[&n] == c)
        {
            // Not admissible.
            return;
        }
        let mut changed = HashSet::new();
        self.set_color(x, c, &mut changed);
        for n in self.gi.neighbors(x).collect::<Vec<_>>() {
            if !self.avoid_color(n, c, &mut changed) {
                // Revert changes.
                for x in &changed {
                    self.colors.insert(*x, self.old_colors[&x]);
                }
                break;
            }
        }
        // Unfix nodes that were fixed.
        for n in changed {
            self.fixed.remove(&n);
        }
    }

    fn set_color(&mut self, x: T, c: usize, changed: &mut HashSet<T>) {
        self.fixed.insert(x);
        self.old_colors.insert(x, self.colors[&x]);
        changed.insert(x);
        self.colors.insert(x, c);
    }

    fn avoid_color(&mut self, x: T, c: usize, changed: &mut HashSet<T>) -> bool {
        if self.colors[&x] != c {
            return true;
        }
        if self.fixed.contains(&x) {
            return false;
        }
        let mut admissible = (0..self.max_color).collect::<HashSet<_>>();
        for n in self.gi.neighbors(x) {
            if self.fixed.contains(&n) {
                admissible.remove(&self.colors[&n]);
            }
        }
        admissible.remove(&c);
        // Choose another color used least by neighbors.
        let Some(c_) = admissible
            .iter()
            .min_by_key(|c| {
                self.gi
                    .neighbors(x)
                    .filter(|n| self.colors[&n] == **c)
                    .count()
            })
            .copied()
        else {
            return false;
        };
        self.set_color(x, c_, changed);
        for n in self.gi.neighbors(x).collect::<Vec<_>>() {
            if !self.avoid_color(n, c_, changed) {
                return false;
            }
        }
        true
    }

    fn build_chunks(&self) -> Vec<ChunkWithWeight<T>> {
        let mut uf = UnionFind {
            root: HashMap::new(),
            rank: HashMap::new(),
        };
        for v in self.gi.nodes() {
            uf.root.insert(v, v);
            uf.rank.insert(v, 0);
        }
        let mut edges = self.ga.all_edges().collect::<Vec<_>>();
        // Sort edge weight from largest to smallest.
        edges.sort_by(|(_, _, w1), (_, _, w2)| w2.partial_cmp(w1).unwrap());
        for (x, y, _) in edges {
            let x = uf.find(x);
            let y = uf.find(y);
            if x == y {
                continue;
            }
            if !self.gi.all_edges().any(|(v, w, _)| {
                let v = uf.find(v);
                let w = uf.find(w);
                (x == v && y == w) || (x == w && y == v)
            }) {
                uf.union(x, y);
            }
        }
        let mut chunks: HashMap<T, HashSet<T>> = HashMap::new();
        for v in self.gi.nodes() {
            let root = uf.find(v);
            chunks.entry(root).or_default().insert(v);
        }
        chunks
            .into_values()
            .map(|chunk| ChunkWithWeight {
                weight: self.chunk_cost(&chunk),
                chunk,
            })
            .collect()
    }

    fn chunk_cost(&self, chunk: &HashSet<T>) -> f64 {
        let mut cost = 0.0;
        for x in chunk {
            for y in self.ga.neighbors(*x).filter(|y| chunk.contains(y)) {
                cost += self.ga.edge_weight(*x, y).unwrap();
            }
        }
        cost / 2.0 // Each edge is counted twice.
    }

    fn recolor_chunk(&mut self, chunk: &HashSet<T>, q: &mut BinaryHeap<ChunkWithWeight<T>>) {
        let mut best_chunk: Option<ChunkWithWeight<T>> = None;
        let mut best_color = 0;
        for c in 0..self.max_color {
            for x in chunk {
                self.fixed.remove(x);
            }
            for x in chunk {
                self.recolor(*x, c);
                self.fixed.insert(*x);
            }
            // Find the best affine component colored to c.
            let mut g_tmp: UnGraphMap<T, ()> = UnGraphMap::new();
            for x in chunk.iter().filter(|x| self.colors[x] == c) {
                g_tmp.add_node(*x);
                for y in self
                    .ga
                    .neighbors(*x)
                    .filter(|y| chunk.contains(y) && self.colors[x] == c)
                {
                    g_tmp.add_edge(*x, y, ());
                }
            }
            let Some(m) = tarjan_scc(&g_tmp)
                .into_iter()
                .map(|cc| {
                    let cc = HashSet::from_iter(cc);
                    ChunkWithWeight {
                        weight: self.chunk_cost(&cc),
                        chunk: cc,
                    }
                })
                .max()
            else {
                continue;
            };
            if let Some(prev_best) = &best_chunk {
                if m.weight > prev_best.weight {
                    best_chunk = Some(m);
                    best_color = c;
                }
            } else {
                best_chunk = Some(m);
                best_color = c;
            }
        }
        for x in chunk {
            self.fixed.remove(x);
        }
        let Some(best_chunk) = best_chunk else {
            return;
        };
        for x in &best_chunk.chunk {
            self.recolor(*x, best_color);
            self.fixed.insert(*x);
        }
        if chunk.len() > best_chunk.chunk.len() {
            let new_chunk: HashSet<T> = chunk.difference(&best_chunk.chunk).copied().collect();
            assert!(!new_chunk.is_empty());
            q.push(ChunkWithWeight {
                weight: self.chunk_cost(&new_chunk),
                chunk: new_chunk,
            });
        }
    }
}

#[derive(Debug, Clone)]
struct ChunkWithWeight<T: NodeTrait> {
    chunk: HashSet<T>,
    weight: f64,
}

impl<T: NodeTrait> PartialEq for ChunkWithWeight<T> {
    fn eq(&self, other: &Self) -> bool {
        self.weight == other.weight
    }
}

impl<T: NodeTrait> Eq for ChunkWithWeight<T> {}

impl<T: NodeTrait> PartialOrd for ChunkWithWeight<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: NodeTrait> Ord for ChunkWithWeight<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        f64::total_cmp(&self.weight, &other.weight)
    }
}

// Union-find
#[derive(Debug, Clone)]
struct UnionFind<T: NodeTrait> {
    root: HashMap<T, T>,
    rank: HashMap<T, usize>,
}

impl<T: NodeTrait> UnionFind<T> {
    fn find(&mut self, x: T) -> T {
        let root = self.root[&x];
        if root == x {
            x
        } else {
            let root = self.find(root);
            self.root.insert(x, root);
            root
        }
    }

    fn union(&mut self, x: T, y: T) {
        let x = self.find(x);
        let y = self.find(y);
        if x == y {
            return;
        }
        match self.rank[&x].cmp(&self.rank[&y]) {
            Ordering::Less => {
                self.root.insert(x, y);
            }
            Ordering::Greater => {
                self.root.insert(y, x);
            }
            Ordering::Equal => {
                self.root.insert(y, x);
                self.rank.insert(x, self.rank[&x] + 1);
            }
        }
    }
}
