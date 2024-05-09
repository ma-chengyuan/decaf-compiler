use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
};

use good_lp::{
    constraint, highs, variable, Expression, ProblemVariables, ResolutionError, Solution,
    SolverModel, Variable,
};
use petgraph::graphmap::{NodeTrait, UnGraphMap};

use crate::inter::ir::{Inst, InstRef};

use super::LoweredMethod;

/// The time limit for the ILP solver in seconds.
const HIGHS_TIME_LIMIT: f64 = 60.0; // 10 seconds / per function is pretty generous.
const HIGHS_VERBOSE: bool = false; // Set to false to disable verbose output.

pub struct Coalescer<T: NodeTrait> {
    /// The interference graph.
    gi: UnGraphMap<T, ()>,
    /// The affinity graph.
    ga: UnGraphMap<T, f64>,

    max_color: usize,
    initial_solution: Option<HashMap<T, usize>>,
    colors: HashMap<T, usize>,
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
    pub fn new(l: &LoweredMethod) -> Self {
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

        Self {
            gi,
            ga,
            max_color: l.max_reg,
            colors: HashMap::new(),
            initial_solution: Some(l.reg.clone()),
        }
    }

    pub fn solve_and_apply(mut self, l: &mut LoweredMethod) {
        if self.solve().is_ok() {
            // Sanity check!
            assert!(self.max_color == l.max_reg);
            assert!(self.colors.len() == l.reg.len());
            for (a, b, _) in self.gi.all_edges() {
                assert!(self.colors[&a] != self.colors[&b]);
            }
            for (inst_ref, color) in &self.colors {
                assert!(l.reg.contains_key(inst_ref));
                l.reg.insert(*inst_ref, *color);
            }
        }
    }
}

impl<T: NodeTrait + Debug> Coalescer<T> {
    /// Finds all affinity-violating paths between two interfering nodes (a, b).
    ///
    /// "We call two nodes a, b affinity violating if a and b interfere and
    /// there exists a path P = (V_P, A_P), V_P = {a,...,b} of affinity edges
    /// such that the only interference of nodes in the path is between a and
    /// b". (Definition 4.6 in Hack's thesis)
    fn find_affinity_violating_paths(&self, a: T, b: T) -> Vec<im::Vector<T>> {
        fn dfs<T: NodeTrait>(
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

    fn solve_hardcore(&mut self) -> Result<f64, ResolutionError> {
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
        if let Some(solution) = &self.initial_solution {
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
        model.set_verbose(HIGHS_VERBOSE);
        let start = std::time::Instant::now();
        let solution = model.solve()?;
        if HIGHS_VERBOSE {
            println!("ILP took {:?}", start.elapsed());
        }
        let mut colors = HashMap::new();
        for (k, v) in x.iter() {
            let color = v
                .iter()
                .position(|x| solution.value(*x) > 0.5)
                .ok_or(ResolutionError::Infeasible)?;
            colors.insert(*k, color);
        }
        for (a, b, _) in self.gi.all_edges() {
            if colors[&a] == colors[&b] {
                return Err(ResolutionError::Infeasible);
            }
        }
        if HIGHS_VERBOSE {
            println!("validated ILP solution");
        }
        self.colors = colors;
        Ok(solution.eval(&objective))
    }

    fn solve(&mut self) -> Result<(), ResolutionError> {
        let mut removed: Vec<(T, Vec<T>)> = vec![];
        loop {
            let Some(v) = self.gi.nodes().find(|v| {
                // If a node has less than max_color neighbors then it can always be colored.
                // ... but only if it has no affinity edges
                self.gi.neighbors(*v).count() < self.max_color && !self.ga.contains_node(*v)
            }) else {
                break;
            };
            let neighbors = self.gi.neighbors(v).collect::<Vec<_>>();
            self.gi.remove_node(v);
            removed.push((v, neighbors));
        }
        self.solve_hardcore()?;
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
}
