//! Implements the algorithm described in section 4.4 of Hack's thesis.
//!
//! Serializes parallel copies into a sequence of copy and swap operations. This
//! will come in handy both for Phi and PhiMem instructions. For this reasons,
//! we use usize instead of InstRef / StackSlotRef here.

use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub enum SerializedStep {
    Copy { from: usize, to: usize },
    Swap(usize, usize),
}

/// Serializes parallel copies into a sequence of copy and swap operations.
///
/// * `par_copies` - A set of parallel copies.
/// * `free` - A set of free registers, if any. Set it to None if we don't want
/// intermediate registers at all.
pub fn serialize_copies(
    mut par_copies: HashSet<(usize, usize)>,
    mut free: Option<HashSet<usize>>,
) -> Vec<SerializedStep> {
    let mut targets: HashMap<usize, HashSet<usize>> = HashMap::new();
    let mut source: HashMap<usize, usize> = HashMap::new();
    for (from, to) in par_copies.iter() {
        targets.entry(*from).or_default().insert(*to);
        source.insert(*to, *from);
    }
    let mut ret = Vec::new();
    while !par_copies.is_empty() {
        // Find a s <- r where s has out degree 0.
        let Some(s) = source
            .keys()
            .find(|s| targets.get(s).map_or(true, |v| v.is_empty()))
            .cloned()
        else {
            break;
        };
        let r = source[&s];
        ret.push(SerializedStep::Copy { from: r, to: s });
        par_copies.remove(&(r, s));
        source.remove(&s);
        // Transfer all out edges from r to s.
        if targets.contains_key(&r) {
            let transferred = targets[&r]
                .iter()
                .filter(|t| **t != r && **t != s)
                .cloned()
                .collect::<Vec<_>>();
            for t in &transferred {
                par_copies.remove(&(r, *t));
                par_copies.insert((s, *t));
                source.insert(*t, s);
            }
            par_copies.remove(&(r, r)); // Remove self-loop from t to t, if any.
            targets.remove(&r);
            targets.entry(s).or_default().extend(transferred);
        }
        if let Some(free) = &mut free {
            free.insert(r);
        }
    }
    // At this point, we have a forest of cycles.

    // First, remove self-loops.
    par_copies.retain(|(from, to)| from != to);
    source.retain(|to, from| from != to);
    drop(targets);

    while !par_copies.is_empty() {
        let (r, _) = par_copies.iter().next().cloned().unwrap();
        let mut cycle = vec![r];
        let mut cur = r;
        loop {
            let next = source[&cur];
            par_copies.remove(&(next, cur));
            if next == r {
                break;
            }
            cycle.push(next);
            cur = next;
        }
        // Cycle: cycle[0] <- cycle[1] <- ... <- cycle[n-1] <- cycle[0]
        if let Some(f) = free.as_ref().and_then(|f| f.iter().next().cloned()) {
            ret.push(SerializedStep::Copy {
                from: cycle[0],
                to: f,
            });
            for (s, r) in cycle.iter().zip(cycle.iter().skip(1)) {
                ret.push(SerializedStep::Copy { from: *r, to: *s });
            }
            ret.push(SerializedStep::Copy {
                from: f,
                to: cycle.last().cloned().unwrap(),
            });
        } else {
            for (s, r) in cycle.iter().zip(cycle.iter().skip(1)) {
                ret.push(SerializedStep::Swap(*r, *s));
            }
        }
    }
    ret
}
