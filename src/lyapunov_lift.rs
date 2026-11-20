//! Monotone lift chain for F3 modular Lyapunov excluded sets.
//!
//! **Lifting lemma (exact, elementary).** Reduction modulo `2^M` maps
//! `G_{M+1}` onto `G_M`: an edge `u -> v` of `G_{M+1}` (with `n = u + 2^(M+1) t`,
//! `v = T(n) mod 2^(M+1)`) projects to the edge `u mod 2^M -> T(n) mod 2^M` of
//! `G_M`, and `odd(u) = odd(u mod 2^M)`. Hence, if `phi` is an F3 potential on
//! `V_M \ S`, then `phi(u mod 2^M)` is an F3 potential on `V_{M+1} \ lift(S)`
//! with `lift(S) = {u : u mod 2^M in S}`, `|lift(S)| = 2 |S|`. Consequently the
//! exact optimum density `|S_M*| / 2^M` is non-increasing in `M`. This module
//! checks the lemma concretely at every depth (the lifted potential is verified
//! edge by edge), which is a finite check, not a Lean proof.
//!
//! **Experiment.** Starting from the best known set at depth `M - 1` (the exact
//! optimum `S_M*` where it is available, otherwise the previous chain element),
//! the lifted set is pruned by exact incremental warm-start SPFA over *all*
//! excluded vertices (odd and even, inside or outside the F2 survivors), in
//! several restoration orders. The best result is compared with the
//! survivors-only F3 heuristic of `run_lyapunov`, and the smaller set becomes
//! the next chain element. Every chain element is re-verified from scratch.
//!
//! Each chain element is an upper bound `UB_M >= |S_M*|`; nothing here proves
//! optimality for `M > 8`, an asymptotic density limit, or the Collatz
//! conjecture.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use serde::{Deserialize, Serialize};

use crate::lyapunov::{
    build_reverse_graph, build_transition_graph, contraction_horizon, f2_survivors,
    prefix_odd_steps, prune_survivors, solve_integer_potential, verify_contraction_target,
    verify_integer_potential, GRAPH_MAX_MODULUS_BITS, TARGET_P, TARGET_Q,
};
use crate::lyapunov_exact::solve_exact_minimum;

pub const LIFT_DEFAULT_MAX_M: usize = 18;
pub const LIFT_MAX_SUPPORTED_M: usize = GRAPH_MAX_MODULUS_BITS;
pub const LIFT_DEFAULT_EXACT_SEED_MAX_M: usize = 8;

/// Names of the deterministic restoration orders, in tie-break order.
pub const LIFT_ORDERS: [&str; 4] = ["ascending", "descending", "low-odd-weight", "even-first"];
/// Number of additional pseudo-random restoration orders (fixed xorshift seeds).
pub const LIFT_RANDOM_ORDERS: usize = 16;
/// Starting excluded sets that are pruned: the lifted set alone, and the lifted
/// set united with the F2 survivors (both are feasible exclusions).
pub const LIFT_BASES: [&str; 2] = ["lift", "lift+F2"];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LiftOrderResult {
    pub base: String,
    pub order: String,
    pub excluded_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LiftRow {
    pub modulus_bits: usize,
    pub modulus: usize,
    /// Size of the chain element at depth `M - 1` (`M = 1` lifts `{0}` mod `1`).
    pub parent_count: usize,
    /// `2 * parent_count`; feasibility of this set is the lifting lemma.
    pub lifted_count: usize,
    /// Number of active edges on which the lifted potential was verified.
    pub lifted_potential_edges: usize,
    pub order_results: Vec<LiftOrderResult>,
    pub lift_best_count: usize,
    /// Survivors-only F3 heuristic (min of ascending / low-odd-weight orders),
    /// or `None` if the F2 complement itself is infeasible at the target.
    pub survivor_heuristic_count: Option<usize>,
    /// Exact optimum `|S_M*|` for `M <= exact_seed_max_m`.
    pub exact_count: Option<usize>,
    pub chain_count: usize,
    pub chain_source: String,
    pub chain_even_count: usize,
    pub chain_non_survivor_count: usize,
    pub chain_active_edges: usize,
    pub chain_potential_span: i64,
    pub chain_contraction_horizon: usize,
    pub chain_excluded: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LyapunovLiftExperiment {
    pub schema: String,
    pub tool_version: String,
    pub target_p: i64,
    pub target_q: i64,
    pub max_modulus_bits: usize,
    pub exact_seed_max_m: usize,
    pub rows: Vec<LiftRow>,
}

/// Lift an excluded set and its potential from depth `m_bits - 1` to `m_bits`.
/// `parent_excluded` / `parent_phi` live on `2^(m_bits - 1)` residues.
pub fn lift_excluded_set(
    m_bits: usize,
    parent_excluded: &[usize],
    parent_phi: &[i64],
) -> (Vec<usize>, Vec<i64>) {
    let n = 1usize << m_bits;
    let half = n >> 1;
    assert_eq!(parent_phi.len(), half);
    let mut lifted: Vec<usize> = parent_excluded
        .iter()
        .flat_map(|&s| [s, s + half])
        .collect();
    lifted.sort_unstable();
    let phi = (0..n).map(|u| parent_phi[u & (half - 1)]).collect();
    (lifted, phi)
}

fn xorshift_shuffle(order: &mut [usize], seed: u64) {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    for i in (1..order.len()).rev() {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let j = (state % ((i + 1) as u64)) as usize;
        order.swap(i, j);
    }
}

fn order_for(name: &str, excluded: &[usize], m_bits: usize) -> Vec<usize> {
    let mut order = excluded.to_vec();
    if let Some(k) = name.strip_prefix("random-") {
        order.sort_unstable();
        let k: u64 = k.parse().expect("random order index");
        xorshift_shuffle(&mut order, ((m_bits as u64) << 32) | (k + 1));
        return order;
    }
    match name {
        "ascending" => order.sort_unstable(),
        "descending" => order.sort_unstable_by(|a, b| b.cmp(a)),
        "low-odd-weight" => order.sort_by_key(|&u| (prefix_odd_steps(u as u64, m_bits), u)),
        "even-first" => order.sort_by_key(|&u| (u & 1, u)),
        _ => unreachable!("unknown order {name}"),
    }
    order
}

fn survivor_heuristic(
    adj: &[[usize; 2]],
    rev: &[Vec<usize>],
    m_bits: usize,
    p: i64,
    q: i64,
) -> Option<Vec<usize>> {
    let n = adj.len();
    let surv = f2_survivors(m_bits);
    let mut active = vec![true; n];
    for &u in &surv {
        active[u] = false;
    }
    let phi = solve_integer_potential(adj, &active, p, q)?;
    let (_, _, asc) = prune_survivors(adj, rev, &active, &phi, &surv, p, q);
    let mut lw_order = surv.clone();
    lw_order.sort_by_key(|&u| (prefix_odd_steps(u as u64, m_bits), u));
    let (_, _, lw) = prune_survivors(adj, rev, &active, &phi, &lw_order, p, q);
    Some(if lw.len() < asc.len() { lw } else { asc })
}

/// Run the monotone lift chain for `1 <= M <= max_m` at target `p/q`.
///
/// Equivalent to [`run_lyapunov_lift_resume`] with no prior rows.
pub fn run_lyapunov_lift_with(
    max_m: usize,
    exact_seed_max_m: usize,
    p: i64,
    q: i64,
    threads: usize,
    on_row: &mut dyn FnMut(&LiftRow),
) -> Result<LyapunovLiftExperiment, String> {
    run_lyapunov_lift_resume(Vec::new(), max_m, exact_seed_max_m, p, q, threads, on_row)
}

/// Re-check a previously computed row against the chain element of depth
/// `M - 1` and return a from-scratch potential for its chain element.
fn recheck_prior_row(
    row: &LiftRow,
    m_bits: usize,
    parent_excluded: &[usize],
    parent_phi: &[i64],
    p: i64,
    q: i64,
) -> Result<Vec<i64>, String> {
    let n = 1usize << m_bits;
    let fail = |what: &str| Err(format!("resumed row M={m_bits}: {what}"));
    if row.modulus_bits != m_bits || row.modulus != n {
        return fail("depth out of sequence");
    }
    if row.parent_count != parent_excluded.len() || row.lifted_count != 2 * parent_excluded.len() {
        return fail("parent/lifted count does not match the previous chain element");
    }
    let chain = &row.chain_excluded;
    if row.chain_count != chain.len()
        || chain.windows(2).any(|w| w[0] >= w[1])
        || chain.last().is_some_and(|&u| u >= n)
    {
        return fail("chain set is not a sorted subset of the residues");
    }
    if chain.len() > 2 * parent_excluded.len() {
        return fail("chain density increased");
    }
    let adj = build_transition_graph(m_bits);
    let (lifted, lifted_phi) = lift_excluded_set(m_bits, parent_excluded, parent_phi);
    let mut lifted_active = vec![true; n];
    for &u in &lifted {
        lifted_active[u] = false;
    }
    let (lifted_edges, _) = verify_integer_potential(&adj, &lifted_active, &lifted_phi, p, q)
        .map_err(|e| format!("resumed row M={m_bits}: lifted potential failed: {e}"))?;
    if lifted_edges != row.lifted_potential_edges {
        return fail("lifted edge count differs");
    }
    let mut active = vec![true; n];
    for &u in chain {
        active[u] = false;
    }
    let phi = solve_integer_potential(&adj, &active, p, q)
        .ok_or_else(|| format!("resumed row M={m_bits}: chain element is infeasible"))?;
    let (edges, span) = verify_integer_potential(&adj, &active, &phi, p, q)?;
    let surv_set = f2_survivors(m_bits);
    let non_survivor = chain
        .iter()
        .filter(|u| surv_set.binary_search(u).is_err())
        .count();
    let even = chain.iter().filter(|&&u| u & 1 == 0).count();
    if edges != row.chain_active_edges
        || span != row.chain_potential_span
        || contraction_horizon(p, q, span) != row.chain_contraction_horizon
        || non_survivor != row.chain_non_survivor_count
        || even != row.chain_even_count
    {
        return fail("recomputed chain statistics differ");
    }
    Ok(phi)
}

/// Continue the monotone lift chain from previously computed rows
/// `prior` (depths `1..=prior.len()`, e.g. read back from a checkpoint) up to
/// `max_m`. Every prior row is re-checked from scratch: its lifted potential,
/// a freshly solved potential for its chain element, and all derived
/// statistics. Pruning-order counts of prior rows are carried over as recorded.
///
/// The pruning jobs of each depth run on `threads` worker threads (`0` is
/// treated as `1`); the result does not depend on `threads`. `on_row` is called
/// once per completed depth, before the next depth starts (checkpointing).
pub fn run_lyapunov_lift_resume(
    prior: Vec<LiftRow>,
    max_m: usize,
    exact_seed_max_m: usize,
    p: i64,
    q: i64,
    threads: usize,
    on_row: &mut dyn FnMut(&LiftRow),
) -> Result<LyapunovLiftExperiment, String> {
    if max_m == 0 || max_m > LIFT_MAX_SUPPORTED_M {
        return Err(format!(
            "max_m={max_m} out of supported range 1..={LIFT_MAX_SUPPORTED_M}"
        ));
    }
    verify_contraction_target(p, q)?;

    let mut parent_excluded: Vec<usize> = vec![0];
    let mut parent_phi: Vec<i64> = vec![0];
    let mut rows = Vec::with_capacity(max_m);
    if prior.len() > max_m {
        return Err(format!("{} resumed rows exceed max_m={max_m}", prior.len()));
    }
    let start_m = prior.len() + 1;
    for (i, row) in prior.into_iter().enumerate() {
        let phi = recheck_prior_row(&row, i + 1, &parent_excluded, &parent_phi, p, q)?;
        parent_excluded = row.chain_excluded.clone();
        parent_phi = phi;
        rows.push(row);
    }

    for m_bits in start_m..=max_m {
        let n = 1usize << m_bits;
        let adj = build_transition_graph(m_bits);
        let rev = build_reverse_graph(&adj);

        // 1. Lift and verify the lifted potential edge by edge (lifting lemma).
        let (lifted, lifted_phi) = lift_excluded_set(m_bits, &parent_excluded, &parent_phi);
        let mut lifted_active = vec![true; n];
        for &u in &lifted {
            lifted_active[u] = false;
        }
        let (lifted_edges, _) = verify_integer_potential(&adj, &lifted_active, &lifted_phi, p, q)
            .map_err(|e| format!("M={m_bits}: lifted potential failed: {e}"))?;

        // 2. Prune each base over all of its vertices in several orders.
        let surv_set = f2_survivors(m_bits);
        let mut union = lifted.clone();
        union.extend_from_slice(&surv_set);
        union.sort_unstable();
        union.dedup();
        let mut union_active = vec![true; n];
        for &u in &union {
            union_active[u] = false;
        }
        let union_phi = solve_integer_potential(&adj, &union_active, p, q)
            .ok_or_else(|| format!("M={m_bits}: lift+F2 base infeasible"))?;
        let order_names: Vec<String> = LIFT_ORDERS
            .iter()
            .map(|s| s.to_string())
            .chain((0..LIFT_RANDOM_ORDERS).map(|k| format!("random-{k}")))
            .collect();
        // Every (base, order) job is independent; run them on `threads` worker
        // threads together with the survivors-only heuristic. Results are
        // stored by job index and reduced sequentially, so the outcome is
        // identical for every thread count.
        let jobs: Vec<(&str, &String)> = LIFT_BASES
            .iter()
            .flat_map(|&base| order_names.iter().map(move |name| (base, name)))
            .collect();
        let next_job = AtomicUsize::new(0);
        let slots: Vec<Mutex<Option<Vec<usize>>>> = jobs.iter().map(|_| Mutex::new(None)).collect();
        let workers = threads.max(1).min(jobs.len());
        let survivor = std::thread::scope(|scope| {
            let survivor_handle = scope.spawn(|| survivor_heuristic(&adj, &rev, m_bits, p, q));
            for _ in 0..workers {
                scope.spawn(|| loop {
                    let j = next_job.fetch_add(1, Ordering::Relaxed);
                    let Some(&(base, name)) = jobs.get(j) else {
                        break;
                    };
                    let (base_set, base_active, base_phi) = match base {
                        "lift" => (&lifted, &lifted_active, &lifted_phi),
                        _ => (&union, &union_active, &union_phi),
                    };
                    let order = order_for(name, base_set, m_bits);
                    let (_, _, excl) =
                        prune_survivors(&adj, &rev, base_active, base_phi, &order, p, q);
                    *slots[j].lock().expect("job slot") = Some(excl);
                });
            }
            survivor_handle.join().expect("survivor heuristic thread")
        });
        let mut order_results = Vec::with_capacity(jobs.len());
        let mut lift_best: Option<Vec<usize>> = None;
        for (&(base, name), slot) in jobs.iter().zip(slots) {
            let excl = slot
                .into_inner()
                .expect("job slot")
                .expect("every job completed");
            order_results.push(LiftOrderResult {
                base: base.to_string(),
                order: name.clone(),
                excluded_count: excl.len(),
            });
            if lift_best.as_ref().is_none_or(|b| excl.len() < b.len()) {
                lift_best = Some(excl);
            }
        }
        let lift_best = lift_best.expect("at least one order");
        let lift_best_count = lift_best.len();

        // 3. Comparison candidates: survivors-only F3 heuristic and exact optimum.
        let survivor_heuristic_count = survivor.as_ref().map(Vec::len);
        let exact = if m_bits <= exact_seed_max_m {
            let (opt, _, _, _) = solve_exact_minimum(m_bits, p, q)?;
            Some(opt)
        } else {
            None
        };
        let exact_count = exact.as_ref().map(Vec::len);

        let mut chain = lift_best;
        let mut chain_source = "lift".to_string();
        if let Some(s) = survivor {
            if s.len() < chain.len() {
                chain = s;
                chain_source = "survivor-heuristic".into();
            }
        }
        if let Some(e) = exact {
            if e.len() > chain.len() {
                return Err(format!(
                    "M={m_bits}: heuristic set ({}) smaller than exact optimum ({})",
                    chain.len(),
                    e.len()
                ));
            }
            if e.len() < chain.len() {
                chain = e;
                chain_source = "exact".into();
            }
        }
        chain.sort_unstable();

        // 4. Independent re-verification of the chain element from scratch.
        let mut active = vec![true; n];
        for &u in &chain {
            active[u] = false;
        }
        let phi = solve_integer_potential(&adj, &active, p, q)
            .ok_or_else(|| format!("M={m_bits}: chain element failed final check"))?;
        let (chain_active_edges, span) = verify_integer_potential(&adj, &active, &phi, p, q)?;
        let horizon = contraction_horizon(p, q, span);

        // Density monotonicity: |S_M| / 2^M <= |S_{M-1}| / 2^(M-1).
        if chain.len() > 2 * parent_excluded.len() {
            return Err(format!(
                "M={m_bits}: chain density increased ({} > 2 * {})",
                chain.len(),
                parent_excluded.len()
            ));
        }

        let chain_non_survivor_count = chain
            .iter()
            .filter(|u| surv_set.binary_search(u).is_err())
            .count();
        let chain_even_count = chain.iter().filter(|&&u| u & 1 == 0).count();

        rows.push(LiftRow {
            modulus_bits: m_bits,
            modulus: n,
            parent_count: parent_excluded.len(),
            lifted_count: lifted.len(),
            lifted_potential_edges: lifted_edges,
            order_results,
            lift_best_count,
            survivor_heuristic_count,
            exact_count,
            chain_count: chain.len(),
            chain_source,
            chain_even_count,
            chain_non_survivor_count,
            chain_active_edges,
            chain_potential_span: span,
            chain_contraction_horizon: horizon,
            chain_excluded: chain.clone(),
        });
        on_row(rows.last().expect("row just pushed"));

        parent_excluded = chain;
        parent_phi = phi;
    }

    Ok(LyapunovLiftExperiment {
        schema: "collatz-lab-lyapunov-lift-v1".into(),
        tool_version: env!("CARGO_PKG_VERSION").into(),
        target_p: p,
        target_q: q,
        max_modulus_bits: max_m,
        exact_seed_max_m,
        rows,
    })
}

/// Run the monotone lift chain for `1 <= M <= max_m` at target `p/q` on one thread.
pub fn run_lyapunov_lift_at(
    max_m: usize,
    exact_seed_max_m: usize,
    p: i64,
    q: i64,
) -> Result<LyapunovLiftExperiment, String> {
    run_lyapunov_lift_with(max_m, exact_seed_max_m, p, q, 1, &mut |_| {})
}

/// Run the monotone lift chain at the baseline target `63/100`.
pub fn run_lyapunov_lift(
    max_m: usize,
    exact_seed_max_m: usize,
) -> Result<LyapunovLiftExperiment, String> {
    run_lyapunov_lift_at(max_m, exact_seed_max_m, TARGET_P, TARGET_Q)
}
