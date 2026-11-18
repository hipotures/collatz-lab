//! Finite-state modular Lyapunov contraction certificates (F3) on the
//! Collatz transition graph `G_M` modulo `2^M`.
//!
//! For a modulus `2^M`, each residue `u in {0, ..., 2^M - 1}` has two outgoing
//! edges in `G_M` corresponding to the parity of the next bit `t mod 2` of
//! `n = u + 2^M t`:
//! - even `u`: `u -> u/2` and `u -> u/2 + 2^(M-1)` (0 odd steps),
//! - odd `u`: `u -> ((3u+1)/2) mod 2^M` and `u -> (((3u+1)/2) mod 2^M) ^ 2^(M-1)` (1 odd step).
//!
//! An exact integer modular Lyapunov certificate on `V_M \ S` with contraction
//! rate `p/q` (`3^p < 2^q`) is a map `phi: V_M \ S -> Z` satisfying
//! `q * odd(u) + phi(v) - phi(u) <= p` for every edge `(u -> v)` with
//! `u, v not in S`. Telescoping along any length-`L` orbit segment staying in
//! `V_M \ S` proves `q * r_L + phi(u_L) - phi(u_0) <= p * L`, guaranteeing a
//! strict coefficient crossing (`3^r < 2^L`) once `2^(q*L) > 3^(p*L + span)`.
//!
//! Nothing here prevents an orbit from entering the excluded set `S` or proves
//! the Collatz conjecture.

use std::collections::VecDeque;

use num_bigint::BigUint;
use num_traits::One;
use serde::Serialize;

use crate::counting::count_by_length;

pub const DEFAULT_MAX_MODULUS_BITS: usize = 10;
pub const MAX_SUPPORTED_MODULUS_BITS: usize = 12;
pub const TARGET_P: i64 = 63;
pub const TARGET_Q: i64 = 100;

/// Exact verified modular Lyapunov certificate on `V_M \ excluded`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LyapunovCertificate {
    pub modulus_bits: usize,
    pub target_p: i64,
    pub target_q: i64,
    pub excluded_count: usize,
    pub active_count: usize,
    pub active_edge_count: usize,
    pub potential_span: i64,
    pub contraction_horizon: usize,
    pub excluded: Vec<usize>,
}

/// Summary row for one modulus depth `M` (`N = 2^M`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LyapunovRow {
    pub modulus_bits: usize,
    pub modulus: usize,
    pub full_graph_max_cycle_r: usize,
    pub full_graph_max_cycle_k: usize,
    pub minus_one_removed_max_cycle_r: usize,
    pub minus_one_removed_max_cycle_k: usize,
    pub minus_one_witness_cycle: Vec<usize>,
    pub f2_survivor_count: usize,
    pub f2_potential_span: i64,
    pub f2_contraction_horizon: usize,
    pub f3_excluded_count: usize,
    pub f3_saved_vs_f2: usize,
    pub f3_potential_span: i64,
    pub f3_contraction_horizon: usize,
    pub f3_certificate: LyapunovCertificate,
}

/// Complete bounded modular Lyapunov experiment over `1 <= M <= max_m`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LyapunovExperiment {
    pub schema: String,
    pub tool_version: String,
    pub min_modulus_bits: usize,
    pub max_modulus_bits: usize,
    pub target_p: i64,
    pub target_q: i64,
    pub rows: Vec<LyapunovRow>,
}

/// Build the exact transition graph `G_M` on `{0, ..., 2^M - 1}`.
pub fn build_transition_graph(m_bits: usize) -> Vec<[usize; 2]> {
    assert!(
        (1..=MAX_SUPPORTED_MODULUS_BITS).contains(&m_bits),
        "modulus bits {m_bits} out of range"
    );
    let n = 1usize << m_bits;
    let half = 1usize << (m_bits - 1);
    let mask = n - 1;
    let mut adj = Vec::with_capacity(n);
    for u in 0..n {
        let base = if (u & 1) == 1 {
            ((3 * u + 1) >> 1) & mask
        } else {
            u >> 1
        };
        adj.push([base, base ^ half]);
    }
    adj
}

/// Exact set of F2 survivors of length `M`: residues `u in [0, 2^M)` whose
/// length-`j` prefixes satisfy `2^j < 3^(r_j)` for all `1 <= j <= M`.
pub fn f2_survivors(m_bits: usize) -> Vec<usize> {
    let n = 1usize << m_bits;
    let mut survivors = Vec::new();
    for u in 0..n {
        let mut x = u as u64;
        let mut pow3 = 1u128;
        let mut survived = true;
        for j in 1..=m_bits {
            if (x & 1) == 1 {
                x = (3 * x + 1) >> 1;
                pow3 *= 3;
            } else {
                x >>= 1;
            }
            if (1u128 << j) > pow3 {
                survived = false;
                break;
            }
        }
        if survived {
            survivors.push(u);
        }
    }
    survivors
}

/// Verify the exact integer inequality `3^p < 2^q`.
pub fn verify_contraction_target(p: i64, q: i64) -> Result<(), String> {
    if p <= 0 || q <= 0 {
        return Err(format!("target ({p}, {q}) must be positive"));
    }
    let lhs = BigUint::from(3u32).pow(p as u32);
    let rhs = BigUint::one() << (q as usize);
    if lhs >= rhs {
        return Err(format!("3^{p} is not strictly less than 2^{q}"));
    }
    Ok(())
}

/// Exact least `L >= 1` such that `2^(q*L) > 3^(p*L + span)`.
pub fn contraction_horizon(p: i64, q: i64, span: i64) -> usize {
    assert!(p > 0 && q > 0 && span >= 0);
    let pow2_q = BigUint::one() << (q as usize);
    let pow3_p = BigUint::from(3u32).pow(p as u32);
    let mut lhs = pow2_q.clone();
    let mut rhs = BigUint::from(3u32).pow(span as u32) * &pow3_p;
    let mut l = 1usize;
    while lhs <= rhs {
        lhs *= &pow2_q;
        rhs *= &pow3_p;
        l += 1;
    }
    l
}

/// Solve `phi(v) <= phi(u) + (p - q * odd(u))` on the active induced subgraph
/// via exact integer SPFA (Bellman-Ford with queue). Returns `Some(phi)` if
/// feasible (and independently verified on every active edge), or `None` if a
/// cycle violates the target rate `p/q`.
pub fn solve_integer_potential(
    adj: &[[usize; 2]],
    active: &[bool],
    p: i64,
    q: i64,
) -> Option<Vec<i64>> {
    let n = adj.len();
    let active_count = active.iter().filter(|&&a| a).count();
    if active_count == 0 {
        return Some(vec![0; n]);
    }
    let mut dist = vec![0i64; n];
    let mut in_queue = vec![false; n];
    let mut relax_len = vec![0usize; n];
    let mut queue = VecDeque::with_capacity(active_count);
    for u in 0..n {
        if active[u] {
            queue.push_back(u);
            in_queue[u] = true;
        }
    }
    while let Some(u) = queue.pop_front() {
        in_queue[u] = false;
        let w = p - q * ((u & 1) as i64);
        let du = dist[u];
        for &v in &adj[u] {
            if !active[v] {
                continue;
            }
            let cand = du.checked_add(w).expect("i64 potential overflow");
            if cand < dist[v] {
                dist[v] = cand;
                relax_len[v] = relax_len[u] + 1;
                if relax_len[v] >= active_count {
                    return None;
                }
                if !in_queue[v] {
                    queue.push_back(v);
                    in_queue[v] = true;
                }
            }
        }
    }
    // Independent edge-by-edge verification of the potential.
    verify_integer_potential(adj, active, &dist, p, q).ok()?;
    Some(dist)
}

/// Independently verify that `q * odd(u) + phi[v] - phi[u] <= p` for every
/// active edge `(u -> v)`.
pub fn verify_integer_potential(
    adj: &[[usize; 2]],
    active: &[bool],
    phi: &[i64],
    p: i64,
    q: i64,
) -> Result<(usize, i64), String> {
    let mut edge_count = 0usize;
    let mut min_phi = i64::MAX;
    let mut max_phi = i64::MIN;
    for (u, &is_active) in active.iter().enumerate() {
        if !is_active {
            continue;
        }
        min_phi = min_phi.min(phi[u]);
        max_phi = max_phi.max(phi[u]);
        let odd = (u & 1) as i64;
        for &v in &adj[u] {
            if !active[v] {
                continue;
            }
            edge_count += 1;
            let lhs = q * odd + phi[v] - phi[u];
            if lhs > p {
                return Err(format!("potential fails on edge {u} -> {v}: {lhs} > {p}"));
            }
        }
    }
    let span = if min_phi <= max_phi {
        max_phi - min_phi
    } else {
        0
    };
    Ok((edge_count, span))
}

/// Verify the exact `(M - 1) / M` cycle in `G_M \ {2^M - 1}`:
/// starting from `u_0 = 2^(M-1) - 1`, `M - 1` odd steps (avoiding `2^M - 1`)
/// reach the even vertex `2^M - 2`, whose even edge returns to `2^(M-1) - 1`.
pub fn construct_minus_one_extremal_cycle(m_bits: usize) -> Result<Vec<usize>, String> {
    let adj = build_transition_graph(m_bits);
    let n = 1usize << m_bits;
    let excluded = n - 1;
    if m_bits == 1 {
        if adj[0].contains(&0) {
            return Ok(vec![0]);
        }
        return Err("M=1: missing 0 -> 0 self-loop".into());
    }
    let start = (1usize << (m_bits - 1)) - 1;
    let goal = n - 2;
    // Layered BFS of exact depth m_bits - 1: vertices at layers 0..m_bits-2 must be odd != excluded,
    // and layer m_bits - 1 must reach `goal` (even).
    let mut parent = vec![vec![None; n]; m_bits];
    parent[0][start] = Some(start);
    let mut frontier = vec![start];
    for step in 0..(m_bits - 1) {
        let mut next_frontier = Vec::new();
        for &u in &frontier {
            for &v in &adj[u] {
                if v == excluded {
                    continue;
                }
                let ok = if step + 1 == m_bits - 1 {
                    v == goal
                } else {
                    (v & 1) == 1
                };
                if ok && parent[step + 1][v].is_none() {
                    parent[step + 1][v] = Some(u);
                    next_frontier.push(v);
                }
            }
        }
        frontier = next_frontier;
    }
    if parent[m_bits - 1][goal].is_none() {
        return Err(format!(
            "M={m_bits}: failed to find extremal cycle to {goal}"
        ));
    }
    let mut cycle = vec![0usize; m_bits];
    let mut cur = goal;
    for step in (0..m_bits).rev() {
        cycle[step] = cur;
        if step > 0 {
            cur = parent[step][cur].expect("reconstructed parent");
        }
    }
    // Verify the cycle independently!
    if cycle.len() != m_bits {
        return Err(format!("M={m_bits}: wrong cycle length"));
    }
    let mut odd_count = 0usize;
    for i in 0..m_bits {
        let u = cycle[i];
        let v = cycle[(i + 1) % m_bits];
        if u == excluded {
            return Err(format!("M={m_bits}: cycle touches 2^M - 1"));
        }
        if !adj[u].contains(&v) {
            return Err(format!("M={m_bits}: invalid edge {u} -> {v}"));
        }
        if (u & 1) == 1 {
            odd_count += 1;
        }
    }
    if odd_count != m_bits - 1 {
        return Err(format!(
            "M={m_bits}: expected {} odd steps, got {odd_count}",
            m_bits - 1
        ));
    }
    Ok(cycle)
}

/// Run the bounded modular Lyapunov experiment for `1 <= M <= max_m`.
pub fn run_lyapunov(max_m: usize) -> Result<LyapunovExperiment, String> {
    if max_m == 0 || max_m > MAX_SUPPORTED_MODULUS_BITS {
        return Err(format!(
            "max_m={max_m} out of supported range 1..={MAX_SUPPORTED_MODULUS_BITS}"
        ));
    }
    verify_contraction_target(TARGET_P, TARGET_Q)?;
    let length_counts = count_by_length(max_m);
    let mut rows = Vec::with_capacity(max_m);

    for (m_bits, expected_survivors) in length_counts
        .survivors
        .iter()
        .enumerate()
        .take(max_m + 1)
        .skip(1)
    {
        let n = 1usize << m_bits;
        let adj = build_transition_graph(m_bits);

        // 1. Verify full-graph self-loop at 2^M - 1 (odd density 1/1).
        if !adj[n - 1].contains(&(n - 1)) {
            return Err(format!("M={m_bits}: missing self-loop at {}", n - 1));
        }

        // 2. Verify G_M \ {2^M - 1} has exact max odd density (M - 1) / M:
        //    - lower bound: explicit cycle of length M with M - 1 odd vertices,
        //    - upper bound: exact integer potential exists at (p, q) = (M - 1, M).
        let witness_cycle = construct_minus_one_extremal_cycle(m_bits)?;
        let mut active_minus_one = vec![true; n];
        active_minus_one[n - 1] = false;
        let p_tight = (m_bits - 1) as i64;
        let q_tight = m_bits as i64;
        if solve_integer_potential(&adj, &active_minus_one, p_tight, q_tight).is_none() {
            return Err(format!(
                "M={m_bits}: G_M \\ {{2^M - 1}} exceeded theoretical upper bound ({p_tight}/{q_tight})"
            ));
        }

        // 3. F2-induced Lyapunov certificate on G_M \ Survivors_M.
        let surv = f2_survivors(m_bits);
        if &BigUint::from(surv.len()) != expected_survivors {
            return Err(format!(
                "M={m_bits}: F2 survivor count {} disagrees with counting recurrence {expected_survivors}",
                surv.len(),
            ));
        }
        let mut active_f2 = vec![true; n];
        for &u in &surv {
            active_f2[u] = false;
        }
        let phi_f2 = solve_integer_potential(&adj, &active_f2, TARGET_P, TARGET_Q)
            .ok_or_else(|| format!("M={m_bits}: F2 complement failed to contract at 63/100"))?;
        let (_, f2_span) = verify_integer_potential(&adj, &active_f2, &phi_f2, TARGET_P, TARGET_Q)?;
        let f2_horizon = contraction_horizon(TARGET_P, TARGET_Q, f2_span);

        // 4. F3-pruned Lyapunov certificate: greedily restore redundant F2 survivors
        //    while keeping exact integer contraction at (63, 100).
        let mut active_f3 = active_f2;
        let mut kept_excluded = Vec::new();
        for &u in &surv {
            active_f3[u] = true;
            if solve_integer_potential(&adj, &active_f3, TARGET_P, TARGET_Q).is_none() {
                active_f3[u] = false;
                kept_excluded.push(u);
            }
        }
        let phi_f3 = solve_integer_potential(&adj, &active_f3, TARGET_P, TARGET_Q)
            .ok_or_else(|| format!("M={m_bits}: F3 pruned set failed final check"))?;
        let (f3_edges, f3_span) =
            verify_integer_potential(&adj, &active_f3, &phi_f3, TARGET_P, TARGET_Q)?;
        let f3_horizon = contraction_horizon(TARGET_P, TARGET_Q, f3_span);

        let f3_excluded_count = kept_excluded.len();
        let f3_certificate = LyapunovCertificate {
            modulus_bits: m_bits,
            target_p: TARGET_P,
            target_q: TARGET_Q,
            excluded_count: f3_excluded_count,
            active_count: n - f3_excluded_count,
            active_edge_count: f3_edges,
            potential_span: f3_span,
            contraction_horizon: f3_horizon,
            excluded: kept_excluded,
        };

        rows.push(LyapunovRow {
            modulus_bits: m_bits,
            modulus: n,
            full_graph_max_cycle_r: 1,
            full_graph_max_cycle_k: 1,
            minus_one_removed_max_cycle_r: m_bits - 1,
            minus_one_removed_max_cycle_k: m_bits,
            minus_one_witness_cycle: witness_cycle,
            f2_survivor_count: surv.len(),
            f2_potential_span: f2_span,
            f2_contraction_horizon: f2_horizon,
            f3_excluded_count,
            f3_saved_vs_f2: surv.len() - f3_excluded_count,
            f3_potential_span: f3_span,
            f3_contraction_horizon: f3_horizon,
            f3_certificate,
        });
    }

    Ok(LyapunovExperiment {
        schema: "collatz-lab-lyapunov-v1".into(),
        tool_version: env!("CARGO_PKG_VERSION").into(),
        min_modulus_bits: 1,
        max_modulus_bits: max_m,
        target_p: TARGET_P,
        target_q: TARGET_Q,
        rows,
    })
}
