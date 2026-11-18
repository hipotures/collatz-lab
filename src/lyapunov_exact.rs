//! Exact minimum excluded sets `|S_M*|` (minimum weighted-cycle feedback vertex
//! set on `G_M`), certified integer dual-LP lower bounds, and `p/q` sensitivity
//! analysis for F3 modular Lyapunov certificates.
//!
//! - For `1 <= M <= 8`, exact Branch-and-Cut with certified integer dual-LP
//!   lower bounds computes the global minimum `|S_M*|` over ALL subsets `S <= V_M`.
//! - For `9 <= M <= 12`, an explicit collection of independently verified
//!   violating cycles (`q * r(C) > p * |C|`) and exact `i64` dual weights
//!   certify `LB_M <= |S_M*|`, paired with the verified F3 upper bound `UB_M`.
//! - Sensitivity sweep compares exact `|S_M*|` (`M <= 7`) and F3 `|S_M|` +
//!   exact contraction horizon `L_0` (`8 <= M <= 15`) across rational targets
//!   `p/q < 1/log2(3)`: `5/8, 17/27, 63/100, 41/65, 94/149, 306/485`.

use std::collections::VecDeque;

use serde::Serialize;

use crate::lyapunov::{
    build_transition_graph, contraction_horizon, f2_survivors, run_lyapunov,
    solve_integer_potential, verify_contraction_target, verify_integer_potential, TARGET_P,
    TARGET_Q,
};

pub const EXACT_MAX_M: usize = 8;
pub const BRACKET_MAX_M: usize = 12;
pub const SENSITIVITY_MAX_M: usize = 15;

pub const SENSITIVITY_TARGETS: [(i64, i64); 5] = [(5, 8), (17, 27), (63, 100), (41, 65), (94, 149)];

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactOptimumRow {
    pub modulus_bits: usize,
    pub modulus: usize,
    pub f2_survivor_count: usize,
    pub f3_heuristic_count: usize,
    pub exact_min_count: usize,
    pub heuristic_gap: usize,
    pub exact_even_count: usize,
    pub exact_non_survivor_count: usize,
    pub exact_potential_span: i64,
    pub exact_contraction_horizon: usize,
    pub branch_and_cut_nodes: u64,
    pub optimal_excluded: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CertifiedBracketRow {
    pub modulus_bits: usize,
    pub modulus: usize,
    pub certified_lb: usize,
    pub f3_ub: usize,
    pub dual_cycle_count: usize,
    pub dual_sum_y: i64,
    pub dual_max_load: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SensitivityCell {
    pub p: i64,
    pub q: i64,
    pub excluded_count: usize,
    pub potential_span: i64,
    pub contraction_horizon: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SensitivityRow {
    pub modulus_bits: usize,
    pub modulus: usize,
    pub f2_survivor_count: usize,
    pub cells: Vec<SensitivityCell>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactSensitivityRow {
    pub modulus_bits: usize,
    pub modulus: usize,
    pub cells: Vec<SensitivityCell>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LyapunovExactExperiment {
    pub schema: String,
    pub tool_version: String,
    pub baseline_p: i64,
    pub baseline_q: i64,
    pub exact_rows: Vec<ExactOptimumRow>,
    pub bracket_rows: Vec<CertifiedBracketRow>,
    pub exact_sensitivity_rows: Vec<ExactSensitivityRow>,
    pub f3_sensitivity_rows: Vec<SensitivityRow>,
}

/// Exact SPFA returning `None` if `G_M \ excluded` is feasible at `(p, q)`,
/// or `Some(cycle)` with an independently verified simple violating cycle.
pub fn find_violating_cycle(
    adj: &[[usize; 2]],
    excluded: &[bool],
    p: i64,
    q: i64,
) -> Option<Vec<usize>> {
    let n = adj.len();
    let active_count = excluded.iter().filter(|&&e| !e).count();
    if active_count == 0 {
        return None;
    }
    let mut dist = vec![0i64; n];
    let mut pred = vec![usize::MAX; n];
    let mut in_q = vec![false; n];
    let mut len = vec![0usize; n];
    let mut queue = VecDeque::with_capacity(active_count);
    for (u, &is_excl) in excluded.iter().enumerate() {
        if !is_excl {
            queue.push_back(u);
            in_q[u] = true;
        }
    }
    let mut witness = None;
    'outer: while let Some(u) = queue.pop_front() {
        in_q[u] = false;
        let w = p - q * ((u & 1) as i64);
        let du = dist[u];
        for &v in &adj[u] {
            if excluded[v] {
                continue;
            }
            let cand = du.checked_add(w).expect("i64 SPFA overflow");
            if cand < dist[v] {
                dist[v] = cand;
                pred[v] = u;
                len[v] = len[u] + 1;
                if len[v] >= active_count {
                    witness = Some(v);
                    break 'outer;
                }
                if !in_q[v] {
                    queue.push_back(v);
                    in_q[v] = true;
                }
            }
        }
    }
    let mut cur = witness?;
    for _ in 0..n {
        cur = pred[cur];
    }
    let start = cur;
    let mut cyc = Vec::new();
    loop {
        cyc.push(cur);
        cur = pred[cur];
        if cur == start {
            break;
        }
    }
    cyc.reverse();
    verify_violating_cycle(adj, &cyc, p, q).expect("extracted cycle must violate p/q");
    Some(cyc)
}

/// Independently verify that `cyc` is a directed cycle in `adj` with `q * r > p * len`.
pub fn verify_violating_cycle(
    adj: &[[usize; 2]],
    cyc: &[usize],
    p: i64,
    q: i64,
) -> Result<(), String> {
    if cyc.is_empty() {
        return Err("empty cycle".into());
    }
    let mut r = 0i64;
    for i in 0..cyc.len() {
        let u = cyc[i];
        let v = cyc[(i + 1) % cyc.len()];
        if !adj[u].contains(&v) {
            return Err(format!("invalid edge {u} -> {v} in cycle"));
        }
        r += (u & 1) as i64;
    }
    if q * r <= p * (cyc.len() as i64) {
        return Err(format!(
            "cycle of length {} with {} odd steps does not exceed {p}/{q}",
            cyc.len(),
            r
        ));
    }
    Ok(())
}

fn extract_cycle_batch(adj: &[[usize; 2]], excluded: &[bool], p: i64, q: i64) -> Vec<Vec<usize>> {
    let mut tmp = excluded.to_vec();
    let mut batch = Vec::new();
    while let Some(cyc) = find_violating_cycle(adj, &tmp, p, q) {
        for &v in &cyc {
            tmp[v] = true;
        }
        batch.push(cyc);
    }
    batch
}

/// Exact certified integer lower bound via Multiplicative-Weights dual packing.
/// Returns `ceil(sum_y / max_load)` computed strictly in exact `i64` arithmetic.
fn certified_mwu_lb(
    n: usize,
    cycles: &[Vec<usize>],
    unhit: &[(usize, usize)],
    fixed_in: &[bool],
    rounds: usize,
) -> usize {
    if unhit.is_empty() {
        return 0;
    }
    let k = unhit.len();
    let mut v_to_local = vec![usize::MAX; n];
    let mut local_verts = Vec::new();
    let mut cyc_locals: Vec<Vec<usize>> = Vec::with_capacity(k);
    for &(_, idx) in unhit {
        let mut lv = Vec::new();
        for &v in &cycles[idx] {
            if !fixed_in[v] {
                let mut lid = v_to_local[v];
                if lid == usize::MAX {
                    lid = local_verts.len();
                    v_to_local[v] = lid;
                    local_verts.push(v);
                }
                lv.push(lid);
            }
        }
        cyc_locals.push(lv);
    }
    let nv = local_verts.len();
    if nv == 0 {
        return usize::MAX;
    }
    let mut w = vec![1.0f64; nv];
    let mut y = vec![0i64; k];
    let mult = (0.25f64).exp();
    for _ in 0..rounds {
        let mut best_i = 0;
        let mut best_cost = f64::INFINITY;
        for (i, lv) in cyc_locals.iter().enumerate() {
            let mut cost = 0.0f64;
            for &v in lv {
                cost += w[v];
            }
            if cost < best_cost {
                best_cost = cost;
                best_i = i;
            }
        }
        y[best_i] += 1;
        let mut max_w = 0.0f64;
        for &v in &cyc_locals[best_i] {
            w[v] *= mult;
            if w[v] > max_w {
                max_w = w[v];
            }
        }
        if max_w > 1e100 {
            let inv = 1.0 / max_w;
            for wi in &mut w {
                *wi *= inv;
            }
        }
    }
    let mut load = vec![0i64; nv];
    let mut sum_y = 0i64;
    for (i, lv) in cyc_locals.iter().enumerate() {
        let yi = y[i];
        if yi > 0 {
            sum_y += yi;
            for &v in lv {
                load[v] += yi;
            }
        }
    }
    let max_load = load.into_iter().max().unwrap_or(0);
    if max_load == 0 {
        return 0;
    }
    ((sum_y + max_load - 1) / max_load) as usize
}

struct BranchAndCut {
    adj: Vec<[usize; 2]>,
    p: i64,
    q: i64,
    cycles: Vec<Vec<usize>>,
    best: Vec<usize>,
    upper: usize,
    nodes: u64,
}

impl BranchAndCut {
    fn bnb(&mut self, excluded: &mut [bool], fixed_in: &mut [bool], cur_size: usize) {
        self.nodes += 1;
        if cur_size >= self.upper {
            return;
        }
        let n = self.adj.len();
        let mut forced: Vec<usize> = Vec::new();
        loop {
            let mut unhit: Vec<(usize, usize)> = Vec::new();
            let mut dead = false;
            for (idx, cyc) in self.cycles.iter().enumerate() {
                if cyc.iter().any(|&v| excluded[v]) {
                    continue;
                }
                let free = cyc.iter().filter(|&&v| !fixed_in[v]).count();
                if free == 0 {
                    dead = true;
                    break;
                }
                unhit.push((free, idx));
            }
            if dead {
                for v in forced {
                    excluded[v] = false;
                }
                return;
            }
            if unhit.is_empty() {
                let cuts = extract_cycle_batch(&self.adj, excluded, self.p, self.q);
                if cuts.is_empty() {
                    let total = cur_size + forced.len();
                    if total < self.upper {
                        self.upper = total;
                        self.best = (0..n).filter(|&u| excluded[u]).collect();
                    }
                    for v in forced {
                        excluded[v] = false;
                    }
                    return;
                }
                if cur_size + forced.len() + cuts.len() >= self.upper {
                    self.cycles.extend(cuts);
                    for v in forced {
                        excluded[v] = false;
                    }
                    return;
                }
                self.cycles.extend(cuts);
                continue;
            }
            unhit.sort_unstable();
            if unhit[0].0 == 1 {
                let cyc = &self.cycles[unhit[0].1];
                let v = *cyc.iter().find(|&&x| !fixed_in[x]).unwrap();
                excluded[v] = true;
                forced.push(v);
                if cur_size + forced.len() >= self.upper {
                    for u in forced {
                        excluded[u] = false;
                    }
                    return;
                }
                continue;
            }
            // Fast greedy disjoint LB
            let mut used = vec![false; n];
            let mut greedy_lb = 0usize;
            for &(_, idx) in &unhit {
                let cyc = &self.cycles[idx];
                if cyc.iter().all(|&v| fixed_in[v] || !used[v]) {
                    greedy_lb += 1;
                    for &v in cyc {
                        if !fixed_in[v] {
                            used[v] = true;
                        }
                    }
                }
            }
            if cur_size + forced.len() + greedy_lb >= self.upper {
                for u in forced {
                    excluded[u] = false;
                }
                return;
            }
            let gap = self.upper - (cur_size + forced.len());
            if greedy_lb + 3 >= gap {
                let mwu_lb = certified_mwu_lb(n, &self.cycles, &unhit, fixed_in, 80);
                if cur_size + forced.len() + mwu_lb >= self.upper {
                    for u in forced {
                        excluded[u] = false;
                    }
                    return;
                }
            }
            let free_verts: Vec<usize> = self.cycles[unhit[0].1]
                .iter()
                .copied()
                .filter(|&v| !fixed_in[v])
                .collect();
            let mut freq = vec![0usize; free_verts.len()];
            for &(_, idx) in &unhit {
                let c = &self.cycles[idx];
                for (i, &fv) in free_verts.iter().enumerate() {
                    if c.contains(&fv) {
                        freq[i] += 1;
                    }
                }
            }
            let mut ord: Vec<usize> = (0..free_verts.len()).collect();
            ord.sort_by(|&a, &b| freq[b].cmp(&freq[a]));
            let mut added_fixed = Vec::new();
            for i in ord {
                let v = free_verts[i];
                excluded[v] = true;
                self.bnb(excluded, fixed_in, cur_size + forced.len() + 1);
                excluded[v] = false;
                fixed_in[v] = true;
                added_fixed.push(v);
            }
            for v in added_fixed {
                fixed_in[v] = false;
            }
            for v in forced {
                excluded[v] = false;
            }
            return;
        }
    }
}

/// Fast exact F2-survivor pruning (ascending order) at arbitrary `(p, q)` with `3^p < 2^q`.
pub fn prune_f2_at_target(
    m_bits: usize,
    p: i64,
    q: i64,
) -> Result<(Vec<usize>, i64, usize), String> {
    verify_contraction_target(p, q)?;
    let n = 1usize << m_bits;
    let adj = build_transition_graph(m_bits);
    let mut rev = vec![Vec::with_capacity(2); n];
    for (u, edges) in adj.iter().enumerate() {
        for &v in edges {
            rev[v].push(u);
        }
    }
    let surv = f2_survivors(m_bits);
    let mut active = vec![true; n];
    for &u in &surv {
        active[u] = false;
    }
    let mut phi = solve_integer_potential(&adj, &active, p, q)
        .ok_or_else(|| format!("M={m_bits}: F2 complement failed at {p}/{q}"))?;
    let mut in_queue = vec![false; n];
    let mut queue = VecDeque::with_capacity(64);
    let mut excluded = Vec::new();

    for &u in &surv {
        let w_u = p - q * ((u & 1) as i64);
        if adj[u].contains(&u) && w_u < 0 {
            excluded.push(u);
            continue;
        }
        let mut has_pred = false;
        let mut init_u = i64::MAX;
        for &x in &rev[u] {
            if active[x] {
                let w_x = p - q * ((x & 1) as i64);
                init_u = init_u.min(phi[x].checked_add(w_x).expect("i64 overflow"));
                has_pred = true;
            }
        }
        if !has_pred {
            let mut safe_u = 0i64;
            for &v in &adj[u] {
                if active[v] {
                    safe_u = safe_u.max(phi[v].checked_sub(w_u).expect("i64 overflow"));
                }
            }
            active[u] = true;
            phi[u] = safe_u;
            continue;
        }
        active[u] = true;
        let old_u = phi[u];
        phi[u] = init_u;
        let mut touched = Vec::new();
        queue.clear();
        queue.push_back(u);
        in_queue[u] = true;
        let mut ok = true;
        'spfa: while let Some(x) = queue.pop_front() {
            in_queue[x] = false;
            let w_x = p - q * ((x & 1) as i64);
            let dx = phi[x];
            for &v in &adj[x] {
                if !active[v] {
                    continue;
                }
                let cand = dx.checked_add(w_x).expect("i64 overflow");
                if cand < phi[v] {
                    if v == u {
                        ok = false;
                        break 'spfa;
                    }
                    touched.push((v, phi[v]));
                    phi[v] = cand;
                    if !in_queue[v] {
                        queue.push_back(v);
                        in_queue[v] = true;
                    }
                }
            }
        }
        while let Some(x) = queue.pop_front() {
            in_queue[x] = false;
        }
        if !ok {
            for (v, old_val) in touched.into_iter().rev() {
                phi[v] = old_val;
            }
            phi[u] = old_u;
            active[u] = false;
            excluded.push(u);
        }
    }
    let clean_phi = solve_integer_potential(&adj, &active, p, q)
        .ok_or_else(|| format!("M={m_bits}: final potential check failed at {p}/{q}"))?;
    let (_, span) = verify_integer_potential(&adj, &active, &clean_phi, p, q)?;
    let horizon = contraction_horizon(p, q, span);
    Ok((excluded, span, horizon))
}

/// Compute the exact global minimum `|S_M*|` over ALL subsets `S <= V_M` via Branch-and-Cut.
pub fn solve_exact_minimum(
    m_bits: usize,
    p: i64,
    q: i64,
) -> Result<(Vec<usize>, i64, usize, u64), String> {
    verify_contraction_target(p, q)?;
    let n = 1usize << m_bits;
    let adj = build_transition_graph(m_bits);
    let (heur, _, _) = prune_f2_at_target(m_bits, p, q)?;
    let mut excluded = vec![false; n];
    let mut fixed_in = vec![false; n];
    excluded[n - 1] = true;
    let init_cuts = extract_cycle_batch(&adj, &excluded, p, q);
    let mut solver = BranchAndCut {
        adj: adj.clone(),
        p,
        q,
        cycles: init_cuts,
        best: heur.clone(),
        upper: heur.len(),
        nodes: 0,
    };
    solver.bnb(&mut excluded, &mut fixed_in, 1);

    // Independently verify the optimal excluded set via fresh SPFA + edge check!
    let mut active = vec![true; n];
    for &u in &solver.best {
        active[u] = false;
    }
    let phi = solve_integer_potential(&adj, &active, p, q)
        .ok_or_else(|| format!("M={m_bits}: optimal set failed feasibility check"))?;
    let (_, span) = verify_integer_potential(&adj, &active, &phi, p, q)?;
    let horizon = contraction_horizon(p, q, span);
    Ok((solver.best, span, horizon, solver.nodes))
}

/// Compute a 100% certified integer lower bound `LB_M <= |S_M*|` by collecting
/// independently verified violating cycles in `G_M \ {2^M - 1}` and running
/// exact integer-certified MWU dual packing (`1 + ceil(sum_y / max_load)`).
pub fn certify_dual_lower_bound(
    m_bits: usize,
    p: i64,
    q: i64,
) -> Result<(usize, usize, i64, i64), String> {
    verify_contraction_target(p, q)?;
    let n = 1usize << m_bits;
    let adj = build_transition_graph(m_bits);
    let mut excl = vec![false; n];
    excl[n - 1] = true;
    let mut pool = extract_cycle_batch(&adj, &excl, p, q);
    if pool.is_empty() {
        return Ok((1, 0, 0, 1));
    }
    // Collect rich cycle diversity via greedy hitting-set iterations
    loop {
        let mut unhit_exists = false;
        let mut freq = vec![0usize; n];
        for c in &pool {
            if c.iter().any(|&v| excl[v]) {
                continue;
            }
            unhit_exists = true;
            for &v in c {
                freq[v] += 1;
            }
        }
        if unhit_exists {
            let best_v = (0..n).max_by_key(|&v| (freq[v], v)).unwrap();
            excl[best_v] = true;
            continue;
        }
        let batch = extract_cycle_batch(&adj, &excl, p, q);
        if batch.is_empty() {
            break;
        }
        pool.extend(batch);
    }

    // Independently verify every single cycle in `pool` is a genuine violating cycle in `G_M`
    for cyc in &pool {
        verify_violating_cycle(&adj, cyc, p, q)?;
        if cyc.contains(&(n - 1)) {
            return Err("pool cycle unexpectedly contains self-loop 2^M - 1".into());
        }
    }

    // Run MWU to obtain dual weights, then certify in exact i64 arithmetic
    let mut w = vec![1.0f64; n];
    let mut y = vec![0i64; pool.len()];
    let mult = (0.08f64).exp();
    for _ in 0..4000 {
        let mut best_i = 0;
        let mut best_c = f64::INFINITY;
        for (i, cyc) in pool.iter().enumerate() {
            let mut c = 0.0;
            for &v in cyc {
                c += w[v];
            }
            if c < best_c {
                best_c = c;
                best_i = i;
            }
        }
        y[best_i] += 1;
        let mut max_w = 0.0f64;
        for &v in &pool[best_i] {
            w[v] *= mult;
            if w[v] > max_w {
                max_w = w[v];
            }
        }
        if max_w > 1e100 {
            let inv = 1.0 / max_w;
            for wi in &mut w {
                *wi *= inv;
            }
        }
    }

    let mut load = vec![0i64; n];
    let mut sum_y = 0i64;
    for (i, cyc) in pool.iter().enumerate() {
        let yi = y[i];
        if yi > 0 {
            sum_y += yi;
            for &v in cyc {
                load[v] += yi;
            }
        }
    }
    let max_load = load.into_iter().max().unwrap_or(0);
    if max_load == 0 {
        return Ok((1, pool.len(), 0, 1));
    }
    let lb = 1 + ((sum_y + max_load - 1) / max_load) as usize;
    Ok((lb, pool.len(), sum_y, max_load))
}

/// Run the complete exact minimum + certified bracket + `p/q` sensitivity experiment.
pub fn run_lyapunov_exact(
    exact_max_m: usize,
    bracket_max_m: usize,
    sensitivity_max_m: usize,
) -> Result<LyapunovExactExperiment, String> {
    let f3_all = run_lyapunov(sensitivity_max_m.max(bracket_max_m).max(exact_max_m))?;

    // Part A: Exact global minimum |S_M*| for 1 <= M <= exact_max_m at 63/100
    let mut exact_rows = Vec::with_capacity(exact_max_m);
    for m in 1..=exact_max_m {
        let n = 1usize << m;
        let f3_row = &f3_all.rows[m - 1];
        let surv = f2_survivors(m);
        let mut is_surv = vec![false; n];
        for &u in &surv {
            is_surv[u] = true;
        }
        let (opt, span, horizon, nodes) = solve_exact_minimum(m, TARGET_P, TARGET_Q)?;
        if opt.len() > f3_row.f3_excluded_count {
            return Err(format!(
                "M={m}: exact optimum {} exceeded heuristic {}",
                opt.len(),
                f3_row.f3_excluded_count
            ));
        }
        let exact_even_count = opt.iter().filter(|&&u| (u & 1) == 0).count();
        let exact_non_survivor_count = opt.iter().filter(|&&u| !is_surv[u]).count();
        exact_rows.push(ExactOptimumRow {
            modulus_bits: m,
            modulus: n,
            f2_survivor_count: surv.len(),
            f3_heuristic_count: f3_row.f3_excluded_count,
            exact_min_count: opt.len(),
            heuristic_gap: f3_row.f3_excluded_count - opt.len(),
            exact_even_count,
            exact_non_survivor_count,
            exact_potential_span: span,
            exact_contraction_horizon: horizon,
            branch_and_cut_nodes: nodes,
            optimal_excluded: opt,
        });
    }

    // Part B: Certified integer dual-LP brackets [LB_M, UB_M] for exact_max_m+1 ..= bracket_max_m
    let mut bracket_rows = Vec::new();
    for m in (exact_max_m + 1)..=bracket_max_m {
        let n = 1usize << m;
        let f3_ub = f3_all.rows[m - 1].f3_excluded_count;
        let (lb, pool_sz, sum_y, max_load) = certify_dual_lower_bound(m, TARGET_P, TARGET_Q)?;
        if lb > f3_ub {
            return Err(format!(
                "M={m}: certified LB {lb} exceeded verified UB {f3_ub}"
            ));
        }
        bracket_rows.push(CertifiedBracketRow {
            modulus_bits: m,
            modulus: n,
            certified_lb: lb,
            f3_ub,
            dual_cycle_count: pool_sz,
            dual_sum_y: sum_y,
            dual_max_load: max_load,
        });
    }

    // Part C1: Exact |S_M*| sensitivity to p/q for M = 4..=7
    let mut exact_sensitivity_rows = Vec::new();
    for m in 4..=7.min(exact_max_m) {
        let n = 1usize << m;
        let mut cells = Vec::with_capacity(SENSITIVITY_TARGETS.len());
        for &(p, q) in &SENSITIVITY_TARGETS {
            let (opt, span, horizon, _) = solve_exact_minimum(m, p, q)?;
            cells.push(SensitivityCell {
                p,
                q,
                excluded_count: opt.len(),
                potential_span: span,
                contraction_horizon: horizon,
            });
        }
        exact_sensitivity_rows.push(ExactSensitivityRow {
            modulus_bits: m,
            modulus: n,
            cells,
        });
    }

    // Part C2: F3 sensitivity to p/q for M = 8..=sensitivity_max_m
    let mut f3_sensitivity_rows = Vec::new();
    for m in 8..=sensitivity_max_m {
        let n = 1usize << m;
        let surv_cnt = f3_all.rows[m - 1].f2_survivor_count;
        let mut cells = Vec::with_capacity(SENSITIVITY_TARGETS.len());
        for &(p, q) in &SENSITIVITY_TARGETS {
            let (excl, span, horizon) = prune_f2_at_target(m, p, q)?;
            cells.push(SensitivityCell {
                p,
                q,
                excluded_count: excl.len(),
                potential_span: span,
                contraction_horizon: horizon,
            });
        }
        f3_sensitivity_rows.push(SensitivityRow {
            modulus_bits: m,
            modulus: n,
            f2_survivor_count: surv_cnt,
            cells,
        });
    }

    Ok(LyapunovExactExperiment {
        schema: "collatz-lab-lyapunov-exact-v1".into(),
        tool_version: env!("CARGO_PKG_VERSION").into(),
        baseline_p: TARGET_P,
        baseline_q: TARGET_Q,
        exact_rows,
        bracket_rows,
        exact_sensitivity_rows,
        f3_sensitivity_rows,
    })
}
