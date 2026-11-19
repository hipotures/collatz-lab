//! Independent checks for the monotone lift chain of F3 excluded sets.

use collatz_lab::lyapunov::{
    build_transition_graph, solve_integer_potential, verify_integer_potential, TARGET_P, TARGET_Q,
};
use collatz_lab::lyapunov_exact::solve_exact_minimum;
use collatz_lab::lyapunov_lift::{lift_excluded_set, run_lyapunov_lift, LIFT_MAX_SUPPORTED_M};

#[allow(clippy::manual_div_ceil)]
fn direct_t(n: u64) -> u64 {
    if n.is_multiple_of(2) {
        n / 2
    } else {
        (3 * n + 1) / 2
    }
}

fn active_from(n: usize, excluded: &[usize]) -> Vec<bool> {
    let mut active = vec![true; n];
    for &u in excluded {
        active[u] = false;
    }
    active
}

/// Reduction modulo `2^M` maps every edge of `G_{M+1}` to an edge of `G_M`
/// (checked against direct iteration of `T`, not against the graph builder).
#[test]
fn reduction_is_an_odd_label_preserving_homomorphism() {
    for m in 1..=11usize {
        let n_small = 1u64 << m;
        let n_big = 1u64 << (m + 1);
        for u in 0..n_big {
            let small_u = u % n_small;
            assert_eq!(u & 1, small_u & 1, "odd label must be preserved");
            let small_targets: Vec<u64> = (0..2)
                .map(|t| direct_t(small_u + n_small * t) % n_small)
                .collect();
            for t in 0..2 {
                let v = direct_t(u + n_big * t) % n_big;
                assert!(
                    small_targets.contains(&(v % n_small)),
                    "M={m}: edge {u}->{v} does not project to an edge of G_M"
                );
            }
        }
    }
}

/// Lifting each exact optimum `S_M*` gives a feasible set of size `2|S_M*|` at
/// depth `M + 1`, with the lifted potential valid edge by edge.
#[test]
fn lifted_exact_optima_are_feasible() {
    for m in 1..=7usize {
        let (opt, _, _, _) = solve_exact_minimum(m, TARGET_P, TARGET_Q).expect("exact");
        let adj = build_transition_graph(m);
        let phi = solve_integer_potential(&adj, &active_from(1 << m, &opt), TARGET_P, TARGET_Q)
            .expect("optimum feasible");
        let (lifted, lifted_phi) = lift_excluded_set(m + 1, &opt, &phi);
        assert_eq!(lifted.len(), 2 * opt.len());
        let big = build_transition_graph(m + 1);
        let active = active_from(1 << (m + 1), &lifted);
        verify_integer_potential(&big, &active, &lifted_phi, TARGET_P, TARGET_Q)
            .unwrap_or_else(|e| panic!("M={m}: lifted potential invalid: {e}"));
        // And the exact optimum at M + 1 respects the lifting bound.
        let (next, _, _, _) = solve_exact_minimum(m + 1, TARGET_P, TARGET_Q).expect("exact");
        assert!(next.len() <= lifted.len(), "M={m}: |S_(M+1)*| > 2|S_M*|");
    }
}

#[test]
fn lift_chain_is_verified_monotone_and_reproducible() {
    let outcome = run_lyapunov_lift(12, 6).expect("lift chain");
    let again = run_lyapunov_lift(12, 6).expect("lift chain rerun");
    assert_eq!(outcome, again, "lift chain must be deterministic");

    // Regression values: exact for M <= 6 (cross-checked with lyapunov-exact),
    // greedy upper bounds above.
    let expected = [1usize, 1, 2, 2, 4, 5, 8, 14, 20, 37, 59, 110];
    let mut prev = 1usize; // the set {0} modulo 1
    for (row, &exp) in outcome.rows.iter().zip(expected.iter()) {
        let m = row.modulus_bits;
        let n = 1usize << m;
        assert_eq!(row.chain_count, exp, "M={m}: chain count changed");
        assert_eq!(row.chain_excluded.len(), row.chain_count);
        assert!(
            row.chain_excluded.contains(&(n - 1)),
            "M={m}: 2^M - 1 must stay excluded"
        );
        assert!(row.chain_count <= 2 * prev, "M={m}: density increased");
        assert_eq!(row.lifted_count, 2 * prev);
        if let Some(s) = row.survivor_heuristic_count {
            assert!(row.chain_count <= s);
        }
        if let Some(e) = row.exact_count {
            assert_eq!(row.chain_count, e, "M={m}: chain must equal the exact seed");
        }
        // Independent re-verification from scratch.
        let adj = build_transition_graph(m);
        let active = active_from(n, &row.chain_excluded);
        let phi = solve_integer_potential(&adj, &active, TARGET_P, TARGET_Q)
            .unwrap_or_else(|| panic!("M={m}: chain element infeasible"));
        let (edges, span) =
            verify_integer_potential(&adj, &active, &phi, TARGET_P, TARGET_Q).expect("verify");
        assert_eq!(edges, row.chain_active_edges);
        assert_eq!(span, row.chain_potential_span);
        prev = row.chain_count;
    }
}

#[test]
fn lift_chain_rejects_out_of_range_depth() {
    assert!(run_lyapunov_lift(0, 0).is_err());
    assert!(run_lyapunov_lift(LIFT_MAX_SUPPORTED_M + 1, 0).is_err());
}
