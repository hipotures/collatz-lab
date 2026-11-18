//! Independent verification tests for exact minimum excluded sets `|S_M*|`,
//! certified dual-LP lower bounds, and `p/q` sensitivity in F3.

use collatz_lab::lyapunov::{
    build_transition_graph, solve_integer_potential, verify_integer_potential, TARGET_P, TARGET_Q,
};
use collatz_lab::lyapunov_exact::{
    certify_dual_lower_bound, prune_f2_at_target, solve_exact_minimum,
};

/// Exhaustively check that NO subset of size `k` (containing `n - 1`) makes `G_M`
/// feasible at `(p, q)`. Used to independently verify `|S_M*|` on small `M <= 4`.
fn exists_feasible_subset_of_size(adj: &[[usize; 2]], k: usize, p: i64, q: i64) -> bool {
    let n = adj.len();
    assert!(k >= 1);
    let mut active = vec![true; n];
    active[n - 1] = false;
    fn rec(
        adj: &[[usize; 2]],
        active: &mut [bool],
        start: usize,
        rem: usize,
        p: i64,
        q: i64,
    ) -> bool {
        if rem == 0 {
            return solve_integer_potential(adj, active, p, q).is_some();
        }
        let limit = adj.len() - 1;
        if start + rem > limit {
            return false;
        }
        for u in start..limit {
            active[u] = false;
            if rec(adj, active, u + 1, rem - 1, p, q) {
                return true;
            }
            active[u] = true;
        }
        false
    }
    rec(adj, &mut active, 0, k - 1, p, q)
}

#[test]
fn exact_minima_m1_to_m7_and_brute_force_verification_m1_to_m4() {
    let expected = [1usize, 1, 2, 2, 4, 5, 8];
    for (idx, &exp_min) in expected.iter().enumerate() {
        let m = idx + 1;
        let n = 1usize << m;
        let adj = build_transition_graph(m);
        let (opt, span, _horizon, _nodes) =
            solve_exact_minimum(m, TARGET_P, TARGET_Q).expect("exact solve");
        assert_eq!(opt.len(), exp_min, "M={m}: unexpected exact |S_M*|");

        // Independent edge-by-edge potential verification.
        let mut active = vec![true; n];
        for &u in &opt {
            active[u] = false;
        }
        let phi = solve_integer_potential(&adj, &active, TARGET_P, TARGET_Q)
            .expect("optimal set must be feasible");
        let (_, checked_span) =
            verify_integer_potential(&adj, &active, &phi, TARGET_P, TARGET_Q).expect("edge check");
        assert_eq!(checked_span, span);

        // Exhaustive brute-force impossibility of size `exp_min - 1` for M <= 4.
        if m <= 4 && exp_min >= 2 {
            assert!(
                !exists_feasible_subset_of_size(&adj, exp_min - 1, TARGET_P, TARGET_Q),
                "M={m}: found feasible subset smaller than {exp_min}"
            );
        }
    }
}

#[test]
fn certified_dual_lower_bounds_are_sound_through_m9() {
    let exact_m7 = solve_exact_minimum(7, TARGET_P, TARGET_Q).unwrap().0.len();
    let (lb7, _, _, _) = certify_dual_lower_bound(7, TARGET_P, TARGET_Q).unwrap();
    assert!(lb7 <= exact_m7 && lb7 >= 5);

    let (lb9, cycles9, sum_y9, max_load9) =
        certify_dual_lower_bound(9, TARGET_P, TARGET_Q).unwrap();
    assert!(cycles9 > 0 && sum_y9 > 0 && max_load9 > 0);
    assert!(
        (14..=20).contains(&lb9),
        "M=9 certified LB={lb9} out of expected [14, 20]"
    );
}

#[test]
fn pq_sensitivity_preserves_excluded_count_and_increases_horizon() {
    let targets = [(63i64, 100i64), (41, 65), (94, 149)];
    for m in 8..=10 {
        let mut counts = Vec::new();
        let mut horizons = Vec::new();
        for &(p, q) in &targets {
            let (excl, _span, horizon) = prune_f2_at_target(m, p, q).expect("prune at target");
            counts.push(excl.len());
            horizons.push(horizon);
        }
        assert!(
            counts.windows(2).all(|w| w[0] == w[1]),
            "M={m}: expected identical |S_M| across tight targets, got {counts:?}"
        );
        assert!(
            horizons.windows(2).all(|w| w[0] < w[1]),
            "M={m}: expected strictly increasing horizon L_0 as p/q -> 1/log2(3), got {horizons:?}"
        );
    }
}
