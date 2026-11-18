//! Independent verification and adversarial tests for finite-state modular
//! Lyapunov contraction certificates (F3) on `G_M` modulo `2^M`.

use collatz_lab::lyapunov::{
    build_transition_graph, contraction_horizon, run_lyapunov, solve_integer_potential,
    verify_contraction_target, verify_integer_potential, TARGET_P, TARGET_Q,
};
use num_bigint::BigUint;
use num_traits::One;

#[allow(clippy::manual_div_ceil)]
fn direct_t(n: u64) -> u64 {
    if n.is_multiple_of(2) {
        n / 2
    } else {
        (3 * n + 1) / 2
    }
}

#[test]
fn transition_graph_matches_direct_iteration_exhaustively() {
    for m_bits in 1..=8 {
        let n = 1usize << m_bits;
        let adj = build_transition_graph(m_bits);
        assert_eq!(adj.len(), n);
        for (u, edges) in adj.iter().enumerate() {
            let mut got = [
                (direct_t(u as u64) as usize) & (n - 1),
                (direct_t((u + n) as u64) as usize) & (n - 1),
            ];
            let mut exp = *edges;
            got.sort_unstable();
            exp.sort_unstable();
            assert_eq!(got, exp, "M={m_bits}, u={u}");
        }
    }
}

#[test]
fn finite_state_no_go_on_full_graph_and_minus_one_complement() {
    verify_contraction_target(TARGET_P, TARGET_Q).expect("3^63 < 2^100");
    let exp = run_lyapunov(9).expect("run_lyapunov up to M=9");
    for row in &exp.rows {
        let m = row.modulus_bits;
        let n = row.modulus;
        let adj = build_transition_graph(m);

        // Full graph cannot contract at (99, 100).
        let all_active = vec![true; n];
        assert!(solve_integer_potential(&adj, &all_active, 99, 100).is_none());

        // G_M \ {2^M - 1} is feasible at (M - 1, M) and infeasible at strictly tighter rate.
        let mut minus_one = vec![true; n];
        minus_one[n - 1] = false;
        assert!(solve_integer_potential(&adj, &minus_one, (m - 1) as i64, m as i64).is_some());
        if m >= 2 {
            assert!(
                solve_integer_potential(
                    &adj,
                    &minus_one,
                    (10 * (m - 1) - 1) as i64,
                    (10 * m) as i64
                )
                .is_none(),
                "M={m}: G_M \\ {{2^M - 1}} should not beat (M-1)/M"
            );
        }
        // For M >= 3, (M-1)/M > 1/log2(3), so (63, 100) is impossible on G_M \ {2^M - 1}.
        if m >= 3 {
            assert!(solve_integer_potential(&adj, &minus_one, TARGET_P, TARGET_Q).is_none());
        }
    }
}

#[test]
fn f3_excluded_sets_are_inclusion_minimal_and_telescope_on_actual_orbits() {
    let exp = run_lyapunov(8).expect("run_lyapunov up to M=8");
    // M=4 saves 1 vertex (2 vs 3); M=8 saves 5 vertices (14 vs 19).
    assert_eq!(exp.rows[3].f2_survivor_count, 3);
    assert_eq!(exp.rows[3].f3_excluded_count, 2);
    assert_eq!(exp.rows[7].f2_survivor_count, 19);
    assert_eq!(exp.rows[7].f3_excluded_count, 14);

    for &m in &[4usize, 6, 8] {
        let row = &exp.rows[m - 1];
        let n = 1usize << m;
        let adj = build_transition_graph(m);
        let mut active = vec![true; n];
        for &u in &row.f3_certificate.excluded {
            active[u] = false;
        }
        let phi = solve_integer_potential(&adj, &active, TARGET_P, TARGET_Q)
            .expect("F3 potential must exist");
        let (edges, span) = verify_integer_potential(&adj, &active, &phi, TARGET_P, TARGET_Q)
            .expect("F3 potential must verify");
        assert_eq!(edges, row.f3_certificate.active_edge_count);
        assert_eq!(span, row.f3_potential_span);
        assert_eq!(
            contraction_horizon(TARGET_P, TARGET_Q, span),
            row.f3_contraction_horizon
        );

        // Inclusion minimality: restoring ANY single excluded residue breaks contraction at (63, 100).
        for &u in &row.f3_certificate.excluded {
            active[u] = true;
            assert!(
                solve_integer_potential(&adj, &active, TARGET_P, TARGET_Q).is_none(),
                "M={m}: excluded residue {u} should not be redundant"
            );
            active[u] = false;
        }

        // Direct orbit check: along every maximal segment staying in V_M \ S,
        // verify telescoping inequality and strict coefficient crossing at horizon L_0.
        let mask = (n - 1) as u64;
        let horizon = row.f3_contraction_horizon;
        for seed in 2u64..=5_000 {
            let mut x = seed;
            let mut seg_start_u = (x & mask) as usize;
            let mut seg_len = 0usize;
            let mut seg_r = 0usize;
            for _ in 0..200 {
                let u = (x & mask) as usize;
                if !active[u] {
                    seg_len = 0;
                    seg_r = 0;
                    x = direct_t(x);
                    seg_start_u = (x & mask) as usize;
                    continue;
                }
                if seg_len == 0 {
                    seg_start_u = u;
                }
                let odd = (x & 1) == 1;
                let next_x = direct_t(x);
                let next_u = (next_x & mask) as usize;
                if active[next_u] {
                    seg_len += 1;
                    if odd {
                        seg_r += 1;
                    }
                    assert!(
                        TARGET_Q * (seg_r as i64) + phi[next_u] - phi[seg_start_u]
                            <= TARGET_P * (seg_len as i64),
                        "telescoping bound failed at M={m}, seed={seed}, seg_len={seg_len}"
                    );
                    if seg_len == horizon {
                        let pow3 = BigUint::from(3u32).pow(seg_r as u32);
                        let pow2 = BigUint::one() << seg_len;
                        assert!(
                            pow3 < pow2,
                            "horizon {horizon} failed to force 3^{seg_r} < 2^{seg_len}"
                        );
                    }
                } else {
                    seg_len = 0;
                    seg_r = 0;
                }
                x = next_x;
                if x == 1 {
                    break;
                }
            }
        }
    }
}
