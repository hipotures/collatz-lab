//! Human-readable summary of one bounded experiment.
//!
//! The output is a pure function of the experiment outcome (no timestamps or
//! host details), so a rerun with the same parameters reproduces it exactly.

use std::fmt::Write as _;

use crate::envelope::{EnvelopeExperiment, Witness};
use crate::hypothesis::{ExperimentOutcome, FailureCase, Status};
use crate::mahler::MahlerExperiment;

fn abbreviate_decimal(text: &str, max_len: usize) -> String {
    if text.len() <= max_len {
        text.to_string()
    } else {
        let head = &text[..12];
        let tail = &text[text.len() - 12..];
        format!("{head}...{tail} ({} digits)", text.len())
    }
}

fn format_poly(coeffs: &[String]) -> String {
    let mut terms = Vec::new();
    for (deg, c) in coeffs.iter().enumerate() {
        if c == "0" {
            continue;
        }
        let term = match deg {
            0 => c.clone(),
            1 => {
                if c == "1" {
                    "z".to_string()
                } else if c == "-1" {
                    "-z".to_string()
                } else {
                    format!("{c}*z")
                }
            }
            _ => {
                if c == "1" {
                    format!("z^{deg}")
                } else if c == "-1" {
                    format!("-z^{deg}")
                } else {
                    format!("{c}*z^{deg}")
                }
            }
        };
        terms.push(term);
    }
    if terms.is_empty() {
        "0".to_string()
    } else {
        terms.join(" + ").replace("+ -", "- ")
    }
}

/// Deterministic Phase 3 report for the aperiodic survivor itinerary and Mahler reduction.
pub fn render_mahler(outcome: &MahlerExperiment) -> String {
    let mut out = String::from(
        "# Phase 3: aperiodic survivor itinerary and exact 2-adic Mahler reduction\n\n\
         Generated deterministic evidence for the fixed point `w = lim_{j -> infinity} mu^j(1)` \
         of the uniform morphism `mu(1) = 1110`, `mu(0) = 1101` under the accelerated Collatz map \
         `T(n) = n/2` (even), `(3n+1)/2` (odd). All arithmetic uses exact arbitrary-precision \
         integers (`BigUint` and `BigInt`); no floating point is used anywhere.\n\n\
         Nothing below claims originality over Bernstein-Lagarias (1996), Lagarias (1990), \
         Terras (1976), or `msharpe248/collatz`, and nothing claims a proof of CST or the \
         Collatz conjecture. See [the mathematical memo](../infinite-itineraries.md) for \
         complete proofs, derivations, and literature citations.\n\n\
         Reproduce this summary and `evidence.json` from the repository root with:\n\n\
         ```text\ncargo run --locked --release -- mahler --out-dir research/mahler\n```\n\n\
         ## Epistemic status summary\n\n\
         | claim | status |\n\
         |---|---|\n",
    );
    let statuses = [
        (
            "All-prefix coefficient survival `3^(r_k) > 2^k` for all `k >= 1`",
            outcome.prefix_survival_status,
        ),
        (
            "Aperiodicity of `w` (`w` is not eventually periodic)",
            outcome.aperiodicity_status,
        ),
        (
            "Mahler functional equation and 2-adic identity `x(w) = -23/11 + (4/27)*F_2(16/27)`",
            outcome.mahler_reduction_status,
        ),
        (
            "Five-way modular checkpoint agreement up to `2^1024` and periodic control `-19/11`",
            outcome.finite_checkpoints_status,
        ),
        (
            "Uncancelled polynomial Mahler denominator keeps `D_k` odd for `B(z) = z^2 - z^3`",
            outcome.uncancelled_tower_status,
        ),
        (
            "Bounded exact Padé table (`1 <= m <= 16`) and `a_k^2`-cancelled height ledger",
            outcome.cancelled_pade_exploration_status,
        ),
        (
            "All shifts `sigma^t(w)` (`t >= 0`) and general divergent positive orbits",
            outcome.shift_and_general_divergent_status,
        ),
    ];
    for (claim, status) in statuses {
        let _ = writeln!(out, "| {claim} | `{}` |", status.label());
    }

    out.push_str(
        "\n## Five-way 2-adic checkpoint verification (`w = lim mu^j(1)`)\n\n\
         At each `K`, the unique compatible residue `x_K in [0, 2^K)` is computed five ways: \
         (1) prefix affine map + modular inverse, (2) cylinder Hensel lifting, (3) parity-position \
         inverse sum `-sum_{i=0}^{r_K-1} 2^(d_i) / 3^(i+1) (mod 2^K)`, (4) the Mahler reduction \
         `-23/11 + (4/27)*F_2(16/27) (mod 2^K)`, and (5) direct iteration of `T` for `K` steps on \
         `x_K`. In addition, the repaired seed normalization `D_0 = 11, u_0 = 27*(11*x_K + 23)/4` \
         is checked on each actual checkpoint seed `x_K` across `1 <= L <= K/4 - 1` blocks at level 0 \
         and `1 <= L <= (K/4 - 1)/4` blocks at level 1 (while recording that the unnormalized \
         `(11*x_K + 23)/4` gives `1 != 11 (mod 16)` at `L = 1`). Full decimal values are recorded in `evidence.json`.\n\n\
         | K | r_K | prefixes survive | F_2(16/27) mod 2^K | residue x_K mod 2^K | unnorm / repaired u_0 mod 16 | repaired L_0 / L_1 blocks | 5-way + Mahler eq + cocycle |\n\
         |---|---|---|---|---|---|---|---|\n",
    );
    for row in &outcome.checkpoints {
        let f2_str = abbreviate_decimal(&row.f2_mod_2k.to_string(), 28);
        let res_str = abbreviate_decimal(&row.residue_affine_inverse.to_string(), 28);
        let all_ok = row.all_prefixes_survive
            && row.f2_functional_equation_matches
            && row.block_cocycle_matches
            && row.direct_iteration_matches
            && row.repaired_delta0_divisible_by_a0_sq
            && row.residue_affine_inverse == row.residue_cylinder_lift
            && row.residue_affine_inverse == row.residue_parity_positions
            && row.residue_affine_inverse == row.residue_mahler_reduction;
        let _ = writeln!(
            out,
            "| {} | {} | {} | `{}` | `{}` | `{} != 11` / `{} == 11` | `1..={}` / `1..={}` | {} |",
            row.k_bits,
            row.odd_steps,
            if row.all_prefixes_survive {
                "yes"
            } else {
                "no"
            },
            f2_str,
            res_str,
            row.unnormalized_u0_mod16,
            row.repaired_u0_mod16,
            row.repaired_level0_verified_blocks,
            row.repaired_level1_verified_blocks,
            if all_ok { "exact match" } else { "MISMATCH" },
        );
    }

    out.push_str(
        "\n## Periodic control `(1110)^infinity` (`x = -19/11`)\n\n\
         Every finite prefix of `(1110)^infinity` is realized by positive integers `n_K >= 2` \
         with `T^K(n_K) > n_K`, even though the unique 2-adic limit is the negative rational \
         `-19/11`. Every `n_K` therefore diverges from `(1110)^infinity` at a finite step `k >= K`.\n\n\
         | K | r_K | least positive seed n_K >= 2 | 11*n_K + 19 == 0 (mod 2^K) | T^K(n_K) > n_K | first divergence step |\n\
         |---|---|---|---|---|---|\n",
    );
    for row in &outcome.periodic_control {
        let seed_str = abbreviate_decimal(&row.positive_seed.to_string(), 28);
        let _ = writeln!(
            out,
            "| {} | {} | `{}` | {} | {} | {} |",
            row.k_bits,
            row.odd_steps,
            seed_str,
            if row.matches_minus_19_over_11 {
                "yes"
            } else {
                "no"
            },
            if row.iterated_value_exceeds_seed {
                "yes"
            } else {
                "no"
            },
            row.first_divergence_step,
        );
    }

    let t = &outcome.tower_summary;
    let _ = write!(
        out,
        "\n## Mahler tower structure, repaired `(u_0, D_0)` seed normalization, and `B(z) = z^2 - z^3`\n\n\
         - Power-series identity `(1 - z^4)(F(z) - (z^2 - z^3)F(z^4)) = 1 + z + z^3` verified to degree: `{}`\n\
         - Homogenised prefix recurrence `preS(a, b, 4L)` verified for block counts: `1..={}`\n\
         - Vanishing order of `B(z) = z^2(1 - z)` at `z = 0`: `{}`\n\
         - Base-case regression on unnormalized `u_0^old = (11*x_K + 23)/4` (`D_0 = {}`): `u_0^old mod 16 = {} != 11 = D_0*preS(16, 27, 1) mod 16` and `Delta_0^old mod 256 = {} != 0` (fails at `L = 1`)\n\
         - Repaired seed normalization `D_0 = {}`, `u_0 = 27*(11*x_K + 23)/4` on actual checkpoint seed `x_1024`: `u_0 mod 16 = {} == 11`, verified across `1..={}` blocks at level 0, `1..={}` blocks at level 1 (`D_1 = {}`, odd: `{}`), and `1..={}` blocks at level 2 (`D_2 = {}`, odd: `{}`)\n\
         - 2-adic valuation `v_2(D_1)` of the **uncancelled** polynomial tower denominator: `{}` (`D_1` is even, refuting `Odd D_k` without `a_k^2` cancellation)\n\
         - Exact integer divisibility `a_0^2 | Delta_0` and `a_1^2 | Delta_1` in the **`a_k^2`-cancelled** seed tower: `{}` / `{}`\n\
         - Corrected degree-4 linear form `E_k = D_k*P_0(a_k, b_k) + u_k*P_1(a_k, b_k)` on `x_1024` seed tower: `v_2(E_0) = {}`, `v_2(E_1) = {}`, `v_2(E_2) = {}` (`= 56 * 4^k`)\n\
         - Explicit uniform archimedean height step `H_{{k+1}} <= b_k^7 * H_k` and `|E_k| < 3*(|u_0| + D_0)*3^(19*4^k)` verified on `k = 0, 1, 2`: `{}` (`2^56 = {}` vs `3^19 = {}`)\n\
         - Naive series truncation Liouville exponent `< 1` (`16^L < 27^L`): `{}`\n\
         - Degree-1 Padé (`m = 1`, `N = 3`) in `a_k^2`-cancelled ledger: `2^44 = {}` vs `3^30 = {}` (closes: `{}`)\n\
         - Degree-4 Padé (`m = 4`, `N = 14`) coarse step gain vs cost: `2^56 = {}` vs `16 * 27^7 = {}` (closes: `{}`)\n\n",
        t.functional_equation_verified_degree,
        t.homogenised_prefix_verified_blocks,
        t.b_poly_zero_order_at_origin,
        t.seed_d0,
        t.unnormalized_u0_mod16_at_checkpoints,
        t.unnormalized_delta0_mod_a0_sq,
        t.seed_d0,
        t.repaired_u0_mod16_at_checkpoints,
        t.level0_seed_verified_blocks,
        t.level1_transport_verified_blocks,
        t.cancelled_d1,
        if t.cancelled_d1_is_odd { "yes" } else { "no" },
        t.level2_transport_verified_blocks,
        abbreviate_decimal(&t.cancelled_d2.to_string(), 28),
        if t.cancelled_d2_is_odd { "yes" } else { "no" },
        t.uncancelled_d1_two_adic_valuation,
        if t.cancelled_delta0_divisible_by_a0_sq {
            "yes"
        } else {
            "no"
        },
        if t.cancelled_delta1_divisible_by_a1_sq {
            "yes"
        } else {
            "no"
        },
        t.degree4_e0_two_adic_valuation,
        t.degree4_e1_two_adic_valuation,
        t.degree4_e2_two_adic_valuation,
        if t.explicit_height_step_verified {
            "yes"
        } else {
            "no"
        },
        t.degree4_valuation_base_2_pow_56,
        t.degree4_explicit_height_base_3_pow_19,
        if t.truncation_exponent_lt_one {
            "yes"
        } else {
            "no"
        },
        t.degree1_gain_power_of_two,
        t.degree1_cost_power_of_three,
        if t.degree1_closes_ledger { "yes" } else { "no" },
        t.degree4_coarse_gain_2_pow_56,
        t.degree4_coarse_cost_16_mul_27_pow_7,
        if t.degree4_closes_cancelled_ledger {
            "yes"
        } else {
            "no"
        },
    );

    out.push_str(
        "## Bounded exact Padé auxiliary-form table (`1 <= m <= 16`)\n\n\
         For each degree bound `m`, the nullspace of the `(2m + 1) x (2m + 2)` integer Hankel/Toeplitz \
         system for `p_0(z) + p_1(z)*F(z) = O(z^(2m+1))` is solved by exact fraction-free `BigInt` \
         row reduction, normalized to primitive integer coefficients, and stripped of any common \
         `z^s` shift (`reduced deg`).\n\n\
         | m | null dim | shift s | red deg | singular block | reduced p_0(z) | reduced p_1(z) | L_1 | L_inf | red order N | lead coeff c | v_2(c) | closes cancelled ledger | closes coarse ledger |\n\
         |---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n",
    );
    for row in &outcome.pade_candidates {
        let p0_poly = abbreviate_decimal(&format_poly(&row.reduced_p0_coeffs), 32);
        let p1_poly = abbreviate_decimal(&format_poly(&row.reduced_p1_coeffs), 32);
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} | `{}` | `{}` | {} | {} | {} | `{}` | {} | `2^{} vs 3^{}` ({}) | {} |",
            row.degree_bound,
            row.nullspace_dim_at_2m_plus_1,
            row.common_z_shift,
            row.reduced_max_degree,
            if row.in_singular_block { "yes" } else { "no" },
            p0_poly,
            p1_poly,
            row.l1_height,
            row.linf_height,
            row.reduced_vanishing_order,
            row.leading_coeff,
            row.leading_coeff_v2,
            row.cancelled_tower_gain_exp2,
            row.cancelled_tower_cost_exp3,
            if row.closes_cancelled_tower_asymptotic {
                "yes"
            } else {
                "no"
            },
            if row.closes_coarse_integer_ledger {
                "yes"
            } else {
                "no"
            },
        );
    }

    out.push_str("\n## Unresolved proof obligations\n\n");
    for item in &outcome.unresolved_obligations {
        let _ = writeln!(out, "- {item}");
    }
    out
}

/// Deterministic Phase 2 report. The reproduction command always names the
/// canonical artifact directory, even if the CLI writes a scratch copy.
pub fn render_envelope(outcome: &EnvelopeExperiment) -> String {
    let mut out = String::from(
        "# Phase 2: tightness of Terras's mini-max envelope\n\n\
         Generated finite engineering/mathematical comparison for the accelerated map \
         `T(n)=n/2` (even), `(3n+1)/2` (odd). No originality claim, no all-`r` theorem, \
         and no proof of CST or Collatz is asserted. P1a is **refuted**; P1b remains open.\n\n\
         Reproduce this table and `evidence.json` from the repository root with:\n\n\
         ```text\ncargo run --locked --release -- envelope --out-dir research/envelope\n```\n\n\
         ## Definitions and scope\n\n\
         Exactly `1 <= r <= 12`, with `k = bit_length(3^r) <= 20`. Each family contains \
         every parity word whose first coefficient crossing is at length `k` and has \
         `r` odd steps. Write `T^k(n)=(3^r*n+c)/2^k`, `d=2^k-3^r`, and let `m` be \
         the least class member **at least 2**. The word `10` has residue 1 but `m=5`.\n\n\
         `C_r=max c`, `m_r=min m`, `R_r=max c/(d*m)`, `U_r=C_r/(d*m_r)`, and \
         `E_r=U_r/R_r`. If `R_r=0`, `E_r` and its comparison with 2 are **N/A** \
         (JSON `null`); no value is imputed. All fractions are reduced using gcd; \
         all rankings and comparisons use BigUint cross products.\n\n\
         ## Exhaustive results\n\n\
         Each extremum cell lists **all** tied words as `word (m, c)` in lexicographic \
         order, followed by the number of ties. A single listed word means a unique \
         extremizer. Counts, margins, normalized residues and the independent Terras \
         offsets are also recorded in `evidence.json`; arbitrary-size integers are \
         decimal strings.\n\n\
         | r | k | count | C_r words (m, c); ties | m_r words (m, c); ties | R_r words (m, c); ties | R_r | U_r | E_r | E_r <= 2 |\n\
         |---|---|---|---|---|---|---|---|---|---|\n",
    );
    let witnesses = |values: &[Witness]| {
        let words: Vec<_> = values
            .iter()
            .map(|w| format!("`{}` ({}, {})", w.parity, w.m, w.c))
            .collect();
        format!("{}; {} tie(s)", words.join("<br>"), values.len())
    };
    for row in &outcome.rows {
        let e = row
            .e_ratio
            .as_ref()
            .map_or_else(|| "N/A".into(), ToString::to_string);
        let comparison = match row.e_le_two {
            Some(true) => "yes",
            Some(false) => "no",
            None => "N/A",
        };
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
            row.r,
            row.k,
            row.family_count,
            witnesses(&row.max_c_witnesses),
            witnesses(&row.min_m_witnesses),
            witnesses(&row.max_ratio_witnesses),
            row.r_ratio,
            row.u_ratio,
            e,
            comparison,
        );
    }
    out.push_str("\n## Finite prediction E_r <= 2\n\n");
    if let Some(r) = outcome.first_counterexample_r {
        let row = outcome
            .rows
            .iter()
            .find(|row| row.r == r)
            .expect("counterexample row");
        let e = row.e_ratio.as_ref().expect("counterexample ratio");
        let _ = writeln!(
            out,
            "**refuted on the tested domain**: the first counterexample is `r={r}`, \
             `k={}`, with `E_r={e} > 2`. This refutes only the finite prediction. \
             All twelve families were still evaluated.",
            row.k
        );
    } else {
        out.push_str(
            "**verified-for-finite-domain**: `E_r <= 2` for every tested `r` where \
             `R_r > 0`. This is only a bounded observation on `1 <= r <= 12`, \
             with no extrapolation to larger `r`.\n",
        );
    }
    out.push_str(
        "\nNeither outcome proves P1b or any infinite-family statement.\n\n\
         ## Checks and stopping behavior\n\n\
         Each family count agrees with both independent recurrences in \
         `src/counting.rs`. The enumerated maximum offset agrees with Terras's \
         independent extremal-word recurrence: start with power 1 and offset 0; \
         at positions `i=0..k-2` choose odd iff `3^(odd count so far) < 2^(i+1)`, \
         update `c <- 3*c+2^i` on odd steps, and append a final zero. This is the \
         construction of Theorems 2.4 and 2.6 described in \
         [the primary-source audit](../literature-cst.md).\n\n\
         Every enumerated word, including every reported extremizer, has its \
         modular-inverse residue checked against the independent lifting construction. \
         The independent certificate verifier rederives its closed-form affine offset \
         and checks two members by direct iteration. Its least member `m >= 2` is \
         additionally checked by direct iteration for its parities and affine identity. \
         The independent test in `tests/envelope.rs` scans a full residue period by \
         direct iteration and rechecks all extrema, ties and exact fractions.\n\n\
         P1a is never used to rank classes. At `r=6`, `1111101000` has \
         `(m,c)=(287,697)`, while `1101110100` has `(347,989)` and \
         `989/(295*347) > 697/(295*287)` (cross-product difference 12385280).\n\n\
         The command has fixed bounds and terminates at `r=12`, or immediately on \
         the first invariant failure. An `E_r>2` is a result, not an invariant failure. \
         No artifact is replaced until all mathematical checks pass. It retains one \
         family at a time (at most 2652 classes); the full run checks 4403 classes. \
         Runtime in milliseconds is printed to stderr and omitted from these \
         deterministic artifacts. See the repository README for measured performance.\n",
    );
    out
}

fn describe_case(case: &FailureCase) -> String {
    match case {
        FailureCase::NoDescentWithinWindow { n, window } => {
            format!("n = {n}: T^j(n) >= n for all 1 <= j <= {window}")
        }
        FailureCase::OddMajorityDescent { parity, witness } => {
            format!(
                "prefix {parity} descends although odd steps are a majority; witness n = {witness}"
            )
        }
        FailureCase::ThresholdException { parity, n } => {
            format!("prefix {parity}: member n = {n} does not descend")
        }
    }
}

/// Renders the Markdown summary.
pub fn render_summary(outcome: &ExperimentOutcome, command: &str) -> String {
    let p = &outcome.params;
    let c = &outcome.cover;
    let mut out = String::new();
    // Writing to a String cannot fail.
    let _ = write!(
        out,
        "# Bounded experiment summary\n\n\
         This file is generated. It reports a **bounded** experiment on the accelerated \
         Collatz map `T`. Nothing below is a proof, a novelty claim, a completeness claim \
         or a counterexample to the Collatz conjecture.\n\n\
         Reproduce with:\n\n```text\n{command}\n```\n\n\
         ## Parameters\n\n\
         | parameter | value |\n|---|---|\n\
         | seed | {} |\n| cover depth | {} |\n| exhaustive limit | {} |\n\
         | candidate window | {} |\n| bit-length factor | {} |\n\
         | sample size | {} integers of {} bits |\n| sample step budget | {} |\n\
         | tool version | {} |\n\n",
        p.seed,
        p.depth,
        p.limit,
        p.window,
        p.bits_factor,
        p.samples,
        p.sample_bits,
        p.max_steps,
        env!("CARGO_PKG_VERSION"),
    );

    out.push_str(
        "## Status legend\n\n\
         - `proven-by-algebra`: follows from an explicit algebraic argument; finite checks are only a cross-check.\n\
         - `verified-for-finite-domain`: exhaustively checked on the stated finite domain and nowhere else.\n\
         - `experimentally-observed`: seen on a sample; not exhaustive.\n\
         - `conjectured`: open; recorded as a proof obligation, with no claim of truth.\n\
         - `refuted`: false as stated; counterexamples were re-checked by the independent verifier.\n\n\
         ## Hypotheses\n\n| id | status | domain | failure cases |\n|---|---|---|---|\n",
    );
    for entry in &outcome.entries {
        let _ = writeln!(
            out,
            "| `{}` | {} | {} | {} |",
            entry.hypothesis_id,
            entry.status.label(),
            entry.domain,
            entry.failure_cases.len()
        );
    }

    for entry in &outcome.entries {
        let _ = write!(
            out,
            "\n### `{}` ({})\n\n**Statement.** {}\n\n**Domain.** {}\n",
            entry.hypothesis_id,
            entry.status.label(),
            entry.hypothesis,
            entry.domain
        );
        if !entry.evidence.is_empty() {
            out.push_str("\n**Evidence.**\n\n");
            for line in &entry.evidence {
                let _ = writeln!(out, "- {line}");
            }
        }
        if !entry.failure_cases.is_empty() {
            let heading = if entry.status == Status::Refuted {
                "Counterexamples (verified by direct iteration)"
            } else {
                "Failure cases of the bounded statement"
            };
            let _ = write!(out, "\n**{heading}.**\n\n");
            for case in &entry.failure_cases {
                let _ = writeln!(out, "- {}", describe_case(case));
            }
        }
        if !entry.proof_obligations.is_empty() {
            out.push_str("\n**Open proof obligations.**\n\n");
            for line in &entry.proof_obligations {
                let _ = writeln!(out, "- {line}");
            }
        }
    }

    let _ = write!(
        out,
        "\n## First-descent cover to depth {depth}\n\n\
         - certified first-descent prefixes: {} (longest has length {})\n\
         - residue classes modulo 2^{depth} covered: {} of {}\n\
         - **uncovered classes modulo 2^{depth}: {}** (each has `2^j < 3^(r_j)` for every `1 <= j <= {depth}`)\n",
        c.certificates,
        c.max_certificate_steps,
        c.covered_classes,
        c.total_classes,
        c.uncovered,
        depth = c.depth,
    );
    if c.certificates_with_exceptions.is_empty() {
        out.push_str("- certificates with positive members below threshold: none\n");
    } else {
        out.push_str("- certificates with positive members below threshold:\n");
        for line in &c.certificates_with_exceptions {
            let _ = writeln!(out, "  - {line}");
        }
    }
    out.push_str(
        "\nEvery certificate was re-derived by the independent verifier (integer arithmetic \
         and direct iteration only). Each certificate is conditional: it asserts one descent \
         step count for one residue class above an explicit threshold.\n\n\
         ## What this does not show\n\n\
         - The uncovered set is non-empty at every depth: the class `-1 (mod 2^depth)` is \
         never certified (proven by algebra, see `universal-window`). A covered fraction \
         close to 1 is therefore not progress toward a proof by itself.\n\
         - A descent certificate gives `T^k(n) < n` once; turning a full family of such \
         statements into convergence needs every class covered and every exception handled, \
         which no finite depth provides.\n\
         - Finite searches and samples cover only their stated domains.\n",
    );
    out
}
