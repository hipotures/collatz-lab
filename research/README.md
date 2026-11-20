# Research notes

| file | content |
|---|---|
| [`phase13-progress.md`](phase13-progress.md) | Phase 13 resume point, exact pushed checkpoints, validation and remaining rational-height questions |
| [`phase13-prior-art.md`](phase13-prior-art.md) | Primary-source comparison: approximation lattices, odd-denominator reconstruction, 2-adic complexity and Collatz shadows |
| [`phase13-theory.md`](phase13-theory.md) | Exact finite heights and substituted rational shadows; integer bounds, 3-adic non-cancellation, exact shadow minima/plateaux and two-shadow dichotomy in Lean; written nonconvergence and unconditional `B >= (1-c)/(1+5c)` deductions |
| [`phase13-experiments.md`](phase13-experiments.md) | 16,384-bit profiles, 1,691 independent minimum certificates, benchmarks and falsified conjectures |
| [`phase13/README.md`](phase13/README.md) | Algorithms, exact certificate format and bounded reproduction commands |
| [`phase13/overnight-summary.md`](phase13/overnight-summary.md) | Phase 13 overnight handoff: 24 exact height minima, 16 certified transitions, raw shadows `k=0..8`, corrected provenance (issues #30, #33) |
| [`phase13/tail-gcd-primes.md`](phase13/tail-gcd-primes.md) | Phase 13 follow-up: bounded resonant-prime scan (`p <= 100,000`, `k <= 200`; `p <= 10,000`, `k <= 1,000`) and 13 certified infinite modular cycles for `gcd(|P_k|, Q_k)` |
| [`phase13/intermediate-approximants.md`](phase13/intermediate-approximants.md) | Phase 13 follow-up: dense exact intermediate best approximants across `(L_k, L_{k+1}]` for `k = 0..3` (`12 <= N <= 14,515`), plateau entries, and certified deepest dips |
| [`phase13/morphism-shadows.md`](phase13/morphism-shadows.md) | Phase 13 follow-up: cross-morphism rational shadows and 3-adic non-cancellation for `phase11-110` (`c = (1/4) log2(3)`), `phase11-1011` (`c = (1/5) log2(3)`), and equal-weight controls |
| [`phase13/prime-obstructions.md`](phase13/prime-obstructions.md) | Phase 13 follow-up: exact 2-primary / 3-primary power-residue obstructions (`p == 5 mod 12` excluded for all `k >= 1`; `p = 10597 == 1 mod 12` witness at `k = 677`) and the post-identity abelian trap |
| [`phase13-independent-referee-report.md`](phase13-independent-referee-report.md) | Independent Phase 13 referee: nonconvergence PASS; identified the stale overnight provenance later repaired in #33 |
| [`phase12-findings.md`](phase12-findings.md) | Phase 12: no new rational exclusion; length-six candidate covered by prior art; kernel-checked two-return no-go |
| [`phase12-prior-art-matrix.md`](phase12-prior-art-matrix.md) | Phase 12 source coverage matrix with exact versions and proof-access limits |
| [`phase12-independent-referee-report.md`](phase12-independent-referee-report.md) | Independent Phase 12 referee report (PASS for the exact statements) |
| [`phase12-progress.md`](phase12-progress.md) | Phase 12 checkpoints and resumption |
| [`phase11-findings.md`](phase11-findings.md) | Phase 11: contraction iff subcritical, non-contracting `110/111` and `1011/1111` exclusions, repeated-square criterion, prior-art overlap |
| [`phase11-independent-referee-report.md`](phase11-independent-referee-report.md) | Independent Phase 11 referee report (mathematical PASS; earlier overlap identified) |
| [`phase11-progress.md`](phase11-progress.md) | Phase 11 checkpoints and resumption |
| [`unequal-weight-contraction.md`](unequal-weight-contraction.md) | Phase 10: generic unequal-weight contraction criterion, concrete and family exclusions, 222 kernel-checked finite certificates |
| [`phase10-progress.md`](phase10-progress.md) | Phase 10 checkpoints and resumption |
| [`phase9-prior-art.md`](phase9-prior-art.md) | Phase 9 priority comparison (Molchanov 1983, Monks–Yazinski 2004, López–Stoll 2021) |
| [`phase9-referee-report.md`](phase9-referee-report.md) | Phase 9 theorem and Lean audit |
| [`phase9-progress.md`](phase9-progress.md) | Phase 9 journal; manuscript status and outstanding owner decisions (issue #15 open) |
| [`phase0-report.md`](phase0-report.md) | hand-written report for the first milestone: what is proved, what is only checked, limitations, next questions |
| [`literature-cst.md`](literature-cst.md) | how the lab's objects map to the Coefficient Stopping Time literature: sources, equivalence proof, count reconciliation, open obligations |
| [`phase1-next-questions.md`](phase1-next-questions.md) | P1a refutation, audit of earlier proposals, and the bounded Phase 2 experiment |
| [`envelope/summary.md`](envelope/summary.md) | generated Phase 2 table: all exact extrema and envelope factors for `1 <= r <= 12` |
| [`envelope/evidence.json`](envelope/evidence.json) | exact Phase 2 evidence, all ties, independent counts and Terras offsets |
| [`envelope-extended/summary.md`](envelope-extended/summary.md) | extended exhaustive mini-max envelope (`1 <= r <= 23`, 150,456,309 classes), third P1a counterexample (`r=14`), `E_r <= 3` refutation (`r=22`), and P1b refutation (`m=47, 63` at `r=34, k=54`) |
| [`envelope-extended/evidence.json`](envelope-extended/evidence.json) | machine-readable exact evidence for `1 <= r <= 23` and verified P1b refutation witnesses |
| [`lyapunov/summary.md`](lyapunov/summary.md) | finite-state modular Lyapunov contraction certificates (F3, `1 <= M <= 15`), exact `(M-1)/M` no-go on `G_M \ {2^M - 1}`, and F2 vs F3 excluded-density comparison |
| [`lyapunov/evidence.json`](lyapunov/evidence.json) | machine-readable exact F3 Lyapunov certificates, horizons, and extremal cycles for `1 <= M <= 15` |
| [`lyapunov-exact/summary.md`](lyapunov-exact/summary.md) | exact global minimum `|S_M*|` (`1 <= M <= 8`), certified integer dual-LP brackets (`9 <= M <= 12`), heuristic gap, and `p/q` sensitivity (`5/8` through `94/149`) |
| [`lyapunov-exact/evidence.json`](lyapunov-exact/evidence.json) | machine-readable exact optimal sets `S_M*`, certified dual lower bounds, and `p/q` sensitivity tables |
| [`lyapunov-lift/summary.md`](lyapunov-lift/summary.md) | monotone lift chain of F3 excluded sets (`1 <= M <= 21`): lifting lemma `|S_{M+1}*| <= 2|S_M*|`, pruning over all vertices, improved upper bounds `UB_M` |
| [`lyapunov-lift/analysis-m21.md`](lyapunov-lift/analysis-m21.md) | `M <= 21` run record, independent Python re-check (`verify_chain.py`), and finite-range comparison `UB_M / surv_M ~ 0.43-0.55` with the F2 survivors |
| [`lyapunov-lift/evidence.json`](lyapunov-lift/evidence.json) | machine-readable lift-chain certificates (excluded sets, spans, horizons, per-order pruning counts) |
| [`infinite-itineraries.md`](infinite-itineraries.md) | Phase 3 mathematical memo: all-prefix survival proof, aperiodicity proof, 2-adic Mahler reduction, `B(z) = z^2 - z^3` denominator analysis, Padé table (`1 <= m <= 16`), and literature audit |
| [`mahler/summary.md`](mahler/summary.md) | generated Phase 3 summary: 5-way modular checkpoints up to `2^1024`, periodic control `(1110)^infinity`, and exact Padé table |
| [`mahler/evidence.json`](mahler/evidence.json) | generated Phase 3 machine-readable evidence (arbitrary-precision integers as decimal strings) |
| [`lean-semantic-audit.md`](lean-semantic-audit.md) | Phase 5 Gate A: adversarial audit of the Lean formalization in PR #9 (statement semantics, dependency path, axioms, documentation defects with suggested patches) |
| [`lean-audit/AuditChecks.lean`](lean-audit/AuditChecks.lean) | the audit's own kernel-checked statements; run against a checkout of PR #9 (not a Lake target on this branch) |
| [`mahler-generalization.md`](mahler-generalization.md) | Phase 5 Gate B: the family `mu_L(1) = 1^(L-1) 0`, `mu_L(0) = 1^(L-2) 0 1`, written proof that no rational seed realizes `w_L` for every `L >= 4` (`L = 5` explicit), a sufficient criterion for uniform equal-weight morphisms, bounded Pade table, literature comparison; uniform irrationality and tails kernel-checked in Phase 6 |
| [`lean-family-formalization.md`](lean-family-formalization.md) | Phase 6: all-`L >= 4` kernel proof, exact theorem signatures, tower cancellation, semantic correspondence, 44-declaration axiom audit, and validation |
| [`lean-family-semantic-audit.md`](lean-family-semantic-audit.md) | Phase 7 A: independent semantic audit of the all-`L` theorem and signed, literal-substitution kernel checks |
| [`phase7-progress.md`](phase7-progress.md) | durable campaign checkpoints and exact resumption instructions for issue #13 |
| [`phase7-next-directions.md`](phase7-next-directions.md) | Phase 7 D4: uniform aperiodicity and all-subcritical exclusion in Lean, degree-six numerical ledger, non-unit leading coefficients, unequal-weight rational control, and exact remaining polynomial-certificate obligations |
| [`lean-equal-weight-formalization.md`](lean-equal-weight-formalization.md) | Phase 7 B: generic Theorem 8.1 and all tails kernel-verified under exactly H1–H3 and (C); full signatures and audit |
| [`mahler-uncovered-morphisms.md`](mahler-uncovered-morphisms.md) | Phase 7 C–D: both targets excluded in Lean; independent primary proofs; generic subcritical and periodic-control criteria; finite evidence |
| [`phase8-progress.md`](phase8-progress.md) | Phase 8 entrypoint: verified A–D, additional degree/order audit, commits, CI and resumption |
| [`lean-polynomial-certificates.md`](lean-polynomial-certificates.md) | Exact general polynomial certificate, rational-series periodicity, integer approximant existence and universal theorem mapping |
| [`phase8-findings.md`](phase8-findings.md) | Mathematical synthesis, degree-six ledger optimality, scope audit and primary-literature comparison |
| [`mahler-uncovered/evidence.json`](mahler-uncovered/evidence.json) | 48 exact degree 1–24 Padé rows, 8 residue checkpoints, bounded signed rational falsification and 144 independently checked periodic-control certificates |
| [`mahler-family/summary.md`](mahler-family/summary.md) | generated Phase 5 finite checks: family table, `L = 5` checkpoints, Pade table (`1 <= m <= 16`), criterion counts |
| [`mahler-family/evidence.json`](mahler-family/evidence.json) | generated Phase 5 machine-readable evidence |
| [`example/summary.md`](example/summary.md) | generated summary of the reference experiment |
| [`example/ledger.jsonl`](example/ledger.jsonl) | generated machine-readable ledger of the reference experiment |

The files in `example/` are produced by one command and are reproduced byte
for byte by rerunning it from the repository root:

```text
cargo run --release -- experiment --out-dir research/example
```

Re-check the recorded counterexamples independently with:

```text
cargo run --release -- verify --ledger research/example/ledger.jsonl
```

Ad-hoc runs default to `research/runs/latest`, which is git-ignored.

The Phase 2 table and evidence are reproduced byte for byte with:

```text
cargo run --locked --release -- envelope --out-dir research/envelope
```

This fixed experiment terminates at `r=12` or on the first invariant failure.
Its first counterexample to the finite prediction `E_r<=2` is `r=11`, with
`E_r=479207/179707`. It makes no all-`r` claim and does not prove P1b.
Performance and independent verification are documented in the repository README.

The extended mini-max envelope (`1 <= r <= 23`, `k <= 37`, 150,456,309 classes)
and P1b refutation witnesses (`m=47` and `m=63` at `r=34, k=54`) are reproduced
byte for byte with:

```text
cargo run --locked --release -- envelope-extended --max-r 23 --out-dir research/envelope-extended
```

Independent regression test: `tests/p1b_refutation.rs`.

The Phase 3 Mahler summary and evidence are reproduced byte for byte with:

```text
cargo run --locked --release -- mahler --out-dir research/mahler
```

See [`infinite-itineraries.md`](infinite-itineraries.md) for the algebraic proofs,
the periodic control `(1110)^infinity` (`x = -19/11`), the comparison with
`msharpe248/collatz` (`Rung1.lean`), and the unresolved proof obligations.

The Phase 5 family checks are reproduced byte for byte with (standard library
only, about three seconds):

```text
python3 research/mahler-family/verify_family.py
cargo test --locked --test mahler_family
```

They are finite checks. The uniform irrationality theorem and shifted-tail
corollary are now kernel-checked for every `L >= 4`; see
[`lean-family-formalization.md`](lean-family-formalization.md). The general
symbolic survival and aperiodicity arguments remain written proofs. The
arbitrary-morphism criterion is now kernel-checked in Phase 7; see
[`lean-equal-weight-formalization.md`](lean-equal-weight-formalization.md).

## Certificate families on record

Before any family is optimised, its exact claim and assumptions are written
down here.

### F1. Single-cylinder descent certificate

- **Input.** A parity prefix of length `k` with `r` odd steps and `2^k > 3^r`.
- **Claim.** For every `n >= N0` with `n = rho (mod 2^k)`: `T^k(n) < n`, where
  `N0 = floor(c / (2^k - 3^r)) + 1`. Members below `N0` satisfy `T^k(n) >= n`.
- **Assumptions.** None beyond the affine form of the prefix (proved by
  induction on `k`).
- **Does not claim.** Anything about other classes, about members below `N0`,
  about a second descent, or about reaching 1.

### F2. First-descent cover to depth `K`

- **Construction.** Split a class by the next parity until the first length
  with `2^k > 3^r`, or until length `K`.
- **Claim.** The leaves partition the non-negative integers. On a certified
  leaf of length `k`, members `n >= N0` have stopping time exactly `k`.
- **Assumptions.** None beyond F1.
- **Known gap.** Leaves that reach length `K` are uncovered. Their number is
  positive and non-decreasing in `K` (the all-odd branch never descends, and
  the odd child of an uncovered class is uncovered). This family therefore
  cannot become a proof at any finite depth.

### F3. Finite-state modular Lyapunov contraction certificate (modulus `2^M`)

- **Construction.** On the transition graph `G_M` modulo `2^M` with excluded
  residue set `S`, compute an exact integer potential `phi: V_M \ S -> Z`
  satisfying `q * odd(u) + phi(v) - phi(u) <= p` on every active edge `(u -> v)`,
  with `3^p < 2^q` (currently `p/q = 63/100`).
- **Claim.** Any orbit segment of length `L` staying inside `V_M \ S` satisfies
  `q * r_L + phi(u_L) - phi(u_0) <= p * L`, forcing a strict coefficient
  crossing `3^(r_L) < 2^L` once `L >= L_0` (`2^(q*L_0) > 3^(p*L_0 + span)`).
  Reproduce `1 <= M <= 15` with
  `cargo run --locked --release -- lyapunov --max-m 15 --out-dir research/lyapunov`
  (independent tests in `tests/lyapunov.rs`).
- **Known gap / finite-state no-go.** On full `G_M` the self-loop at `2^M - 1`
  gives odd density `1/1`, and on `G_M \ {2^M - 1}` the exact maximum odd cycle
  density is `(M - 1)/M` (exceeding `1/log2(3)` for all `M >= 3`). Pruning F2
  survivors via incremental warm-start SPFA reduces the excluded set substantially
  (e.g. `314/16384 = 1.92%` vs `734/16384 = 4.48%` at `M = 14`), but F3 does
  not prevent an orbit from entering `S`.
- **Lifting bound (correction of the `M = 14 -> 15` "bump").** Reduction modulo
  `2^M` is an odd-label-preserving homomorphism `G_{M+1} -> G_M`, so an F3
  certificate lifts with `|lift(S)| = 2|S|` and the exact optimum density
  `|S_M*| / 2^M` is non-increasing in `M` (written argument, checked per depth).
  The survivors-only value `662/32768 = 2.02%` at `M = 15` is a heuristic
  artifact: the lifted `M = 14` set gives `628`, and the monotone lift chain in
  `lyapunov-lift/` gives verified upper bounds `599/32768 = 1.83%` (`M = 15`),
  `1143/65536 = 1.74%` (`M = 16`), `1908/131072 = 1.46%` (`M = 17`) and
  `3490/262144 = 1.33%` (`M = 18`), extended to `6426` (`M = 19`, 1.23%),
  `12627` (`M = 20`, 1.20%) and `22691` (`M = 21`, 1.08%); it also improves
  `UB_10` to `37` and `UB_12` to `110` (the `lyapunov-exact` brackets list
  `38` and `114`). Reproduce with
  `cargo run --locked --release -- lyapunov-lift --max-m 21 --exact-seed-max-m 8 --out-dir research/lyapunov-lift`
  (about 10.5 h on 8 cores; `--max-m 18` takes about 1.5 min and reproduces
  the first 18 rows; independent tests in `tests/lyapunov_lift.rs`, independent
  re-check `research/lyapunov-lift/verify_chain.py`). For `9 <= M <= 21` the
  chain stays at about 43–55% of the F2 survivor count, so the density decrease
  matches the classical F2 survivor decay
  ([analysis](lyapunov-lift/analysis-m21.md)). These are upper bounds only,
  with no claim about the limit of the density.

### Not attempted

Adaptive or unbounded-horizon global certificates remain out of scope. The
no-go result in `src/nogo.rs` concerns fixed descent windows only; the
finite-state modular Lyapunov no-go in `src/lyapunov.rs` concerns uniform
modular potentials on `G_M` and `G_M \ {2^M - 1}`.
