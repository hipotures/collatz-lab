# Research notes

| file | content |
|---|---|
| [`phase0-report.md`](phase0-report.md) | hand-written report for the first milestone: what is proved, what is only checked, limitations, next questions |
| [`literature-cst.md`](literature-cst.md) | how the lab's objects map to the Coefficient Stopping Time literature: sources, equivalence proof, count reconciliation, open obligations |
| [`phase1-next-questions.md`](phase1-next-questions.md) | P1a refutation, audit of earlier proposals, and the bounded Phase 2 experiment |
| [`envelope/summary.md`](envelope/summary.md) | generated Phase 2 table: all exact extrema and envelope factors for `1 <= r <= 12` |
| [`envelope/evidence.json`](envelope/evidence.json) | exact Phase 2 evidence, all ties, independent counts and Terras offsets |
| [`infinite-itineraries.md`](infinite-itineraries.md) | Phase 3 mathematical memo: all-prefix survival proof, aperiodicity proof, 2-adic Mahler reduction, `B(z) = z^2 - z^3` denominator analysis, Padé table (`1 <= m <= 16`), and literature audit |
| [`mahler/summary.md`](mahler/summary.md) | generated Phase 3 summary: 5-way modular checkpoints up to `2^1024`, periodic control `(1110)^infinity`, and exact Padé table |
| [`mahler/evidence.json`](mahler/evidence.json) | generated Phase 3 machine-readable evidence (arbitrary-precision integers as decimal strings) |
| [`lean-semantic-audit.md`](lean-semantic-audit.md) | Phase 5 Gate A: adversarial audit of the Lean formalization in PR #9 (statement semantics, dependency path, axioms, documentation defects with suggested patches) |
| [`lean-audit/AuditChecks.lean`](lean-audit/AuditChecks.lean) | the audit's own kernel-checked statements; run against a checkout of PR #9 (not a Lake target on this branch) |
| [`mahler-generalization.md`](mahler-generalization.md) | Phase 5 Gate B: the family `mu_L(1) = 1^(L-1) 0`, `mu_L(0) = 1^(L-2) 0 1`, written proof that no rational seed realizes `w_L` for every `L >= 4` (`L = 5` explicit), a sufficient criterion for uniform equal-weight morphisms, bounded Pade table, literature comparison; uniform irrationality and tails kernel-checked in Phase 6 |
| [`lean-family-formalization.md`](lean-family-formalization.md) | Phase 6: all-`L >= 4` kernel proof, exact theorem signatures, tower cancellation, semantic correspondence, 44-declaration axiom audit, and validation |
| [`lean-family-semantic-audit.md`](lean-family-semantic-audit.md) | Phase 7 A: independent semantic audit of the all-`L` theorem and signed, literal-substitution kernel checks |
| [`phase7-progress.md`](phase7-progress.md) | durable campaign checkpoints and exact resumption instructions for issue #13 |
| [`lean-equal-weight-formalization.md`](lean-equal-weight-formalization.md) | Phase 7 B: generic Theorem 8.1 and all tails kernel-verified under exactly H1–H3 and (C); full signatures and audit |
| [`mahler-uncovered-morphisms.md`](mahler-uncovered-morphisms.md) | Phase 7 C–D: both targets excluded in Lean; independent primary proofs; generic subcritical and periodic-control criteria; finite evidence |
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

### Not attempted

Adaptive or unbounded-horizon certificates, potential (Lyapunov) functions,
and finite-state contraction certificates are out of scope for this
milestone. The no-go result recorded in `src/nogo.rs` concerns fixed descent
windows only and must not be read as covering those.
