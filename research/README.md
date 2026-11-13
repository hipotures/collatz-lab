# Research notes

| file | content |
|---|---|
| [`phase0-report.md`](phase0-report.md) | hand-written report for the first milestone: what is proved, what is only checked, limitations, next questions |
| [`literature-cst.md`](literature-cst.md) | how the lab's objects map to the Coefficient Stopping Time literature: sources, equivalence proof, count reconciliation, open obligations |
| [`phase1-next-questions.md`](phase1-next-questions.md) | three bounded, falsifiable follow-up experiments with stopping rules |
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
