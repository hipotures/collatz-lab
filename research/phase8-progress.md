# Phase 8 research campaign — issue #14

Work directly on `main`; no branches, worktrees, PRs or force pushes.
Starting HEAD (2026-11-14 UTC):
`63296dd317eb1b8d48554b7ea843424fca97b74b`.
Initial working tree was clean; fetch and fast-forward pull succeeded.

## Resume here

**The universal theorem is proposed, not yet proved.** Phase 7 results are
retained. Read `phase7-next-directions.md` and the issue before extending them.
**Current code checkpoint:** milestone A is kernel-verified and fully validated.
Its first code commit is being pushed; subsequent checkpoints record its SHA. New modules are `PolynomialPair.lean`,
`PolynomialHeight.lean`, `PolynomialCertificate.lean`, `PolynomialChecks.lean`.
Read `lean-polynomial-certificates.md` for the exact conditional interface.

| Milestone | Verified status |
|---|---|
| A: arbitrary polynomial-pair conditional certificate | COMPLETE — kernel-verified, full local validation |
| B: rational binary series implies eventual periodicity | Open |
| C: universal degree-six/order-at-least-thirteen existence | Open |
| D: unconditional equal-weight exclusion and tails | Open; depends on B–C |
| E: scope audit and further mathematics | Pending |

## Exact next obligations

1. Prove deterministic finite-memory repetition for a binary sequence
   satisfying an eventual recurrence with nonzero determining coefficient;
   handle initial zero coefficients in the denominator polynomial.
2. Prove six homogeneous equations in seven integer unknowns have a nonzero
   solution. An integer elimination proof can induct on the number of rows:
   if column zero vanishes choose its unit vector; otherwise choose a pivot
   row with nonzero column-zero coefficient, eliminate that column in the
   other rows, and reconstruct an integer solution without division.
3. Compose B–C with A and the existing degree-six ledger; choose the first
   nonzero residual index with no a priori upper bound.

## Constraints and failed shortcuts to retain

- Keep the raw degree-six pair; dividing out a common power of `z` loses
  part of the guaranteed residual order.
- The degree-six Thue–Morse residual starts with coefficient **8** at order
  13. An odd/unit first coefficient at every tower level is false.
- The existing degree-six numerical gap is a ledger, not pair existence.
- Equal weights are essential to the scalar tower; `UnequalControl.lean`
  supplies a rational unequal-weight counterexample.
- All mathematical claims promoted as verified must compile without proof
  escapes and pass the exact standard-foundation audit.

## Reproduction

```text
lake build
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 190
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/mahler-uncovered/verify_uncovered.py --check
```

The exact audit now includes all 33 new exported declarations (190 total).
Also run `python3 research/phase8/verify_polynomial.py`; CI runs it too.

## A checkpoint details

- Arbitrary constant-first integer pairs, common raw degree, exact finite
  convolution and explicit tail: kernel proofs compiled.
- All-level `a_k^N` divisibility, exact non-unit valuation after finite start,
  coefficient norm height, conditional exclusion and all tails: compiled.
- Both existing periodic controls and degree-six Thue–Morse coefficient 8:
  compiled. A genuine 64-symbol prefix seed independently checks form
  valuations 29 and 55.
- Independent Python regression: 686 exact convolution identities, signed
  height bounds, concrete coefficient-8 valuations pass.
- All baseline Phase 7 checks pass: 157-declaration audit, 94 Rust tests,
  formatting, Clippy, Python artifact reproduction.
- Full A validation passes: Lean build, 190 exact audited declarations (only
  approved standard foundations), audit-parser self-tests, 94 Rust tests,
  formatting, Clippy, both Python checkers, empty forbidden-token scan and
  `git diff --check`.

