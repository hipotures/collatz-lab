# Phase 8 research campaign — issue #14

Work directly on `main`; no branches, worktrees, PRs or force pushes.
Starting HEAD (2026-11-14 UTC):
`63296dd317eb1b8d48554b7ea843424fca97b74b`.
Initial working tree was clean; fetch and fast-forward pull succeeded.

## Resume here

**The universal theorem is proposed, not yet proved.** Phase 7 results are
retained. Read `phase7-next-directions.md` and the issue before extending them.
**Pushed A checkpoint:** `6560d1719ad5998be988236182feef8f2ade1292`.
**CI:** https://github.com/hipotures/collatz-lab/actions/runs/43579255480 — success.

**Pushed C checkpoint:** `723f103107406db4658d7122a2b2f3091b804bf3`.
**CI:** https://github.com/hipotures/collatz-lab/actions/runs/43579550635 — success.

**Current local result:** milestone B is kernel-verified and fully validated,
including the recurrence, nonzero-residual corollary and independent examples.
Next: compose A–C with the numerical ledger into milestone D.
New modules are `PolynomialPair.lean`,
`PolynomialHeight.lean`, `PolynomialCertificate.lean`, `PolynomialChecks.lean`.
Read `lean-polynomial-certificates.md` for the exact conditional interface.

| Milestone | Verified status |
|---|---|
| A: arbitrary polynomial-pair conditional certificate | COMPLETE — kernel-verified, full local validation |
| B: rational binary series implies eventual periodicity | COMPLETE — kernel-verified, full local validation |
| C: universal degree-six/order-at-least-thirteen existence | COMPLETE — kernel-verified, full local validation |
| D: unconditional equal-weight exclusion and tails | Open; A–C ingredients now proved |
| E: scope audit and further mathematics | Pending |

## Exact next obligations

1. For the degree-six pair from C, use `RationalSeries.nonzero_residual`
   and `Morphism.not_eventually_periodic` to obtain a nonzero residual.
   Choose its least index `N`; the initial 13 cancellations imply `N>=13`.
2. Lift `Morphism.degree_six_ledger` from order 13 to this arbitrary `N`,
   then invoke `no_rational_seed_with_polynomial_pair` and export all tails.
3. Audit the full theorem, exact supercritical length-six examples and
   independent literal/rational semantics; then degree/order refinements.

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
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 214
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/mahler-uncovered/verify_uncovered.py --check
```

The exact audit now includes all 57 new exported declarations (214 total).
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


## C checkpoint details

- `FiniteLinear.integer_null_vector`: for every `m` and every integer matrix
  with `m` rows and `m+1` columns, there is a nonzero integer kernel vector.
  Zero column: use its unit vector. Otherwise eliminate using a nonzero
  column-zero pivot, apply induction to the other rows, then reconstruct
  without division. No rank hypothesis is needed.
- `PolynomialPair.polynomial_pair_exists`: for every integer sequence and
  **every degree `d`**, a pair with nonzero denominator of raw degree `d`
  cancels coefficients below `2*d+1`.
- `PolynomialPair.degree_six_pair_exists`: the required universal order-13
  statement, with no binary-prefix enumeration or leading-unit condition.
- Independent exact regression covers 144 integer matrices (dimensions
  zero through eight), including zero columns and deficient rank.
- Full C validation passes: Lean build, 201-declaration exact audit, 94 Rust
  tests, formatting, Clippy, both Python checkers, forbidden-token scan and
  diff whitespace check. All new declarations use approved foundations only.

## B checkpoint details

- `RationalSeries.deterministic_binary_periodic` encodes each length-`d`
  binary window below `2^d`, finds a repeated state and extends equality by
  strong induction. It includes `d=0`.
- `first_nonzero_coefficient` isolates a determining nonzero coefficient
  without changing the raw pair. `recurrence_determines` works with initial
  zeros, negative coefficients, and arbitrary numerator coefficients.
- `rational_binary_eventually_periodic` proves coefficientwise rational
  binary series are eventually periodic. `nonzero_residual` is its general
  contrapositive for every nonperiodic binary sequence.
- `RationalSeriesChecks.lean` checks a degree-zero negative denominator,
  a finite impulse, alternating symbols with common factor `z^2` and a
  negative determining coefficient, and Thue–Morse residual nonvanishing.
  No Collatz rational-exclusion theorem is used in this bridge.
- Full B validation passes: Lean build, 214-declaration exact audit, 94 Rust
  tests, formatting, Clippy, both Python checkers, empty proof-escape scan,
  and diff whitespace check.
