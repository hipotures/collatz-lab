# Phase 8 research campaign — issue #14

Work directly on `main`; no branches, worktrees, PRs or force pushes.
Starting HEAD (2026-11-14 UTC):
`63296dd317eb1b8d48554b7ea843424fca97b74b`.
Initial working tree was clean; fetch and fast-forward pull succeeded.

## Resume here

**The universal theorem and its tails are now kernel-verified.** All Phase 7
results and independent proofs are retained. Read the proof mapping before
extending the theorem's scope.
**Pushed A checkpoint:** `6560d1719ad5998be988236182feef8f2ade1292`.
**CI:** https://github.com/hipotures/collatz-lab/actions/runs/43579255480 — success.

**Pushed C checkpoint:** `723f103107406db4658d7122a2b2f3091b804bf3`.
**CI:** https://github.com/hipotures/collatz-lab/actions/runs/43579550635 — success.

**Pushed B checkpoint:** `83835a7e8ef8f0b0a3d12af332ad83b6642a557a`.
**CI:** https://github.com/hipotures/collatz-lab/actions/runs/43579996609 — success.

**Pushed D checkpoint:** `59cc117ef9beeb81ebacdc2d8594781c622e607a`.
**CI:** https://github.com/hipotures/collatz-lab/actions/runs/43580578326 — success.
A–D are complete. No main theorem proof obligation remains.

**Pushed E checkpoint:** `7cd9a95285718e01cc5f59e6086ad13495bf2fcb`.
**CI:** https://github.com/hipotures/collatz-lab/actions/runs/43581609610 — success.

**Current additional result E2:** `MinimalCertificate.lean` is kernel-verified. Degree
six is the least uniform degree for the implemented certificate criterion,
**allowing arbitrary residual order**, by a length-1000 example excluding
all degree-at-most-five pairs. An explicit degree-six pair closes that case.
Full validation passes before committing this stronger result (258 audited
declarations, 94 Rust tests, both independent checkers).

| Milestone | Verified status |
|---|---|
| A: arbitrary polynomial-pair conditional certificate | COMPLETE — kernel-verified, full local validation |
| B: rational binary series implies eventual periodicity | COMPLETE — kernel-verified, full local validation |
| C: universal degree-six/order-at-least-thirteen existence | COMPLETE — kernel-verified, full local validation |
| D: unconditional equal-weight exclusion and tails | COMPLETE — kernel-verified, clean rebuild and full validation |
| E: scope audit and further mathematics | Kernel-verified degree/order results, scope and literature audit; further work optional |

## Exact next obligations

1. Record E2's pushed SHA and CI. A–D are complete and should
   not be re-proved or replaced by finite enumeration.
2. Optional further work: generalize the standalone finite-memory theorem
   to bounded integer alphabets. This extends only the algebraic bridge;
   a larger-alphabet Collatz theorem still needs a valid scalar/vector tower.
3. Investigate improved height recurrences, different approximant shapes,
   or independent review. The E2 minimal degree is relative to the exact
   implemented gap, not to every possible mathematical exclusion method.

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
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 258
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/mahler-uncovered/verify_uncovered.py --check
```

The exact audit now includes all 101 new exported declarations (258 total).
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

## D checkpoint details

- `Morphism.universal_degree_six_certificate`: pair and finite order exist
  from H1–H3, independently of any rational seed hypothesis.
- `no_rational_seed_realizes_all_equal_weight`, all finite shifts and
  eventual shifted matches are kernel-checked. No (C), base ordering,
  subcriticality or extra nonperiodicity hypothesis is present.
- `UniversalChecks.lean`: old named cases as new corollaries; a supercritical
  length-six example that fails (C); an independent explicit pair; literal
  substitutions at lengths 2 through 6; signed rational prefix witnesses;
  unreduced fractions equivalent at every index; non-vacuous infinite predicate.
- Local full checks pass: build, 233-declaration exact audit, parser self-tests,
  94 Rust tests, formatting, Clippy, Phase 7 artifact reproduction, 144 exact
  null vectors, five semantic/existence fixtures, 686 convolution identities,
  coefficient-8 form values, empty forbidden-token scan and diff check.
- Clean rebuild: `lake clean && lake build` succeeds, followed by the exact
  233-declaration audit. No stale compiled artifact is needed.

## E checkpoint details

- `universal_dimension_gap_iff`: the existing uniform numerical ledger at
  guaranteed order `2*d+1` holds iff `d>=6`.
- Actual admissible `highWeight101` realizes `r=e=100` and refutes that ledger
  for every `d<=5`. Six small-base comparisons are checked in the kernel,
  then monotone powers lift them to the ledger.
- The same example has `highWeight101Low`, degree 2, first order 201,
  coefficient -1, with a proved strict gap and an independent conditional
  rational exclusion. This prevents overclaiming the degree-six minimum.
- `Morphism.universal_high_degree_certificate`: every degree `d>=6` supplies
  a closing pair for every admissible equal-weight morphism.
- `phase8-findings.md` records a scope audit and direct primary-source
  comparisons (Bugeaud–Yao, Adamczewski–Faverjon, López–Stoll), with no novelty
  claim and no imported external proof assumption.
- Independent exact search of worst-parameter ledger failures finds first
  lengths `[2,2,2,7,16,101]` for degrees 0 through 5; only this finite search
  result, not its length minimality in Lean, is asserted.
- Full E validation passes: build, exact 245-declaration audit, 94 Rust tests,
  formatting, Clippy, both Python checkers, empty proof-escape scan and diff check.

## E2 checkpoint details

- `MinimalCertificate.universal_certificate_degree_iff`: minimum uniform
  degree six for the implemented finite polynomial interface, at arbitrary
  first residual order.
- One admissible length-1000 word has prefix `110100010011`, weight 993 and
  last disagreement 999. Six small nonsingular systems force every nonzero
  denominator of degree `d<=5` to have order at most `2*d+1`; exact twelfth-power
  comparisons then block its gap. No huge closed power is evaluated.
- An explicit degree-six/order-13 pair with leading coefficient -1 closes
  the same word and independently excludes rational seeds through A.
- Python checks all six determinants, the actual images/weights, the
  exponent comparisons, explicit degree-six pair and the earlier order-201
  low-degree example. Full validation passes for this checkpoint.
- Build, 258-declaration exact audit, 94 Rust tests, formatting, Clippy, both
  Python checkers, empty proof-escape scan and diff check all pass.
