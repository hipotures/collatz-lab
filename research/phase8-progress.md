# Phase 8 research campaign — issue #14

Work directly on `main`; no branches, worktrees, PRs or force pushes.
Starting HEAD (2026-11-14 UTC):
`63296dd317eb1b8d48554b7ea843424fca97b74b`.
Initial working tree was clean; fetch and fast-forward pull succeeded.

## Resume here — all required milestones complete

**Verified code commit:** `63a52b4b400a1bf17aac38531c3d8c8c147ff70b`.
**Code CI:** https://github.com/hipotures/collatz-lab/actions/runs/43584835901 — success.
This journal-only checkpoint follows that immutable code commit; read
`git rev-parse HEAD` for the current journal commit. Work remains on `main`.

The main export is `CollatzLab.no_rational_seed_realizes_all_equal_weight`
in `CollatzLab/UniversalEqualWeight.lean`. It has exactly H1–H3 and `L>=2`,
with arbitrary integer numerators/denominators interpreted by the unchanged
`RealizesWord` predicate. All finite shifts and eventual matches are excluded.
No main theorem or required milestone proof obligation remains. All useful
Lean work is committed; no scratch proof must be recovered.

| Milestone | Verified status |
|---|---|
| A: arbitrary polynomial-pair conditional certificate | COMPLETE — arbitrary signs and non-unit coefficients, explicit finite start |
| B: rational binary series implies eventual periodicity | COMPLETE — also generalized to every bounded integer alphabet, with converse |
| C: universal degree-six/order-at-least-thirteen existence | COMPLETE — general division-free integer linear algebra, no prefix cache |
| D: unconditional equal-weight exclusion and tails | COMPLETE — kernel-verified, independent semantic witnesses and clean rebuild |
| E: additional research and audit | COMPLETE — scope/literature comparison, minimum degree for the implemented criterion, premature-valuation counterexample, quantitative bounds and uniform safe level |

Read `lean-polynomial-certificates.md` for the exact theorem mapping and
`phase8-findings.md` for mathematical scope, additional results and sources.
Do not repeat the Phase 7/8 proof campaigns or finite catalogues.

## Optional future proof obligations — not blockers for issue #14

1. Sharpen the coefficient bound by proving controlled maximal-minor or
   primitive-vector bounds, including deficient-rank and zero matrices.
   The current verified bound is `X=720*2^57`; chosen certificates have
   leading valuation below 70 and safe valuation level 6. No minimum safe
   level is asserted, and no upper bound on first residual order is supplied.
2. Improve the actual height recurrence before seeking a smaller universal
   certificate degree. Degree six is least **for the implemented Gap criterion**,
   even at arbitrary order; a genuinely stronger criterion needs a new proof.
3. For broader substitution domains, first supply a valid common block
   multiplier and scalar/vector transport. Unequal weights have a known
   rational periodic counterexample. The bounded-series bridge alone does
   not exclude general automatic or larger-alphabet Collatz itineraries.

Independent mathematical review and a fuller prior-art comparison remain
welcome; no novelty, Collatz or general Periodicity Conjecture claim is made.

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
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 306
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/mahler-uncovered/verify_uncovered.py --check
python3 research/phase8/verify_polynomial.py
python3 research/lean-audit/check_axioms.py --self-test
```

The exact audit now includes all 149 new exported declarations (306 total).
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

## E3 checkpoint details

- `RationalSeries.deterministic_window_periodic` shares the finite-window
  repetition argument; the old binary export keeps its exact signature.
- `BoundedRationalSeries.lean`: arbitrary signed finite integer intervals,
  injective base encoding (including base 1), bounded rational-series
  periodicity and nonzero residuals.
- `eventually_periodic_rational_pair` constructs the converse for every
  integer sequence, with denominator `1-z^p`. `bounded_rational_iff_periodic`
  gives the full equivalence for bounded integer coefficient sequences.
- `BoundedSeriesChecks.lean`: signed wave, singleton at -7, and coefficient
  identity for the unbounded sequence n, which is proved nonperiodic and
  unbounded. Boundedness cannot be dropped from the forward implication.
- These are standalone series facts; the Collatz theorem's semantic domain
  is unchanged. Full checkpoint validation passes.
- Build, 276-declaration exact audit, 94 Rust tests, formatting, Clippy,
  both Python checkers, empty proof-escape scan and diff check all pass.

## E4 checkpoint details

- `PrematureValuation.lean` independently checks the old degree-ten secondary
  pair with order 21/coefficient 24, its closing ledger and actual 256-symbol
  rational prefix. No old search bound is extended.
- Exact finite tower congruences at length 22 and form valuations 68 at
  level zero, 192 at level one. The former contradicts the premature 66
  predicted without strict leading-coefficient domination.
- The finite seed is not an infinite realization. The refuted step is an
  arithmetic deduction from finite congruence/residual data.
- Full validation passes: build, 284-declaration exact audit, 94 Rust tests,
  formatting, Clippy, both Python checkers, empty proof-escape scan, diff check.

## E5 checkpoint details

- `BoundedLinear.integer_null_vector_bounded`: explicit finite coefficient
  bounds at every dimension, with arbitrary signed entries and deficient rank.
- `UniformStart.lean`: bounded approximant existence, exact degree-six
  coefficient/norm/height constants, first residual valuation below 70 and
  a uniform safe starting level 6.
- `Morphism.universal_bounded_degree_six_certificate` and
  `universal_degree_six_valuation` export this data for every admissible
  morphism, before choosing any hypothetical rational seed.
- No upper bound on first order or contradiction level is claimed. The
  general exclusion and its hypotheses are unchanged.
- Full checks pass: build, 301-declaration exact audit, 94 Rust tests,
  formatting, Clippy, both Python checkers, empty proof-escape scan, diff check.

## E6 / final local validation

- `CertificateSanity.lean` derives the pair/denominator nonzero conditions
  from finite coefficient data and the strict gap, with no orbit assumptions.
- `lake clean && lake build` succeeds from scratch. Exact audit: 306 entries,
  all standard foundations only; parser self-tests pass (2 valid, 8 adversarial).
- A source-to-audit comparison confirms every one of the 149 new theorem
  exports is listed, and all 157 baseline entries remain.
- 94 Rust tests, formatting, Clippy with `-D warnings`, both Python checkers,
  empty proof-escape scan and full-baseline whitespace check pass.
- The original `Word`, `MorphismWord`, `MorphismTower`, Rust source/test and
  Cargo dependency files have no diff from the starting commit.

## Pushed code history

Every code checkpoint below was fully validated locally and pushed directly
onto `origin/main`; no branch, worktree, PR or force push was used. CI status
is recorded only after observation of the actual run.

| Checkpoint | Full commit SHA | CI |
|---|---|---|
| A: general polynomial certificate | `6560d1719ad5998be988236182feef8f2ade1292` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43579255480) |
| C: integer elimination and universal pair existence | `723f103107406db4658d7122a2b2f3091b804bf3` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43579550635) |
| B: rational binary-series periodicity | `83835a7e8ef8f0b0a3d12af332ad83b6642a557a` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43579996609) |
| D: universal theorem and all tails | `59cc117ef9beeb81ebacdc2d8594781c622e607a` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43580578326) |
| E: dimension-count ledger threshold and scope | `7cd9a95285718e01cc5f59e6086ad13495bf2fcb` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43581609610) |
| E2: least degree for the actual certificate interface | `4f54b3acbca6010b608a6a35bc92f59cdf9c52f6` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43582367746) |
| E3: bounded integer rational-series characterization | `12e9e53c74c92a31492de9b0c83f06647de594eb` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43583179137) |
| E4: actual premature valuation counterexample | `50bdb4d3ad6916782b8283c875abe1dfd3466390` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43583686517) |
| E5: uniform coefficient and starting-level bounds | `476cd2a0b3d2d099217745a06d8040bc622012a6` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43584500897) |
| E6: finite certificate nonzero audit | `63a52b4b400a1bf17aac38531c3d8c8c147ff70b` | [success](https://github.com/hipotures/collatz-lab/actions/runs/43584835901) |

Final verified local counts: **306 exact audited declarations**, including
all **149** new theorem exports and all **157** retained baseline entries;
only approved standard foundations. **94 Rust tests**, zero failures.
Both Python checkers pass, including 686 general finite convolution identities,
144 bounded null-vector fixtures, 5,635 signed-alphabet encodings, literal and
signed/unreduced prefix checks, minimal-degree systems, coefficient bounds,
and the genuine premature-valuation regression. The final code was rebuilt
from a clean Lake directory. Actual parity semantics and Rust behavior remain
unchanged. The main target and all described additional research are complete;
future work above is optional.
