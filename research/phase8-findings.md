# Phase 8 mathematical findings

## A: general polynomial certificate (Lean-kernel-verified)

The conditional certificate in `PolynomialCertificate.lean` accepts arbitrary
signed integer pairs, first residual order at least their common raw degree,
and a strict integer base gap. Its proof confirms the proposed cost exponent
`d*(L-1)+L+e` without imposing a sign on `B-A` or the signed denominator.

A nonzero first coefficient always has an exact finite factorization `2^v*c`
with odd signed `c`. At tower spacing greater than `v`, the leading term
cannot cancel with the remaining tail. All earlier levels can be discarded:
raising both strict-gap bases to `L^k0` preserves strictness and reduces the
remaining bounds to the already proved exponential contradiction.

See `lean-polynomial-certificates.md` for exact finite identities, theorem
interfaces, height constants, regressions, and the trust boundary.

## C: uniform existence (Lean-kernel-verified)

A division-free integer elimination proof establishes a nonzero kernel vector
for every `m` by `m+1` integer matrix, including deficient rank. This gives
raw degree `d` / order at least `2*d+1` polynomial pairs for **every integer
sequence**, with a nonzero denominator polynomial. The required degree-six
case follows directly. No finite binary-word cache or Mathlib was needed.

## B: rational binary series (Lean-kernel-verified)

A coefficientwise polynomial identity with a nonzero denominator implies an
eventual finite-memory recurrence. Equal binary windows force equal next
symbols by cancellation of the first nonzero coefficient, including initial
zero coefficients. Finite-window repetition gives eventual periodicity.
Thus every nonperiodic binary sequence has a nonzero residual for every
nonzero denominator pair. No rational Collatz periodicity assertion is used.

## D: universal equal-weight exclusion (Lean-kernel-verified)

`no_rational_seed_realizes_all_equal_weight` has exactly H1–H3 and `L>=2`.
Its all-shift and eventual-match corollaries preserve positive odd denominator
semantics and allow negative numerators and unreduced fractions.

The degree-six pair has a nonzero residual by B and proved word aperiodicity.
A least nonzero index `N>=13` is obtained without an upper bound; the numerical
ledger is monotone in `N`. A then gives the height/valuation contradiction,
discarding the required finite number of early levels.

The explicit length-six images `101011/011011` have `B=81>A=64` and fail (C).
They are excluded by the universal theorem, and an independently checked
raw polynomial pair has order 13 and a closing ledger. Literal substitution
and actual signed rational prefix checks cover lengths 2 through 6, and the
infinite itinerary predicate remains explicitly non-vacuous.

See the proof mapping for exact signatures and the complete semantic audit.
Further degree/order optimization and primary-literature comparison remain.
 There is no counterexample to the route established by this work.
The coefficient-8 obstruction refutes only the discarded unit-leading shortcut.

## Scope

No assertion about all Collatz orbits, the general 2-adic Periodicity Conjecture,
transcendence or novelty is made. No external literature comparison has yet
been performed during Phase 8. Unequal weights continue to fall outside the
constant block-multiplier theorem.
