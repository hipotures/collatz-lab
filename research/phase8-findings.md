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

## Remaining proposal

The A–C ingredients now compile. Composition, universal/tail exports and
adversarial semantic audit remain; the unconditional equal-weight exclusion
is **not yet claimed**. There is no counterexample to the route established by this work.
The coefficient-8 obstruction refutes only the discarded unit-leading shortcut.

## Scope

No assertion about all Collatz orbits, the general 2-adic Periodicity Conjecture,
transcendence or novelty is made. No external literature comparison has yet
been performed during Phase 8. Unequal weights continue to fall outside the
constant block-multiplier theorem.
