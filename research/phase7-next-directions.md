# Phase 7 D4: uniform aperiodicity and the degree-six proposal

2026-11-14 UTC. This note separates newly kernel-verified results from a
promising **unfinished** extension. No unconditional exclusion of all
admissible supercritical morphisms is claimed.

## 1. Uniform aperiodicity is now kernel-verified

The public result, in `CollatzLab.Morphism`, is:

```lean
theorem not_eventually_periodic {L : Nat} (hL : 2 ≤ L) (M : Images L)
  (h1 : image M true 0 = true)
  (hw : weight (image M false) L = weight (image M true) L)
  (hd : M.zero ≠ M.one) :
  ¬ CollatzLab.EventuallyPeriodic (parityWord M)
```

`MorphismAperiodic.lean` proves this for arbitrary admissible images, using
only finite words, counts and natural-number gcd. It does not use any
rational Collatz periodicity assertion or analytic Mahler theorem.

Here is the complete combinatorial argument checked by the kernel. Suppose
an eventual period `p>=1` exists. Distinct fixed-length images are injective
on letters. Put `g=gcd(L,p)`. Because `L*(p/g)=p*(L/g)`, period `p` implies
the two image blocks at letter indices `n` and `n+p/g` agree sufficiently far
out; injectivity makes `p/g` an eventual letter period. If `g>1`, strong
induction descends to a smaller positive period.

If `g=1`, every aligned block has weight `r`, so counting any sufficiently
late interval of length `L*p` in the two ways gives `p*r=L*c`, where `c`
is the weight of one period. Coprimality forces `L|r`, contrary to
`1<=r<L`. The implementation uses `Nat.gcd_mul_dvd_mul_gcd` to justify that
cancellation explicitly. No limiting density or minimal-period existence
principle is assumed.

This supplies the previously explicit aperiodicity hypothesis in the
subcritical criterion. The new exact export is:

```lean
theorem CollatzLab.no_rational_seed_realizes_subcritical_equal_weight
  {L : Nat} (hL : 2 ≤ L) (M : CollatzLab.Morphism.Images L)
  (h1 : CollatzLab.Morphism.image M true 0 = true)
  (hw : CollatzLab.Morphism.weight (CollatzLab.Morphism.image M false) L =
        CollatzLab.Morphism.weight (CollatzLab.Morphism.image M true) L)
  (hd : M.zero ≠ M.one)
  (hBA : CollatzLab.Morphism.B M < CollatzLab.Morphism.A L) (p q : Int) :
  ¬ CollatzLab.RealizesWord p q (CollatzLab.Morphism.parityWord M)
```

`no_rational_seed_realizes_shifted_subcritical_equal_weight` and
`no_eventually_shifted_subcritical_equal_weight_itinerary` provide all tails.
The old independent Thue–Morse aperiodicity and contraction proof is retained.

## 2. A uniform numerical gap for degree six is kernel-verified

`DegreeSix.lean` proves, for every `L>=2`, `r<L`, `e<L`,

```text
max(2^L,3^r)^(6*(L-1)+L+e) < 2^(13*L*(L-1)).
```

The exact names are `CollatzLab.degree_six_numerical_gap` and
`CollatzLab.Morphism.degree_six_ledger`. The latter derives parameter bounds
from the actual images and equal-weight/distinctness conditions.

If the maximum is `2^L`, exponent comparison suffices. If it is `3^r`,
put `cost=6*(L-1)+L+e`. The elementary bounds `cost<=8L`, `r<=L-1` give
`8*r*cost<=64*L*(L-1)<65*L*(L-1)`. Compare fifth powers using
`3^5<2^8`; reflect their strict order back to the positive original bases.
This proof uses no floating point.

**What this does not prove:** existence or nonvanishing of a suitable Padé
pair. It is a numerical ledger theorem, not a universal irrationality theorem.

## 3. The next proposal, not a completed theorem

The remaining route to exclusion of *all* admissible equal-weight words is:

1. For a binary series `F`, use a degree-6 pair. There are seven denominator
   coefficients and six homogeneous equations, for residual coefficients
   7 through 12. A rational nullspace vector can be scaled to integers;
   choosing numerator coefficients to cancel 0 through 6 gives order at
   least 13. This dimension argument is a written algebra observation, not
   yet a Lean theorem in this repository.
2. Prove that the residual is not identically zero. Otherwise it gives a
   rational generating function and a deterministic finite-memory recurrence
   for the binary symbols, hence eventual periodicity, contradicting §1.
   The bridge from a rational integer-coefficient series identity to an
   eventually periodic binary word still needs a kernel implementation.
3. Generalize `PeriodicCertificate` from denominators `1-z^P` to arbitrary
   primitive polynomial pairs. The coefficient norm is a fixed factor in the
   height bound; the existing signed tower and strict-gap theorem apply.
4. Handle a non-unit first residual coefficient correctly. If it is
   `c=2^v*c_odd`, the exact valuation formula is safe at levels where
   `L^(k+1)>v`. It then gives `N*L^(k+1)+v`, with a nonzero form. Shift the
   level index by a finite `k0` before applying the exponential contradiction.
   Discarding the first levels does not discard any rational seed.
   The arithmetic core is now kernel-checked in `LeadingCoefficient.lean`:
   `nonunit_leading_valuation` proves exact valuation for
   `2^v*c_odd+2^m*t` when `v<m`, and
   `finite_start_for_leading_coefficient` supplies a uniform finite starting
   level. Integrating it with a general polynomial convolution is still open.

A common power of `z` need not be divided out: keep the **raw** pair of
degree at most 6 and raw order at least 13. Homogenize to degree 6. This
avoids losing part of the guaranteed order during a normalization step.

The present formal interface proves periodic controls only. Steps 1–4 above
are real remaining obligations; none is an assumed proposition hidden in a
published irrationality theorem. A complete general polynomial certificate
and its existence proof must be supplied before promoting the proposal.

## 4. Failed shortcut: a unit leading coefficient is not automatic

The committed Thue–Morse Padé row at search degree 6 is a concrete refutation:

```text
p0 = 1-6z+3z^2-4z^3-3z^4+6z^5-9z^6,
p1 = -1+6z-3z^2+5z^3-3z^4-2z^5-z^6,
order N=13, first coefficient c=8, v2(c)=3.
```

Python and Rust independently check the exact coefficient. At level zero
`v2(a_0)=2`, so the desired domination `v2(a_k)>v2(c)` fails; at level one
it is `4>3`. This refutes only an all-level unit-coefficient shortcut. It
does not refute the degree-six proposal. The already formalized period-six
Thue–Morse control has a unit residual and avoids this obstruction.

## 5. Unequal weights require a different theorem

`UnequalControl.lean` kernel-checks `mu(1)=101`, `mu(0)=010`:
H1 and distinctness hold, but the image weights are 2 and 1. The fixed point
is `(10)^infinity`, and `RealizesWord 1 1` holds for it. Thus simply deleting
equal weights from an irrationality or aperiodicity claim is **refuted**.

In general the affine block multiplier is `3^(r_b)`, depending on the parent
symbol. Iteration produces a multiplicative cocycle, not the constant `B`
needed for the single rational Mahler point. A possible vector/cocycle
approach must first replace the scalar finite seed identity; this is a
precise algebraic obstruction, not a computational resource limit.

## Resume priorities

First implement an arbitrary polynomial-pair finite convolution checker and
integrate the proved leading-coefficient lemma with its finite starting level. Then
formalize the binary finite-memory periodicity bridge. Only then choose a
general linear-algebra implementation or a kernel-checked finite cache for
the 4096 possible initial 13-symbol binary prefixes starting in 1. Such a
cache would certify a finite linear-algebra fact for arbitrary lengths; it
must not be confused with a finite catalogue of morphisms.
