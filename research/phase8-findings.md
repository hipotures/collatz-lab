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
transcendence or novelty is made. The primary-literature comparison below
records its exact limits. Unequal weights continue to fall outside the
constant block-multiplier theorem.

## E: degree/order tradeoff (Lean-kernel-verified)

`DegreeTradeoff.lean` proves `UniversalDimensionGap d ↔ 6 <= d`, where this
predicate is exactly the existing numerical ledger with **only** the
uniformly guaranteed order `2*d+1`, over all `L>=2`, `r<L`, `e<L`.
Sufficiency starts from degree six and proves that each increase in degree
preserves the gap: `m<4^L` controls the extra height while the guaranteed
order increases by two. Necessity is an exact integer counterexample at
`L=101`, `r=e=100`, simultaneously for degrees 0 through 5.

These worst-case parameters are attained by actual admissible images:
`mu(1)` is length 101 with its sole zero at position 1, and `mu(0)` has its
sole zero at position 100 (zero-based positions). Their aperiodicity and
rational exclusion follow from the universal theorem. The six exact
small-base comparisons are checked at exponents at most 1111; the large
ledger comparison is then proved by monotone powers, not by reducing huge
closed numerals.

This is **not** a lower bound on the degree of the best certificate for an
individual word. The very same length-101 example has the degree-two pair

```text
P0=-1+z-z^2, P1=1-z,
first residual N=201, coefficient -1.
```

The kernel checks its exact first residual and strict gap and excludes the
word independently via the conditional polynomial theorem. This both catches
an overstatement of minimality and exercises residual orders far greater
than 13. The general theorem `Morphism.universal_high_degree_certificate`
also supplies a closing pair of every raw degree `d>=6` for every admissible
morphism, with order at least `2*d+1`.

Independent exact Python search records the first failure of the worst-parameter
ledger for degrees 0 through 5 as `L=2,2,2,7,16,101`, respectively. Those
minimal-length observations are **finite-domain-verified**, not promoted to
extra Lean minimal-length theorems.

## Scope audit

The polynomial existence theorem applies to all integer coefficient sequences.
The rational-series periodicity theorem applies to every binary sequence and
is independent of any automatic-word or Collatz hypothesis. These broad
algebraic facts do **not** extend the Collatz exclusion to all automatic words:
its signed tower, height and numerical bounds are proved for the specified
binary uniform equal-weight images.

For a substitution on a larger parent alphabet, even common coded image
weight `r` would only yield the block recurrence

```text
2^L*x_(n+1) = 3^r*x_n + c_(parent_n)*q.
```

The current scalar reduction needs the additional identity
`c_a=c0+(c1-c0)*code(a)` for every parent symbol `a`, with compatible coded
block identities. Arbitrary larger-alphabet substitutions supply neither that
identity nor the scalar polynomial multiplier used by the tower. A vector
Mahler system would require new transport and height theorems. Unequal weights
replace `3^r` by a symbol-dependent multiplier; the existing `101/010` rational
counterexample continues to block deleting this hypothesis. No extension to
these domains is claimed.

## Primary-literature comparison (consulted 2026-11-14 UTC)

This is a limited comparison of hypotheses, not a novelty certification. None
of these external theorems is an assumption in the Lean dependency chain.

- Yann Bugeaud and Jia-Yan Yao, *Hankel determinants, Padé approximations, and
  irrationality exponents for p-adic numbers*, Ann. Mat. Pura Appl. 196 (2017),
  929–946; [author PDF](https://irma.math.unistra.fr/~bugeaud/travaux/p-adic18.pdf)
  and [author publication list](https://www.math.unistra.fr/~bugeaud/publi.html).
  Theorem 3.1 (PDF p. 6) studies values at `p^w` under a Mahler recurrence and
  Hankel conditions; Theorem 1.1 treats Thue–Morse at those points. The present
  Collatz point is `2^L/3^r`, with a nontrivial odd denominator, and the Lean
  conclusion is rational exclusion, not an irrationality exponent or
  transcendence theorem. **Inference:** this is related methodology, but the
  displayed theorem is not a direct substitution for the proof here.
- Boris Adamczewski and Colin Faverjon, *Méthode de Mahler: relations linéaires,
  transcendance et applications aux nombres automatiques*, Proc. London Math.
  Soc. 115 (2017), 55–90; [arXiv v2](https://arxiv.org/pdf/1508.07158v2).
  Théorème 1.2 concerns relations at regular complex algebraic points with
  `0<|alpha|<1`. **Inference:** a complex statement alone does not justify this
  2-adic evaluation; some present cases even have `2^L/3^r>1` in the real
  absolute value. No analytic lifting theorem is imported.
- Josefina López and Peter Stoll, *The 3x+1 Periodicity Conjeture in R*,
  [arXiv:2101.12747v1](https://arxiv.org/pdf/2101.12747v1).
  The full author preprint was consulted around the real/2-adic identification
  in Section 2, equations (15)–(16). The earlier repository audit in
  `infinite-itineraries.md` §2.2 remains relevant. Phase 8 does not identify
  real and 2-adic limits or invoke the broader density claim in that preprint.

The Padé/Mahler framework is established prior mathematics. This comparison
does not establish that the all-equal-weight statement, its proof, or its
formalization is new. A complete prior-art review and independent mathematical
review remain appropriate before making any such claim.
