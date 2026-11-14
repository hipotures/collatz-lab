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
Further degree/order results and the limited primary-literature comparison
are recorded below.
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

## E2: minimum uniform degree within the implemented certificate interface

**Lean-kernel-verified:**
`MinimalCertificate.universal_certificate_degree_iff d` proves that a closing
polynomial certificate of degree at most `d` exists for every admissible
morphism **if and only if `6<=d`**, allowing arbitrary residual orders and
arbitrary integer coefficients. The definition `UniversalCertificateDegree`
includes the nonzero denominator, first residual, degree/order bound and the
exact `PolynomialPair.Gap` used in milestone A. This is a lower bound within
that explicit interface; it says nothing about stronger height estimates,
other exclusion methods, or transcendence proofs.

For the lower bound, a single admissible length-1000 example is constructed.
Its one-image starts

```text
110100010011
```

then has ones through position 998, and a zero at 999. Its zero-image swaps
the bits at positions 0 and 999. Both weights are 993, they are distinct and
prolongable at 1, and their last disagreement is 999. These properties are
checked directly in the kernel.

For each `d=0,...,5`, the `(d+1)` equations at coefficient indices
`d+1,...,2*d+1` have an invertible denominator matrix. Its entries are
`w_(d+1+i-j)` and depend only on the displayed twelve symbols. The six
integer linear systems are explicitly expanded and solved by Lean's `omega`;
no determinant assertion is assumed. Therefore any nonzero denominator of
raw degree `d<=5` must have its first residual at some `N<=2*d+1`.

For all those degrees the exact inequality

```text
12*(2*d+1)*1000*999 <= 19*993*(d*999+1999)
```

and `2^19<=3^12` prove failure of the required base gap even at the largest
possible `N`. Smaller `N` only weakens that gap. Twelfth-power comparison
avoids evaluating the multi-million-bit ledger integers. Thus **no**
nonzero-denominator pair of degree at most five can certify this particular
word through the implemented gap.

The positive direction uses the already proved universal degree-six theorem.
An independent explicit certificate for the hard example is also checked:

```text
P0=1+2z-z^3-2z^4-4z^5-z^6,
P1=-1-z+z^2+z^3+2z^4+z^5-z^6,
N=13, first coefficient -1.
```

The existing numerical ledger closes it, and the conditional polynomial
theorem excludes its rational seeds independently. The Python regression
checks the six matrix determinants as `[1,-1,1,-1,-1,-1]`, the actual weights
and disagreements, the small exponent comparisons, and this explicit pair.
These finite checks support the kernel proof but do not replace it.

## E3: exact rational-series characterization for bounded integer sequences

**Lean-kernel-verified:** for every bounded integer sequence, a nonzero
integer denominator polynomial gives a coefficientwise rational identity
if and only if the sequence is eventually periodic.

`BoundedRationalSeries.lean` extends the forward bridge from binary symbols
to any fixed signed integer interval. Translate each symbol by the lower
endpoint and encode a length-`d` window in the alphabet's base. A positional
pair lemma proves injectivity, including the singleton base-one case.
The shared deterministic-window theorem then supplies eventual repetition.
The polynomial recurrence argument is unchanged and never assumed binary
symbols. Existing binary public theorem signatures are retained.

Conversely, given an eventual period `p>=1` starting at `start`, use
`P1=1-z^p` and choose the numerator to cancel the first `start+p+1`
coefficients. Every later residual is `v_n-v_(n-p)=0`. The raw common degree
is kept, and `P1(0)=1` proves a nonzero denominator.

Independent kernel examples cover the alphabet `{-2,3}`, the singleton
`{-7}`, and the unbounded sequence `v_n=n`. The latter has the exact rational
identity `(1-z)^2*F-z=0`, but is proved nonperiodic and unbounded. Thus the
boundedness hypothesis in the forward bridge cannot simply be removed.
Python independently checks 5,635 signed-alphabet window encodings and the
three coefficient identities at their stated finite sizes.

This is a standalone statement about generating functions, not the assertion
that a rational Collatz seed has a rational generating function of its parity
symbols. No extra Collatz alphabet or automatic-word class is covered by
this extension alone.

## E4: actual premature non-unit valuation failure

**Lean-kernel-verified:** the already committed secondary Padé row at search
degree 10 has residual order 21 and first coefficient 24 (`v2=3`). At tower
level zero the spacing is also 3, so the strict domination hypothesis fails.
For the exact 256-symbol Collatz prefix seed in the Phase 7 evidence, the
integral form has valuation **68**, whereas the premature expression
`21*3+3` would give **66**. At level one the spacing is 9 and the exact
valuation is `21*9+3=192`.

`PrematureValuation.lean` checks the coefficient identity, first residual,
strict gap, actual 256-symbol prefix, both finite tower congruences at
length 22, exact forms and both valuations. It also independently excludes
the secondary word through the general non-unit polynomial theorem.

The seed realizes a finite prefix, not the infinite word. The counterexample
refutes the all-level **arithmetic inference from finite residual and tower
congruence data**; it is not an infinite rational realization. It confirms
that the strict spacing condition in `nonunit_leading_valuation` cannot be
deleted. The coefficient-8 Thue–Morse example happened to retain the formula
at level zero, so that example alone would not catch this stronger shortcut.
No Padé search bound or existing artifact was extended or regenerated to
obtain this regression; the degree-ten row was already in the verified table.

## E5: coefficient bounds and a uniform valuation starting level

**Lean-kernel-verified:** every admissible morphism has a chosen degree-six
certificate whose leading residual valuation is below 70. The same safe
starting level **k=6** therefore works for that chosen certificate across
all lengths and images. This concerns the valuation argument, not a uniform
upper bound on residual order or on the later height-contradiction index.

`BoundedLinear.integer_null_vector_bounded` quantifies the division-free
construction. If the original matrix entries have absolute value at most
`H>=1`, elimination bounds each reduced entry by `2*H^2`. Reconstruction
bounds the new vector by `m*H` times the preceding bound. The recursive
quantity is

```text
B(0,H)=1,
B(m+1,H)=(m+1)*H*B(m,2*H^2).
```

Its positivity and the vector bounds are proved for arbitrary dimensions,
including zero columns, deficient rank, negative entries and zero matrices.
For six binary rows the kernel computes

```text
X = B(6,1) = 720*2^57 = 103762935414616227840.
```

`UniformStart.lean` chooses denominator coefficients bounded by `X`, and
numerator coefficients bounded by `7*X`. Consequently

```text
norm(P) <= 2+56*X,
heightConstant(P) < 2^76.
```

The first residual index is still allowed to be arbitrarily large. Since
`N>=13>6`, its coefficient is a convolution of seven bounded denominator
coefficients with binary symbols. Its absolute value is at most `7*X<2^70`.
The exact factorization `R_N=2^val*c_odd` therefore has `val<70`. At any
`k>=6`, `L^(k+1)>=2^7=128>val`, so the non-unit valuation theorem applies.

`Morphism.universal_bounded_degree_six_certificate` exports all this data
before any seed is chosen. `universal_degree_six_valuation` gives exact
valuation, divisibility, next-power nondivisibility and the absolute lower
bound at every `k>=6` for a hypothetical realization. The original universal
exclusion theorem is unchanged. Arbitrarily long finite rational prefix
realizations remain consistent with these bounds: the height contradiction
still depends on the seed height and the required prefix precision grows
with the tower level.

The independent exact Python implementation checks the vector bounds on its
144 matrices, the constant `X`, both power caps, and the coefficient/height
bounds of its explicit binary-word fixtures. No finite binary-prefix cache
is used in the universal proof.

## E6: finite nonzero conditions of the certificate interface

**Lean-kernel-verified:** `PolynomialPair.first_pair_nonzero` derives a
nonzero polynomial pair from the finite `First` condition alone.
`first_gap_denominator_nonzero` derives a nonzero denominator from `First`
and `Gap`, for every integer coefficient sequence and every image length.
Neither result uses a rational realization, aperiodicity or any exclusion theorem.

If all denominator coefficients are zero, convolution vanishes, so a nonzero
first residual must be a numerator coefficient at index `N<=degree`.
Since `m>=2^L`, monotonicity then gives

```text
2^(L*(L-1)*N) <= m^(degree*(L-1)+L+e),
```

contradicting `Gap`. The claimed nonzero data are therefore consequences of
explicit finite arithmetic inputs, not a hidden rationality assumption.
All constructed universal certificates also supply the nonzero denominator
independently from linear algebra. Primitivity is unnecessary: the norm and
leading-coefficient factorization already handle common integer content and
common powers of `z`.

The final local audit includes all **149** new Phase 8 theorem exports and
retains every **157** baseline audit entry, for **306** declarations total.
The actual Collatz definitions, `RealizesWord`, fixed-point definition,
signed tower, Rust CLI, Rust tests and Cargo dependencies are unchanged from
the starting commit. A clean rebuild and all full checks pass.
