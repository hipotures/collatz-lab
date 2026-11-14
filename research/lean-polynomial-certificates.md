# General polynomial certificates — Phase 8

## Verified conditional theorem

`CollatzLab.no_rational_seed_with_polynomial_pair` is a general conditional
exclusion theorem, without a unit-leading-coefficient assumption. Its inputs
are exactly H1–H3, `L >= 2`, a `PolynomialPair P`, an order `N >= P.degree`,
`P.First (Morphism.parityWord M) N`, and `P.Gap M N`. Its conclusion is
`¬ RealizesWord p q (Morphism.parityWord M)` for arbitrary integers `p,q`.
`no_rational_seed_with_shifted_polynomial_pair` and
`no_eventually_shifted_polynomial_pair_itinerary` cover finite shifts and
all eventual shifted matches. The existing rational semantics are unchanged.

This is milestone A. It does **not** establish pair existence for arbitrary
words or the unconditional equal-weight theorem. Those need milestones B–D.

## Representation and finite identity

`PolynomialPair` stores `degree : Nat` and `p0,p1 : Nat → Int`. Only indices
`0,...,degree` are used; all higher values are ignored. Index zero is the
constant coefficient. Trailing zero coefficients are kept. Evaluation is
homogenized to this common raw degree:

```text
eval(p,a,b,d) = sum(j=0..d) p_j a^j b^(d-j).
R_n = [n<=d] p0_n + sum(j=0..min(d,n)) p1_j w_(n-j).
E_k = D_k eval(p0,a_k,b_k,d) + eval(p1,a_k,b_k,d) u_k.
```

`residual_identity` proves, for every `n >= d+1` and **arbitrary signed integer
coefficients and symbols**, the exact finite identity

```text
b^(n-1) eval(p0,a,b,d) + eval(p1,a,b,d) pre(w,a,b,n)
  = b^d pre(R,a,b,n) + a^n tail(p1,w,a,b,n,d).
```

`tail` is explicitly recursive, equivalently
`sum(j=1..d) p1_j b^(d-j) pre(w shifted by n-j,a,b,j)`.
The identity is valid at zero and negative bases too; the tower subsequently
provides positive coprime bases. No analytic series convergence is involved.

## Nonzero assumptions and valuation

`First P w N` asserts all coefficients below `N` vanish and `R_N != 0`.
No irrationality assertion is a certificate premise. The integral coefficient
factorization `int_two_power_factorization` proves `R_N=2^v*c` with odd signed
`c` from `R_N != 0`, including negative coefficients.

`tower_residual` combines the finite identity at length `N+1` with the existing
signed tower congruence. It yields an explicit integer `T` such that

```text
b_k^N E_k = a_k^N (D_k b_k^d R_N + a_k T).
```

`tower_divisibility` proves `a_k^N | E_k` at **every** level by Bezout.
For `v < L^(k+1)`, `PolynomialPair.valuation` additionally gives

```text
E_k != 0,
2^(N L^(k+1)+v) | E_k,
2^(N L^(k+1)+v+1) does not divide E_k,
2^(N L^(k+1)+v) <= |E_k|.
```

It uses `nonunit_leading_valuation` on the bracket above and cancels the odd
factor `b_k^N` by Bezout. Odd signed denominators preserve the coefficient's
valuation. `finite_start_for_leading_coefficient` supplies a finite `k0`.
`no_eventual_doubly_exponential_bound` proves the growth contradiction from
bounds only for `k>=k0`, by shifting the level and taking positive integer
powers of the two bases. No assertion about the discarded levels is needed.

## Height ledger

Let `norm P = 2 + sum(j=0..d)(|p0_j|+|p1_j|)` and `C=(d+1)*norm P`.
These definitions are executable, strictly positive, and independent of `k`.
`eval_bound`, `form_bound` and `form_power_bound` prove

```text
|E_k| <= C m_k^d H_k,
|E_k|^(L-1) <= C^(L-1) H_0^(L-1) ((2L)^(L-1))^k
                * m^((d*(L-1)+L+e)*L^k).
```

The existing height recurrence handles both base orderings and signs.
Consequently the sufficient strict gap is exactly

```text
m^(d*(L-1)+L+e) < 2^(L*(L-1)*N).
```

The fixed coefficient norm and the singly exponential factor are retained
in the contradiction. No leading-coefficient magnitude is assumed bounded
uniformly over all pairs or all words.

## Regressions and trust

`PolynomialChecks.lean` kernel-checks the period-two secondary pair, the old
period-six Thue–Morse control as a general pair, and the degree-six Thue–Morse
pair with order 13 and coefficient **8**. The conditional general theorem
independently excludes both named words, preserving their older proofs.
A concrete 64-bit actual Collatz prefix seed `3195543223027673837` gives form
valuations 29 and 55 at levels zero and one. These are finite witnesses,
not an infinite realization. Level one is the first level at which the
**general** coefficient-8 domination condition holds; level zero happens to
have the same formula for this specific witness.

`research/phase8/verify_polynomial.py` independently checks 686 signed
convolution identities, height inequalities, and both concrete form values.
It uses Python exact integers and supplies regression evidence only.

All 33 new exported theorems at checkpoint A are included in the existing
exact-name/order audit (190 declarations total); only standard foundations
are permitted. No dependency or proof escape is added. The project remains
Lean 4.18.0 with no Mathlib or other packages. CI includes both the kernel
proofs and the independent finite checker. Validation and pushed commits
are recorded in `phase8-progress.md`.

## C: universal pair existence (Lean-kernel-verified)

`FiniteLinear.integer_null_vector` proves the following general theorem,
using a finite dot product `dot`:

```lean
∀ m : Nat, ∀ A : Nat → Nat → Int,
  ∃ x : Nat → Int, (∃ j, j < m + 1 ∧ x j ≠ 0) ∧
    (∀ i, i < m → FiniteLinear.dot (A i) x (m + 1) = 0)
```

Induct on `m`. If column zero is zero, its unit vector works. Otherwise let
row `r` have nonzero coefficient `a=A(r,0)`. Delete that row and column zero,
and form `B(i,j)=a*A(i,j+1)-A(i,0)*A(r,j+1)`. Induction gives a nonzero
integer vector `y` in its kernel. Reconstruct
`x_0=-sum(j) A(r,j+1)*y_j` and `x_(j+1)=a*y_j`.
The pivot equation holds identically; the other equations are exactly `B*y=0`.
Since `a!=0`, a nonzero coordinate of `y` gives a nonzero coordinate of `x`.
The `skip_surjective` lemma checks row deletion for every pivot position.
This includes deficient rank, empty matrices and negative entries, without
division, rational arithmetic, determinants or a rank assumption.

`PolynomialPair.polynomial_pair_exists d v` applies this to the `d` equations
at indices `d+1,...,2*d`, with `d+1` denominator coefficients. Numerator
coefficients are the negative convolution at indices `0,...,d`.
Its signature is uniform over **all integer sequences**, stronger than the
binary case required by the issue:

```lean
∃ P : PolynomialPair, P.degree = d ∧
  (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧
  (∀ n, n < 2 * d + 1 → P.residual v n = 0)
```

`degree_six_pair_exists` specializes to `d=6`, order at least 13.
The raw degree is retained; no common power of `z` is removed. There is no
bound on the first **nonzero** residual index and no assertion about its
parity. Non-identical-zero residual is supplied by the periodicity bridge B
in the next section.
The expanded audit includes all 44 new declarations (201 total).

## B: coefficientwise rational binary series are eventually periodic

`RationalSeries.rational_binary_eventually_periodic` takes any integer sequence
`v` with `v n = 0 ∨ v n = 1`, any raw polynomial pair `P`, a nonzero coefficient
of its denominator within the raw degree, and the identity
`∀ n, P.residual v n = 0`. It concludes `EventuallyPeriodic v`.

The proof is independent of all Collatz rational-exclusion theorems. Choose
the first nonzero denominator coefficient `p1_s`. For sufficiently late
indices, the numerator is absent. Comparing the recurrences at
`a+d+s` and `b+d+s`, coefficients before `s` are zero, and coefficients after
`s` inspect the preceding length-`d` windows. Equal windows therefore force
`p1_s*v(a+d)=p1_s*v(b+d)`. Integer cancellation gives equal next symbols,
without dividing by that coefficient or requiring it to be a unit.

`deterministic_binary_periodic` encodes each such window as a natural number
strictly below `2^d`. The existing elementary bounded-collision theorem finds
two equal windows. Strong induction extends their equality to every future
symbol, supplying an explicit eventual period. The empty window `d=0` is
included; it forces the tail to be constant. The proof keeps the raw pair
and handles any common initial power of `z`.

`RationalSeries.nonzero_residual` exports the contrapositive for every
nonperiodic binary sequence. Independent checks cover a finite impulse with
constant denominator `-3`, an alternating series with common factor `z^2`
and negative determining coefficient, and nonzero residuals of Thue–Morse.
The exact audit now has 214 declarations, including all new B theorems.

## D: unconditional universal equal-weight exclusion

`UniversalEqualWeight.lean` composes A–C with the Phase 7 aperiodicity and
numerical ledger. The main public signature is exactly:

```lean
theorem CollatzLab.no_rational_seed_realizes_all_equal_weight
    {L : Nat} (hL : 2 ≤ L) (M : CollatzLab.Morphism.Images L)
    (h1 : CollatzLab.Morphism.image M true 0 = true)
    (hw : CollatzLab.Morphism.weight (CollatzLab.Morphism.image M false) L =
          CollatzLab.Morphism.weight (CollatzLab.Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (p q : Int) :
    ¬ CollatzLab.RealizesWord p q (CollatzLab.Morphism.parityWord M)
```

`no_rational_seed_realizes_shifted_all_equal_weight` quantifies over every
finite shift and arbitrary integer `p,q`. The eventual analogue is
`no_eventually_shifted_all_equal_weight_itinerary`, with arbitrary start
indices `s,t` and positive odd `q`. `no_integer_seed_realizes_all_equal_weight`
specializes the denominator to 1.

`Morphism.universal_degree_six_certificate` first supplies an actual pair
and order, before any rational-realization assumption is introduced:

```text
exists P,N: degree(P)=6, N>=13, P1 nonzero, First(P,word,N), Gap(P,M,N).
```

The denominator is nonzero by C. If its residual vanished at every index,
B would force eventual periodicity, contradicting Phase 7's theorem under
exactly H1–H3. A nonzero residual coefficient therefore exists. Applying
the finite first-nonzero-coefficient lemma up to that witness gives a least
index `N`, and the initial cancellations give `N>=13`. Monotonicity of powers
of 2 lifts the degree-six/order-13 ledger to this possibly larger `N`.
A applies, including arbitrary `v2(R_N)` and its finite starting level.
There is no finite upper bound on `N`, on `L`, or on coefficient magnitudes.

### Semantics and adversarial audit

The proof quantifies over arbitrary `Images L`; no finite list appears in
its signature or dependency chain. No criterion (C), subcritical inequality,
chosen control, nonperiodicity assumption or irrationality assertion is
added to the public theorem. Nonperiodicity is a separately proved consequence
of H1–H3. The argument does not depend on the older named rational-exclusion
proofs, which remain available as independent cross-checks.

`RealizesWord` and all actual Collatz definitions are unchanged. The theorem
covers every integer numerator and every positive odd denominator, including
negative numerators and unreduced fractions. Backward inverse branches used
for shifts retain that domain. It excludes a particular class of infinite
itineraries; it makes no claim about the behavior of every integer orbit or
the general rational 2-adic Periodicity Conjecture.

The new `supercriticalSix` example has literal images `1 -> 101011`,
`0 -> 011011`, with `r=4`, `A=64`, `B=81`, `s=0`, `e=1`, `t=1`, `N_old=6`.
The kernel checks `A<B` and failure of (C). The universal theorem excludes
it directly. An independent explicit raw degree-six pair

```text
P0=-z-z^3+z^4-z^5, P1=z-z^4
```

has first residual at 13 with coefficient 1 and closes `81^37<2^390`.
Its common initial factor is retained, exercising the raw-pair convention.

`UniversalChecks.lean` also derives the old Thue–Morse, secondary, sigma and
reverse-order cases from the new theorem without deleting their old proofs.
Independent literal two-step substitutions and actual positive and negative
rational prefix witnesses are checked for representative lengths 2 through 6.
At length 6 the numerator `11999337121` reaches `49315963742` after 36 steps;
the negative seed `(-8722791131)/5` and its unreduced representation with
denominator 15 have the same prefix. Their parity equivalence is proved at
**every** index using `numIter_equiv`, not inferred from that prefix.
Explicit infinite all-zero and negative all-one realizations verify that the
infinite predicate remains satisfiable outside the morphism hypotheses.

All 76 new Phase 8 exported declarations are now audited (233 total), using
only approved standard foundations. All finite checks use exact arithmetic;
none substitutes for the universal kernel proof. See the campaign journal
for actual validation, pushed commits and CI results.

## E: exact limits of the dimension-count ledger

`DegreeTradeoff.lean` proves `universal_dimension_gap_iff`: the uniform ledger
with guaranteed order `2*d+1` holds exactly when `6<=d`. The counterexample
for all smaller degrees is realized by `highWeight101`, an admissible
length-101 pair with `r=e=100`. This is a statement about the **specific
ledger and guaranteed order**, not the smallest possible individual certificate.
Indeed `highWeight101Low` is an independent degree-two certificate with order
201 and coefficient -1, accepted by `no_rational_seed_with_polynomial_pair`.

`Morphism.universal_high_degree_certificate` supplies a valid closing
certificate at every raw degree `d>=6`, with order at least `2*d+1`, for every
admissible equal-weight morphism. The degree-six main theorem stays unchanged.
The findings report records scope limits and primary-literature comparisons;
none of the external sources is a proof dependency or a novelty certificate.

## E2: sharpness for arbitrary residual orders

`MinimalCertificate.lean` strengthens the guaranteed-order ledger audit:
`UniversalCertificateDegree d ↔ 6<=d` for the exact certificate interface
above, even when pairs may have arbitrarily high first residual order.
`hardImages` is an admissible length-1000 counterexample to every degree
bound at most five. `prefix_kernel` checks six small nonsingular systems;
`prefix_order_bound` uses them to force `N<=2*d+1`. Then
`hard_small_degree_ledger_failure` and `hard_no_small_certificate` rule out
closing the gap. All coefficients, raw common factors and orders are quantified.

This formal lower bound concerns the specified coefficient/height ledger,
not arbitrary possible irrationality arguments. The degree-two/order-201
length-101 example remains a useful illustration that individual words can
have smaller certificates. The findings report gives the hard example's
explicit degree-six pair and its exact proof mapping. The expanded audit is
258 declarations (all 101 new Phase 8 theorem exports included).

## E3: bounded integer coefficients and the converse

`RationalSeries.rational_bounded_integer_eventually_periodic` takes any
sequence with `∃lo hi:Int, ∀n, lo<=v_n<=hi`, a nonzero denominator and the
coefficientwise identity. The conclusion is `EventuallyPeriodic v`.
`bounded_nonzero_residual` exports its contrapositive.
`eventually_periodic_rational_pair` proves the reverse implication for every
integer sequence by constructing denominator `1-z^p`; together they give
`bounded_rational_iff_periodic`.

The finite repetition proof is shared through `deterministic_window_periodic`;
all old binary theorem signatures remain unchanged. The generic window uses
an arbitrary signed interval, and `radix_pair_injective` includes base one.
The unbounded sequence n is a checked counterexample to deleting boundedness.
The Collatz theorem's domain remains the binary equal-weight uniform class.
The complete audit now has 276 declarations, including all 119 new exports.

## E4: the finite starting level is arithmetically necessary

`PrematureValuation.lean` reuses the existing secondary degree-ten row,
`N=21`, `c=24`, `v=3`. An actual 256-symbol prefix seed satisfies the finite
tower congruences at levels zero and one. The kernel computes exact form
valuations 68 and 192. Level zero therefore violates the premature formula
`N*3+v=66`; level one satisfies `N*9+v=192`. This demonstrates a failure of
the finite arithmetic shortcut, without asserting an infinite realization.
The old coefficient-8 regressions remain independent. All eight new exports
are in the expanded exact audit (284 declarations total).
