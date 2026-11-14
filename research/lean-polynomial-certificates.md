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
parity. Non-identical-zero residual still needs the periodicity bridge B.
The expanded audit includes all 44 new declarations (201 total).
