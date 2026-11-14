# Generic equal-weight criterion — Lean-kernel-verified (Phase 7 B)

**Theorem 8.1 and its shifted-tail corollaries are accepted by Lean 4.18.0**,
with exactly H1–H3 and criterion (C). Length and both images are arbitrary
parameters: this is one generic theorem, not a finite catalogue. Existing
family and original-word proofs remain independent.

No Collatz, CST, general Periodicity or arbitrary automatic-word theorem is
claimed. Failure of (C) has no rational-realizability consequence.

## Exact public signatures

These are exported by `import CollatzLab`:

```lean
theorem CollatzLab.no_rational_seed_realizes_equal_weight
    {L : Nat} (hL : 2 ≤ L) (M : CollatzLab.Morphism.Images L)
    (h1 : CollatzLab.Morphism.image M true 0 = true)
    (hw : CollatzLab.Morphism.weight (CollatzLab.Morphism.image M false) L =
          CollatzLab.Morphism.weight (CollatzLab.Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hC : CollatzLab.Morphism.Criterion M) (p q : Int) :
    ¬ CollatzLab.RealizesWord p q (CollatzLab.Morphism.parityWord M)

theorem CollatzLab.no_rational_seed_realizes_shifted_equal_weight
    {L : Nat} (hL : 2 ≤ L) (M : CollatzLab.Morphism.Images L)
    (h1 : CollatzLab.Morphism.image M true 0 = true)
    (hw : CollatzLab.Morphism.weight (CollatzLab.Morphism.image M false) L =
          CollatzLab.Morphism.weight (CollatzLab.Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hC : CollatzLab.Morphism.Criterion M) :
    ∀ (t : Nat) (p q : Int),
      ¬ CollatzLab.RealizesWord p q
        (CollatzLab.shiftWord (CollatzLab.Morphism.parityWord M) t)

theorem CollatzLab.no_eventually_shifted_equal_weight_itinerary
    {L : Nat} (hL : 2 ≤ L) (M : CollatzLab.Morphism.Images L)
    (h1 : CollatzLab.Morphism.image M true 0 = true)
    (hw : CollatzLab.Morphism.weight (CollatzLab.Morphism.image M false) L =
          CollatzLab.Morphism.weight (CollatzLab.Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hC : CollatzLab.Morphism.Criterion M)
    (s t : Nat) (p q : Int) (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, CollatzLab.seedParity q p (s+j) =
      CollatzLab.Morphism.parityWord M (t+j))
```

`RealizesWord` is unchanged: positive odd `q` and equality of **actual**
accelerated Collatz parities at every index. There is no numerator sign,
reducedness, height or search bound. The existing `numStep`, `numIter`,
integer specialization and rational inverse branches are used directly.

## Parameters and word semantics

`Morphism.Images L` stores `zero, one : Fin L → Bool`. `image` selects the
finite image below `L` and is false beyond it. `word` is a fuelled fixed point
starting in true, independent of any seed; `parityWord` converts Bool to 0,1.
`word_block`, `literal_block`, `word_unique` prove the recurrence, equality
with the selected literal finite image, and uniqueness among fixed points
**starting at 1**. This qualification matters for `10/01`.

`weight_positive`, `one_has_zero`, `weight_lt_length`, `t_bounds`, `se_bounds`,
`s_lt_e` derive `1<=r<L`, `1<=t<L`, `0<=s<e<L` from H1–H3. Canonical `t,s`
are finite first-index searches; `e` is a finite last-index search.
`N=L*t+s`, `A=2^L`, `B=3^r`, `m=max(A,B)`, and `Criterion M` is literally

```text
2^(L*(L-1)*N) > max(A,B)^(L*L+e).
```

There is no `A<B` assumption and no rounded or logarithmic comparison.

## Dependency map

Names without another qualifier have prefix `CollatzLab.Morphism`.

| Component | Kernel declarations | Module |
|---|---|---|
| Images, correct fixed point, literal blocks | `word_rec`, `word_block`, `word_unique`, `literal_block`, `parity_binary` | `MorphismWord` |
| Actual Collatz affine offsets and all finite seed identities | `affine_prefix`, `numIter_block`, `g_step`, `base_identity` | `MorphismWord`, `MorphismPrefix` |
| Finite homogeneous Mahler identity | `prefix_mahler` | `MorphismPrefix` |
| Signed offset valuation and exact quotient | `offset_difference`, `offsets_odd_multiple`, `kappa_spec` | `MorphismOffset`, `MorphismTower` |
| Multiplier support factor and odd unit | `gamma_factor`, `gammaStar_odd`, `s_lt_e` | `MorphismPolynomial` |
| Exact cancelled tower, all levels and lengths | `delta_exact`, `congruence_step`, `initial_exact`, `initial_divisibility`, `normalized_base`, `tower_congruence`, `tower_exact` | `MorphismTransport`, `MorphismTower` |
| Positive denominator model and signs | `positive_denominator_props`, `positive_denominator_initial`, `positive_denominator_step`, `positive_tower_step` | `MorphismTower` |
| First disagreement, unit residual, exact valuation | `first_disagreement`, `residual_identity`, `residual_first`, `odd_multiple`, `valuation` | `MorphismOffset`, `MorphismApprox` |
| General coefficient and height bounds | `sum_bound`, `Q_bound`, `GammaStar_bound`, `height_step`, `height_power_closed`, `form_power_bound` | `MorphismHeight` |
| Strict gap dominates singly exponential factors | `CollatzLab.homogeneous_bernoulli`, `amplify_integer_gap`, `no_doubly_exponential_bound` | `ExponentialGap` |
| Universal theorem and tails | public signatures above | `EqualWeight` |
| Independent concrete semantics and specializations | `independent_prefix_witnesses`, `no_rational_seed_realizes_sigma`, `no_rational_seed_realizes_reverseOrder` | `EqualWeight`, `EqualWeightChecks` |

## Exact division, signs and valuation

From actual Collatz blocks, put `g_n=(B-A)*numIter q p (L*n)+c0*q`. For every
`n>=1` the raw finite identity is

```text
B^(n-1)*(B*g_0)-((B-A)*(c0-c1)*q)*pre(A,B,n)=A^n*g_n.
```

The initial quotient is proved exact. Normalized base congruences use old
length **`n+1`** before cancelling `2^s`, retaining the full modulus `A^n`.
`initial_divisibility` also proves `2^s | g_0` by coprimality with `B`.

The internal executable tower is signed:

```text
D_0=(B-A)*kappa*q, u_0=B*g_0/2^s,
D_(k+1)=D_k*GammaStar_h(a_k,b_k)*(b_k^L-a_k^L),
u_(k+1)=b_k^e*(delta_k/a_k^s).
```

`delta_exact` proves `a_k^s | delta_k` before using the quotient. Transport
uses old length **`L*(n+1)`**, cancels the positive `a^s`, then a coprime
power of `b`. The entire new modulus survives. The exact multiplier factor
is `Gamma_h=a^s*b^(L-1-e)*GammaStar_h`. Every signed denominator is odd and
nonzero, with no assumed ordering of the bases or sign of `kappa`.

The proved positive model is `positiveD=absInt D`,
`positiveU=sign(D)*u`. Its initial denominator is exactly
`abs(B-A)*abs(kappa)*q`; its recurrence multiplies absolute values, and
`positive_tower_step` supplies an explicit sign in `{1,-1}`. Thus the paper's
positive-odd convention is satisfied, including both signs at every level.

The periodic residual first differs at exactly `N=L*t+s`, with leading
coefficient 1 or -1. A finite convolution identity makes its remaining tail
an explicit multiple of `a^(N+1)`. The congruence at length `N+1` proves
`E_k` is an odd multiple of `a_k^N`. `valuation` gives nonvanishing,
divisibility by `2^(N*L^(k+1))`, nondivisibility by the next power, and the
ordinary absolute lower bound, at every level and for either denominator sign.

## Heights and strict-gap contradiction

With `H_k=|u_k|+|D_k|`, the kernel checks

```text
H_(k+1) <= 2L*m_k^(L+e)*H_k, m_k=m^(L^k),
H_k^(L-1) <= H_0^(L-1)*(2L)^(k*(L-1))*m^((L+e)*(L^k-1)),
|E_k|^(L-1) <= K*Dbase^k*m^((L^2+e)*L^k),
K=L^(L-1)*H_0^(L-1), Dbase=(2L)^(L-1).
```

General homogeneous sums are bounded by coefficient norms. The factor
`(2L)^k` is retained. The lower bound would force
`alpha^(L^k)<=K*Dbase^k*beta^(L^k)` for all `k`, where
`alpha=2^(L*(L-1)*N)>beta=m^(L^2+e)`.

`no_doubly_exponential_bound` handles **any** strict positive integer gap.
Homogeneous Bernoulli inequalities amplify it at a finite index `J`;
shifting to `J+t` forces `2^t<=K*Dbase^J` for all `t`. This contradicts
`t<2^t` at `t=toNat(K*Dbase^J)`. No asymptotic claim or extra analytic axiom
replaces this finite-index argument.

## Non-vacuity, independent instances and validation

- `sigma=110/011`, with `L=3,t=2,s=0,e=2,N=6,A=8,B=9`, satisfies (C).
  The generic specialization compiles; actual integer 187 realizes the first
  nine literal symbols. This is the non-original upstream example.
- `reverseOrder=1100/1010`, with `L=4,t=2,s=1,e=2,N=9,A=16,B=9`, satisfies
  (C). Here `A>B`, cancellation is required, and signed `D_0=-7` at `q=1`.
  Its generic specialization compiles; actual integer 12947 realizes the
  first sixteen literal symbols. This detects hidden base-order assumptions.
- `thueMorse_fails_criterion` remains a checked statement. Its separate
  rational exclusion uses the subcritical theorem.

At B3 the audit has **118 declarations**, permitting only subsets of
`propext`, `Classical.choice`, `Quot.sound`, or no axioms. The three generic
exports use exactly those three standard foundations. There are no extra
unproved assumptions or proof escapes. Standalone infinite series and 2-adic
analytic objects remain outside Lean: all needed finite congruences are
derived directly from `RealizesWord`.

```text
lake clean
lake build
lake env lean research/lean-audit/FamilyAudit.lean
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/mahler-uncovered/verify_uncovered.py --check
```

The clean build, audit, formatting, Clippy, all 93 Rust tests, and deterministic
Python reproduction pass. CI enforces the exact audit count and dependency
format. Pushed commits and CI runs are recorded in `phase7-progress.md`.

Later C2/D2 adds the generic periodic-control criterion and both uncovered
targets' Mahler certificates and the finite catalogue. D4 adds uniform
aperiodicity and further arithmetic, bringing the current audit to 157; see
`mahler-uncovered-morphisms.md`. B3's mathematical theorem is unchanged.
`check_axioms.py` validates exact source declaration names, order and count;
it normalizes only approved-foundation continuation lines in Lean's output,
and rejects diagnostics or every other dependency. Its adversarial self-tests
are part of CI.
