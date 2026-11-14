# Phase 6: the uniform Mahler family in Lean 4 (issue #12)

Theorem 4.1 and Corollary 9.1 of
[`mahler-generalization.md`](mahler-generalization.md) are now accepted by the
Lean 4.18.0 kernel for **every natural number `L >= 4`**. The parameter `L` is
free in the exported theorem; there is no upper bound on `L`, seed height,
or number of iterations. The case `L = 5` (Theorem 5.1) follows by specialization.

The implementation uses exact finite integer identities, not infinite sums
as an additional hypothesis. No rationality or irrationality assertion is
postulated. The existing `RealizesWord`, `numStep`, `numIter`, and public
`L = 4` theorems are unchanged. Rust sources, CLI behavior, deterministic
artifacts, and published schemas are unchanged.

## Exported statements and semantics

Import `CollatzLab`. The full principal signatures are:

```lean
theorem CollatzLab.no_rational_seed_realizes_family
    (L : Nat) (hL : 4 <= L) (p q : Int) :
    ¬ CollatzLab.RealizesWord p q (CollatzLab.familyWord L)

theorem CollatzLab.no_rational_seed_realizes_shifted_family
    (L : Nat) (hL : 4 <= L) :
    ∀ (t : Nat) (p q : Int),
      ¬ CollatzLab.RealizesWord p q
        (CollatzLab.shiftWord (CollatzLab.familyWord L) t)

theorem CollatzLab.no_eventually_shifted_family_itinerary
    (L : Nat) (hL : 4 <= L) (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, CollatzLab.seedParity q p (s + j) =
      CollatzLab.familyWord L (t + j))

theorem CollatzLab.no_int_seed_realizes_shifted_family
    (L : Nat) (hL : 4 <= L) (t : Nat) (p : Int) :
    ¬ CollatzLab.RealizesWord p 1
      (CollatzLab.shiftWord (CollatzLab.familyWord L) t)

theorem CollatzLab.familyWord_four : CollatzLab.familyWord 4 = CollatzLab.w
```

The rational predicate is still exactly:

```lean
def RealizesWord (p q : Int) (v : Nat -> Int) : Prop :=
  q > 0 ∧ q % 2 = 1 ∧ ∀ j : Nat, seedParity q p j = v j

def numStep (q p : Int) : Int :=
  if p % 2 = 0 then p / 2 else (3 * p + q) / 2

def seedParity (q p : Int) (j : Nat) : Int := (numIter q p j) % 2
```

Thus positivity and oddness of `q` are the **only rational-seed side
conditions**. Negative, zero, unreduced, and arbitrarily large numerators
are included. `numStep` preserves the odd denominator and implements the
accelerated Collatz map on `p/q`. Euclidean integer division is exact on
its selected parity branch; the existing `numStep_eq` proves this.
Fraction equivalence is the existing `numIter_equiv` theorem.

`familyWord L n := familyAux L n n` is a structural, fuelled definition,
independent of any seed. Fuel stability proves the unrestricted block
recurrence. For `L >= 3` its unique solution satisfies

```text
w_L(L*m+r) = 1          for r < L-2
w_L(L*m+L-2) = w_L(m)
w_L(L*m+L-1) = 1-w_L(m).
```

`Family.block_images` identifies these blocks, at every offset `r < L`,
with `mu_L(1) = 1^(L-1)0` and `mu_L(0) = 1^(L-2)01`.
`Family.fixed_point` gives function equality with the substitution;
`Family.word_unique` proves uniqueness, and `Family.word_zero` proves the
initial symbol is `1`. `Family.word_binary` proves every symbol is `0` or
`1`. `familyWord_four` identifies this definition with the independently
implemented old word by uniqueness, rather than replacing the old model.

Semantic regressions are compiled as part of the library:

```lean
theorem CollatzLab.familyWord_five_prefix :
    (List.range 25).map (CollatzLab.familyWord 5) =
      [1,1,1,1,0, 1,1,1,1,0, 1,1,1,1,0, 1,1,1,1,0, 1,1,1,0,1]

theorem CollatzLab.family_five_positive_prefix_witness :
    (0 : Int) < 25850607 ∧
    (∀ j : Nat, j < 25 ->
      CollatzLab.seedParity 1 25850607 j = CollatzLab.familyWord 5 j) ∧
    CollatzLab.tIterInt 25850607 25 > 25850607

theorem CollatzLab.realizes_all_zero :
    CollatzLab.RealizesWord 0 1 (fun _ => 0)
```

The positive integer witness follows the actual Collatz map, including
both final changed symbols of the displayed prefix. The two finite
regressions use kernel reduction (`decide`). The infinite all-zero witness
is proved by induction. Together with the unchanged external checks in
[`lean-audit/AuditChecks.lean`](lean-audit/AuditChecks.lean), these distinguish
finite realizability and a satisfiable parity predicate from the impossible
infinite family itinerary.

## Mathematical-to-Lean mapping

Names in the `Family.*` rows have prefix `CollatzLab.Family`.

| Paper obligation | Lean declarations | Source |
|---|---|---|
| Lemma 2.1; literal substitution, binary range, uniqueness | `word_block`, `word_initial`, `word_penult`, `word_last`, `word_binary`, `word_unique`, `fixed_point`, `block_images` | [`FamilyWord.lean`](../CollatzLab/FamilyWord.lean), [`FamilyChecks.lean`](../CollatzLab/FamilyChecks.lean) |
| Original `L=4` model and concrete `L=5` prefix | `CollatzLab.familyWord_four`, `CollatzLab.familyWord_five_prefix` | [`FamilyWord.lean`](../CollatzLab/FamilyWord.lean) |
| Lemma 3.2; `A=2^L`, `B=3^(L-1)`, `c0=B-2^(L-2)`; affine block offsets | `A`, `B`, `c0`, `odd_run`, `numIter_block` | [`FamilyPrefix.lean`](../CollatzLab/FamilyPrefix.lean) |
| Exact initial division and Theorem 3.3 in finite integer form | `initial_divisibility`, `quotient_exact`, `quotient_step`, `base_identity`, `initial_normalization` | [`FamilyPrefix.lean`](../CollatzLab/FamilyPrefix.lean), [`FamilyChecks.lean`](../CollatzLab/FamilyChecks.lean) |
| Lemma 3.1; homogenized finite Mahler equation | `sum`, `geom`, `pre`, `C`, `prefix_block`, `prefix_mahler` | [`FamilyPrefix.lean`](../CollatzLab/FamilyPrefix.lean) |
| Theorem 4.1, Step 1; closed bases and ratio `A/B <= 16/27` | `a_closed`, `b_closed`, `tower_bases`, `bases`, `ab_bounds`, `ab_coprime` | [`FamilyTower.lean`](../CollatzLab/FamilyTower.lean), [`FamilyChecks.lean`](../CollatzLab/FamilyChecks.lean) |
| Positive odd denominators | `D`, `denominator_props` | [`FamilyTower.lean`](../CollatzLab/FamilyTower.lean) |
| Exact cancelled numerator recurrence and all finite congruences | `delta`, `u`, `delta_exact`, `congruence_step`, `tower_congruence`, `tower_exact` | [`FamilyTower.lean`](../CollatzLab/FamilyTower.lean) |
| Step 2; first disagreement at `N=L^2-2` | `before_first_difference`, `first_difference`, `periodic_prefix` | [`FamilyApprox.lean`](../CollatzLab/FamilyApprox.lean), [`FamilyChecks.lean`](../CollatzLab/FamilyChecks.lean) |
| Unit leading coefficient, nonzero linear form, exact valuation, lower bound | `approximant_identity`, `odd_multiple`, `odd_multiple_bounds`, `valuation` | [`FamilyApprox.lean`](../CollatzLab/FamilyApprox.lean) |
| Step 3; `H_(k+1) <= b_k^(2L-1) H_k`, closed height bounds, final upper bound | `geom_bound`, `C_bounds`, `P_bounds`, `height_step_aux`, `height_step`, `height_closed_le`, `height_closed_lt`, `form_upper` | [`FamilyHeight.lean`](../CollatzLab/FamilyHeight.lean) |
| Step 4; all-`L` base-exponent inequality and contradiction | `exponent_gap`, `base_gap`, `powered_gap`, `exponential_bound`, `CollatzLab.no_rational_seed_realizes_family` | [`Family.lean`](../CollatzLab/Family.lean) |
| Corollary 9.1 and integer specializations | `CollatzLab.no_rational_seed_realizes_shifted_family`, `CollatzLab.no_eventually_shifted_family_itinerary`, `CollatzLab.no_int_seed_realizes_shifted_family` | [`Family.lean`](../CollatzLab/Family.lean) |

## Intermediate theorem signatures

These are the complete declaration headers, with proof bodies omitted.
The names and definitions are in `CollatzLab.Family`, with `CollatzLab` open.
`pre L a b n` is the exact finite sum
`sum_{j<n} w_L(j) a^j b^(n-1-j)`; `geom a b n` is the same sum with all symbols
`1`. Thus `C L a b = b^2 geom(a,b,L-2) + a^(L-1)` is exactly the paper's
`C_h(a,b)`. The length-`L` block offset at symbol `1` simplifies to
`c1=B-2^(L-1)`; at symbol `0` it is `c0`.

```lean
theorem numIter_block {L : Nat} (hL : 3 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (m : Nat) :
    A L * numIter q p (L * (m + 1)) = B L * numIter q p (L * m) +
      (c0 L - (2 : Int) ^ (L - 2) * familyWord L m) * q

theorem initial_divisibility {L : Nat} (hL : 3 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (m : Nat) :
    (2 : Int) ^ (L - 2) ∣
      (B L - A L) * numIter q p (L * m) + c0 L * q

theorem initial_normalization {L : Nat} (hL : 4 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) :
    (2 : Int) ^ (L - 2) * u L p q 0 =
      B L * ((B L - A L) * p + c0 L * q)

theorem prefix_mahler (L : Nat) (hL : 3 <= L) (a b : Int) : ∀ n,
    (b ^ L - a ^ L) * pre L a b (L * n) =
      C L a b * (b ^ (L * n) - a ^ (L * n)) +
      a ^ (L - 2) * (b - a) * (b ^ L - a ^ L) *
        pre L (a ^ L) (b ^ L) n

theorem denominator_props {L : Nat} (hL : 4 <= L) {q : Int}
    (hq : 0 < q) (ho : q % 2 = 1) :
    ∀ k, 0 < D L q k ∧ D L q k % 2 = 1

theorem tower_congruence {L : Nat} (hL : 4 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) : ∀ k n, 1 <= n ->
    a L k ^ n ∣ b L k ^ (n - 1) * u L p q k -
      D L q k * pre L (a L k) (b L k) n

theorem tower_exact {L : Nat} (hL : 4 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    a L k ^ (L - 2) ∣ delta L (a L k) (b L k) (u L p q k) (D L q k) ∧
    a L k ^ (L - 2) * u L p q (k + 1) =
      b L k ^ (L - 1) * delta L (a L k) (b L k) (u L p q k) (D L q k)

theorem approximant_identity (L : Nat) (hL : 3 <= L) (a b : Int) :
    b ^ (N L) * P L a b - (b ^ L - a ^ L) * pre L a b (N L + 1) =
      a ^ (N L) * (b ^ L + a * (a * geom a b (L - 1) - a ^ (L - 1)))

theorem valuation {L : Nat} (hL : 4 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    let m := N L * L ^ (k + 1)
    E L p q k ≠ 0 ∧ (2 : Int) ^ m ∣ E L p q k ∧
      ¬ (2 : Int) ^ (m + 1) ∣ E L p q k ∧
      (2 : Int) ^ m <= absInt (E L p q k)

theorem height_step {L : Nat} (hL : 4 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    H L p q (k + 1) <= b L k ^ (heightExponent L) * H L p q k

theorem form_upper {L : Nat} (hL : 4 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    absInt (E L p q k) <
      3 * H L p q 0 * (3 : Int) ^ (formExponent L * L ^ k)

theorem exponent_gap (L : Nat) (hL : 4 <= L) :
    125 + 8 * formExponent L <= 5 * (L * N L)

theorem base_gap (L : Nat) (hL : 4 <= L) :
    (2 : Int) ^ 25 * (3 : Int) ^ (formExponent L) <=
      (2 : Int) ^ (L * N L)

theorem exponential_bound {L : Nat} (hL : 4 <= L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    (2 : Int) ^ (25 * L ^ k) < 3 * H L p q 0
```

Here `a_k=A^(L^k)`, `b_k=B^(L^k)`, `D_0=(B-A)q`,
`D_(k+1)=D_k(b_k-a_k)(b_k^L-a_k^L)`, `u_0=B*quotient(L,p,q,0)`,
`H_k=|u_k|+D_k`, `N=L*L-2`, `P=b^2 geom(a,b,L-1)`,
`E_k=D_k P(a_k,b_k)-u_k(b_k^L-a_k^L)`,
`heightExponent=2L-1`, and `formExponent=L^2+L-1`.
These are executable definitions; their claimed exact divisions are theorems.
The exact divisibility and nondivisibility in `valuation` are the requested
certificate for `v_2(E_k)=N L^(k+1)`, without introducing a separate valuation
convention at zero.

## Dependency and cancellation review

The main path is:

```text
block semantics -> odd-run and block arithmetic -> base_identity
prefix_block -> prefix_mahler -> congruence_step -> tower_congruence
periodic_prefix -> approximant_identity -> odd_multiple -> valuation
ab_bounds + tower_exact -> height_step -> form_upper
exponent_gap + valuation + form_upper -> exponential_bound -> contradiction
```

`initial_divisibility` follows from the common run of `L-2` odd steps.
`quotient_exact` and `initial_normalization` therefore prove the initial
normalization is exact in the ordinary integers, before it is used in a
congruence.

`delta_exact` uses the level-`k` congruence at length `L`, and the identity
`a^L=a^(L-2)*a^2`, to construct a divisor witness for `Delta_k`.
`congruence_step` uses the old congruence at **`M=L*(n+1)`**, not `L*n`.
The transport identity has scale `a^(L-2)*b`, while
`a^M=a^(L-2)*(a^L)^n*a^2`. It first cancels the positive factor
`a^(L-2)`, then cancels `b` by the independently constructed Bezout
certificate. A final prefix step and Bezout cancellation of `b^L` recover
length `n`. The remaining modulus is the whole `(a^L)^n`; there is no
power-of-two loss.

`approximant_identity` is unconditional in the integers `a,b`. It proves
the unit leading coefficient symbolically for arbitrary `L >= 3`, rather
than evaluating `L=4,5,...`. Oddness of `D_k,b_k` and evenness of `a_k`,
followed by Bezout cancellation, make `E_k` an odd multiple of `a_k^N`.

The height proof uses the same bound as the paper with a simpler intermediate
estimate. Put `F=b^(2L-1)`. The exact recurrence and `C_h<3b^(L-1)` give
`4|u_(k+1)| <= F(|u_k|+3D_k)` since `a^(L-2)>=4`.
Also `4D_(k+1)<=FD_k` since `b^(L-2)>=4`. Adding and using `|u_k|>=0`
gives `H_(k+1)<=FH_k`. This requires only inequalities already proved by
`ab_bounds`; it does not assume a sign for any `u_k`.

For the exponent gap, `4L<=L^2` and `4L^2<=L^3` imply
`125+8(L^2+L-1)<=5L(L^2-2)`. The comparison `3^5=243<256=2^8`
then bounds fifth powers. Monotonicity reflects that bound to the original
positive integer bases. No logarithms, floating point, or asymptotic
assumption are used. The final contradiction takes the finite index
`K=toNat(3H_0)` and combines `2^(25L^K)<3H_0=K` with
`K<L^K<=25L^K<2^(25L^K)`.

The tail corollaries reuse the existing `realizes_shiftWord_pred` and
`seedParity_add` with `Family.word_binary`. Their inverse maps and rational
semantics are exactly the same ones as for the original word.

## Reproduction and axiom audit

Run from the repository root, using the unchanged pinned toolchain:

```text
lake clean
lake build
lake env lean research/lean-audit/FamilyAudit.lean
lake env lean research/lean-audit/AuditChecks.lean
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
```

[`FamilyAudit.lean`](lean-audit/FamilyAudit.lean) contains the exact **44**
explicit `#print axioms` declarations used by
[the Lean CI job](../.github/workflows/ci.yml): the original 16, plus 28
family, semantic, and regression statements. CI requires exactly 44
well-formed audit lines, allowing only `propext`, `Classical.choice`, and
`Quot.sound`, or no axioms. It rejects all other output and dependency names.
The source gate also rejects `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
`native_decide`, `implemented_by`, and `extern` in the library.

Headline output:

```text
'CollatzLab.no_rational_seed_realizes_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.no_rational_seed_realizes_shifted_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.no_eventually_shifted_family_itinerary' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.familyWord_five_prefix' does not depend on any axioms
'CollatzLab.family_five_positive_prefix_witness' does not depend on any axioms
```

All other audited declarations use subsets of those three standard
foundation axioms. The `family_ring` macro only expands integer
identities with `simp` and discharges the remaining linear consequences
with `omega`; it does not install a new trusted decision procedure.
There are no added packages; only the pinned Lean distribution is needed.

Local verification on 2026-11-14: Lean 4.18.0 (`11ccbced7964`),
Rust 1.100.0, Cargo 1.100.0. The clean library build, the complete 44-line
CI audit, the earlier external semantic audit, formatting, Clippy with
warnings denied, and all **90 Rust tests** passed. The Rust suite includes
artifact reproduction checks. An independent second-kernel replay was
not performed; `lake build` checks all new proof terms with the pinned
Lean kernel.

## Scope and remaining obligations

**The required uniform irrationality theorem and Corollary 9.1 are complete;
there are no remaining proof obligations for them.** The `L=4` names and
statements remain exported. No mathematical gap in the candidate argument
was needed as an extra assumption.

The general equal-weight morphism criterion (Theorem 8.1) remains a written
proof and is outside this implementation. The family's general symbolic
survival and aperiodicity proofs (Theorems 2.2 and 2.3) are also still written
proofs; their `L=4` counterparts retain the earlier kernel formalization.
The formal-series and 2-adic analytic identities are represented by the
finite integer consequences required for the irrationality contradiction,
not by standalone analytic theorems.

This result concerns this explicit family and its finite shifts and eventual
tails. It does not prove the Collatz conjecture, CST, or the general open
Periodicity Conjecture, and makes no originality claim.
