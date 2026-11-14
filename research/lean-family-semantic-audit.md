# Independent semantic audit of the family theorem (Phase 7 A)

Audited base: `d0ced40fd35af9b94fa6373c9f5e913a58018cc7`, Lean 4.18.0,
2026-11-14 UTC. This is a fresh dependency and semantics review of the actual
sources, plus independent executable checks. It is not a second proof-assistant
implementation or an independent implementation of the Lean kernel.

**Finding:** no critical semantic or mathematical defect found. The formal
theorem excludes rational seeds for the intended family uniformly for every
`L >= 4`. It does not exclude arbitrary automatic words or prove Collatz.

## Statement and rational interpretation

The public statements are literally:

```lean
CollatzLab.no_rational_seed_realizes_family
  (L : Nat) (hL : 4 ≤ L) (p q : Int) :
  ¬ CollatzLab.RealizesWord p q (CollatzLab.familyWord L)

CollatzLab.no_rational_seed_realizes_shifted_family
  (L : Nat) (hL : 4 ≤ L) :
  ∀ (t : Nat) (p q : Int),
    ¬ CollatzLab.RealizesWord p q
      (CollatzLab.shiftWord (CollatzLab.familyWord L) t)
```

`RealizesWord p q v` is `q > 0 ∧ q % 2 = 1 ∧ ∀ j, seedParity q p j = v j`.
`seedParity q p j = numIter q p j % 2` and `numIter` iterates
`numStep q p = if p % 2 = 0 then p / 2 else (3*p+q)/2`.
For odd `q`, numerator parity is parity of `p/q` in the 2-adic integers.
`numStep_eq` proves exact division on each branch, including negative
numerators. `numIter_equiv` proves invariance under equivalent odd-denominator
representations. No reducedness, sign or height constraint is imposed on `p`.
Any rational in the 2-adic integers has a representation with positive odd
denominator, so this is the claimed rational domain.

`L,p,q` are free parameters; the proof uses no finite bound on them.
`numIter_one` connects denominator 1 to actual integer Collatz iteration.
The eventual-tail theorem follows from `seedParity_add` and the same rational
inverse branches. Odd branches may multiply the denominator by 3; positivity
and oddness are proved, so the rational domain remains closed.

## Word model and independent checks

`familyWord L n = familyAux L n n` depends only on `L,n`, never on a seed.
Fuel stability and strict decrease of `n/L` establish the full block recurrence.
For `r<L`, it says the image at symbol `b` is `1` for `r<L-2`, then `b`, then
`1-b`. These are exactly `1^(L-1)0` and `1^(L-2)01`.
The index-zero case gives 1, and the uniqueness argument handles index zero
without a circular recursive call. `familyWord_four` uses uniqueness to compare
the separately defined original word. Binary range holds without a seed premise.

New checks in `CollatzLab/FamilySemanticChecks.lean` build **literal lists** by
concatenation and substitution, independently of the base-`L` recurrence:

- `Phase7Audit.literal_four`, `literal_five`, `literal_six` compare the first
  `L^2` symbols against two literal substitution iterations.
- `positive_prefix_witnesses` uses integer numerators 25319, 25850607,
  3551146143 for lengths 16,25,36. These were found by bitwise residue lifting
  using direct Collatz iteration, without the Mahler formula.
- `signed_prefix_witnesses` checks numerators -201085, -38519125,
  -325841652965 with denominator 5, and -977524958895 with denominator 15.
  The last is an unreduced equivalent fraction. Every comparison uses actual
  `seedParity` and the independent literal list, by kernel reduction.
- `signed_branch_checks` checks both signed parity branches explicitly.
- `negative_realization` proves the infinite all-one word is realized by
  `(-5)/5`, by induction. Together with the old all-zero realization this
  rules out an accidentally unsatisfiable infinite parity predicate.
- `disagreement_controls` checks indices 14,23,34 and the corresponding
  distinct periodic-control symbols.

These finite witnesses do not realize the infinite family word. The family
theorem is a separate infinite statement; finite realizations are consistent
with it.

## Exact arithmetic review

The dependency chain was traced in both directions:

```text
actual Collatz branches -> odd_run -> numIter_block
 -> initial_divisibility -> quotient_exact -> quotient_step -> base_identity
word_block -> prefix_block -> prefix_mahler
base_identity + prefix_mahler -> congruence_step -> tower_congruence
periodic_prefix + first_difference -> approximant_identity
tower_congruence + odd D,b + even a + Bezout -> odd_multiple -> valuation
tower_exact + base ratio -> height_step -> form_upper
valuation + form_upper + base_gap -> exponential_bound -> contradiction
```

In `FamilyTower`, exact cancellation is proved before division is used:
the congruence at length `L` supplies an explicit witness for
`a^(L-2) ∣ delta`. No Euclidean quotient is silently assumed exact.
Transport takes the old congruence at `M=L*(n+1)` and uses
`a^M=a^(L-2)*(a^L)^n*a^2`. After cancellation it still has the full target
modulus `(a^L)^n`. Cancellation of `b` and `b^L` uses explicit Bezout
identities, not division in a non-field. The denominator is positive odd
because `b>a>0`, `b-a` and `b^L-a^L` are odd at every level.

`N=L^2-2=L*(L-1)+(L-2)` is the zero-based first differing index, not a length
including that symbol. All earlier symbols are periodic; the changed symbol
is zero where the periodic symbol is one. `approximant_identity` gives an
integer residual after extracting `a^N` whose constant term is `b^L`.
The all-prefix congruence at `N+1` makes the linear form an odd multiple of
`a^N`; therefore it is nonzero. With `a=2^(L*L^k)` this is exactly
`v2(E_k)=N*L^(k+1)`. `valuation` states divisibility, next-power nondivisibility,
nonvanishing and the ordinary absolute-value lower bound, avoiding any
convention for valuation of zero.

The height proof handles both signs of `u_k` using `absInt`. Its auxiliary
lemma is conditional only on the already established exact recurrence.
`a/b <=16/27` is proved for every `L>=4`, and persists under taking powers.
This bounds geometric sums uniformly; the height step and closed bound have
no hidden constant depending on `k` or a finite table of `L`.
The all-`L` exponent gap follows from `4L<=L^2`, `4L^2<=L^3`, and the integer
comparison `3^5<2^8`. The contradiction chooses the **finite** natural index
`K=toNat(3H_0)`: positivity gives `(K:Int)=3H_0`, while the proved bounds
give both `2^(25L^K)<K` and `K<2^(25L^K)`. No convergence or analytic axiom
is hidden in the proof.

## Trust, validation and documentation defects

`lake build` and the expanded `FamilyAudit.lean` succeed. Its 52 declarations
use only subsets of `propext`, `Classical.choice`, `Quot.sound`, or no axioms.
The seven new finite checks use no axioms; `negative_realization` uses
`propext`. The original 44 audit results are unchanged. The proof-escape scan
finds none of the forbidden tokens in the library. The full Rust formatting,
Clippy and test commands succeed (see the campaign checkpoint for counts).

Minor documentation defect repaired: the README's unqualified sentence that
the Lean project was not compiled was left over from a literature review.
It now explicitly refers to the external project at that earlier investigation.
Phase 6 audit counts are marked historical where necessary; CI now checks 52.

Unformalized claims remain clearly separated: general-family symbolic survival
and aperiodicity, standalone formal series and 2-adic analytic identities,
and generic Theorem 8.1. Aperiodicity alone would not prove rational-seed
irrationality. No independent kernel replay, transcendence result, CST result,
or general Periodicity Conjecture result is claimed.
