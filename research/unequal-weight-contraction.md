# Uniform contraction for unequal-weight substitutions

This is the independent code/research track for [issue #16](https://github.com/hipotures/collatz-lab/issues/16).
It starts from `d2a71facd7135118a562de8a7903b8827934c3ac` and does not modify
or depend on the Phase 9 manuscript. No originality claim is made.

## Generic integer criterion

Let `A`, `Bmax`, `C` be integers, with `Bmax < A` and `C >= 0`. Suppose
`0 <= B(n) <= Bmax`, `-C <= d(n) <= C`, and

```text
A*y(n+1) = B(n)*y(n) + d(n).
```

Then every signed integer state satisfies `-K <= y(n) <= K`, where
`K = absInt(y(0)) + C`. Indeed, the integer gap `A-B(n)` is at least one,
so `(A-B(n))*K >= K >= C`. Multiplication of the induction bounds by the
nonnegative `B(n)`, followed by the recurrence, proves the next bounds after
cancellation of the positive `A`. No convergence theorem or fixed multiplier
is needed. The old constant-multiplier result is now a specialization.

For any Boolean parity word `v`, chunk length `k >= 1`, and actual realization
`RealizesWord p q (fun n => bit (v n))`, put

```text
y(n) = numIter q p (k*n)
r(n) = weight (fun j => v(k*n+j)) k
c(n) = offset (fun j => v(k*n+j)) k.
```

The unchanged `affine_prefix` theorem gives the exact integer recurrence
`2^k*y(n+1) = 3^r(n)*y(n) + c(n)*q`. For all Boolean words, induction gives
`0 <= c(n) <= 3^k-2^k`: the upper bound is attained by the all-one word.
Thus if `r(n) <= R` at every aligned chunk and `3^R < 2^k`, take
`Bmax = 3^R`, `C = (3^k-2^k)*q`. The positive odd `q` is supplied by
`RealizesWord`; the numerator may have either sign and no reduction is needed.
All block states are bounded. Two are equal by finite pigeonhole, and
determinism of the actual numerator dynamics forces an eventually periodic
full parity word. Independently proved non-eventual-periodicity therefore
excludes every rational seed with these semantics.

For a prolongable uniform binary morphism of length `L >= 2`, define
`imageWeightSum M a h` as the sum of the image weights selected by source
symbols `w(a),...,w(a+h-1)`. The kernel proves, for every `a,h`,

```text
weight (fun j => w(L*a+j)) (L*h) = imageWeightSum M a h.
```

Consequently an image-weight bound `<= R` on aligned source groups starting
at `h*n`, together with `3^R < 2^(L*h)` and independent aperiodicity, suffices.
There is no equal-weight premise. Stronger hypotheses on every source window
may be used to discharge the aligned-window requirement.

## Source and theorem map

| Mathematical statement | Lean declaration |
|---|---|
| Variable signed recurrence bound | `CollatzLab.variable_contracting_recurrence_bounded` in `VariableContraction.lean` |
| Preserved constant specialization | `CollatzLab.contracting_recurrence_bounded` in `Subcritical.lean` |
| All-word nonnegative offset cap | `Morphism.offset_bounds` in `MorphismContraction.lean` |
| Exact arbitrary-chunk recurrence | `Morphism.numIter_chunk` |
| Exact source-image weight link | `Morphism.weight_source_blocks` |
| Exact variable single-image recurrence | `Morphism.numIter_variable_block` |
| Exact multi-image recurrence | `Morphism.numIter_source_blocks` |
| Bounded states imply rational itinerary periodicity | `uniformly_contracting_blocks_periodic`, using existing `bounded_blocks_periodic` |
| Arbitrary-word exclusion | `no_rational_seed_uniform_block_contraction` |
| Morphism exclusion criterion | `Morphism.no_rational_seed_block_contraction` |
| Every finite shift | `no_rational_seed_shifts_of_exclusion`, using verified `realizes_shiftWord_pred` |
| Every eventual shifted tail | `no_eventually_shifted_itinerary_of_exclusion`, using verified `seedParity_add` |

Names in the table have prefix `CollatzLab.` when not explicitly shown.
The proof uses the existing `RealizesWord`, `numStep`, `numIter`, and
`seedParity` without modification. It does not use the universal equal-weight
exclusion theorem or a general Collatz periodicity conjecture.

## Scope and rational control

The fixed point for `1 -> 101`, `0 -> 010` is `(10)^infinity`, realized by
`p=q=1` (`Morphism.unequalAlternating_realized`). It is periodic, so it cannot
satisfy the aperiodicity premise of the new criterion. In particular no
blanket unequal-weight exclusion follows. Finite-prefix realization witnesses
are compatible with exclusion of an infinite itinerary.

## Concrete aperiodic example: `1 -> 100`, `0 -> 110`

The literal weights are respectively one and two. The zero image is locally
expanding: `3^2=9>8=2^3`. Thus a per-image maximum does not prove contraction.
The unchanged indexed fixed point agrees with literal list substitution and
satisfies, including at index zero,

```text
w(3*n) = 1,  w(3*n+1) = 1-w(n),  w(3*n+2) = 0.
```

For an eventual period `p>=1` with any starting index, residue `p mod 3=1`
compares a forced zero at `3*start+2` with a forced one. Residue two compares
a forced one at `3*start` with a forced zero. Residue zero compares middle
columns and cancels `1-x`, giving the smaller positive period `p/3` beyond
the same starting index. Strong induction excludes every eventual period.
This proof uses neither the equal-weight aperiodicity theorem nor a rational
realization assumption.

Every length-three source window contains a multiple of three and hence a
one. This proves absence of `000`, across boundaries as well as inside images.
The selected image weights in every three-source window sum to at most five.
The generic source-weight identity therefore bounds every aligned nine-step
chunk by five odd steps, and `243=3^5<2^9=512`. The exact actual recurrence is

```text
512*numIter q p (9*(n+1))
  = 3^(weight (fun j => w(9*n+j)) 9)*numIter q p (9*n)
    + offset (fun j => w(9*n+j)) 9*q.
```

The offset is in `[0,19171]`, since `3^9-2^9=19171`. Thus the signed integer
states at every block boundary are bounded by `absInt p + 19171*q` under
a hypothetical realization, contradicting the independent aperiodicity proof.

`Unequal100110.lean` exports:

```lean
theorem no_rational_seed_realizes_unequal_100_110 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.unequal100110)
```

There are no hidden seed hypotheses. The positive odd denominator is part of
the unchanged predicate. The same file proves every finite-shift exclusion,
every eventual shifted-tail itinerary exclusion, and the corresponding integer
seed and integer forward-orbit corollaries via verified inverse/forward branches.
All are explicitly listed in the exact axiom audit.

`UnequalContractionChecks.lean` compares four literal iterates (lengths
3,9,27,81) to the indexed word, and kernel-checks these 81-bit witnesses:

| Numerator | Denominator | State after 81 steps |
|---|---:|---|
| `2301021985950669302953629` | 1 | `34710635340769718209` |
| `-584148266392945232293615` | 5 | `-8811805182005340970` |
| `-1752444799178835696880845` | 15 | `-26435415546016022910` |

The last pair is unreduced. Their itinerary equivalence is also proved for
every index using `numIter_equiv`. These are finite realization witnesses;
none is asserted to realize the infinite word. Each numerator was obtained by
one modular inverse from the finite affine identity, without a seed search.

The independent Python verifier `phase10/verify_unequal.py --check` reproduces
`phase10/unequal-certificate.json`, with exact multiplier/offset rows for all
seven three-source words except `000`. It verifies literal substitutions,
boundary crossings, all signed 81-step affine recurrences, a negative-denominator
sign-normalization check, and the rational `101/010` control. The finite table
gives a sharper offset cap 761; the current infinite Lean proof only needs the
universal cap 19171. Finite checks and kernel proofs are kept distinct.

Focused primary-literature comparisons and further finite-language research
follow after the principal validation checkpoint.
