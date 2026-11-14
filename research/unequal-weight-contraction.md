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

The concrete `100/110` proof, exact finite-language certificates, signed prefix
checks, and focused primary-literature comparisons are the next checkpoints.
