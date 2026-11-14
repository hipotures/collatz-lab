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

## Kernel-checked finite-language interface

`WindowCertificate.lean` implements the stretch certificate. A certificate is
a finite list of source windows, containing the actual initial window and
closed under the `L` child-window offsets of substitution. For a source window
at any positive index `a`, its parent starts at `a/L<a`. Strong induction,
the literal fixed-point recurrence, and a verified parent-index bound prove
that every infinite-word window is in the finite language. No primitivity,
recurrence, or finite-prefix saturation assumption is needed for coverage.

The finite fields are checked with ordinary Lean `decide`, with every proof
term checked by the kernel. `window_certificate_weight_bound` links the finite
row weights to every infinite source window. `no_rational_seed_window_certificate`
combines that bound with the generic contraction criterion and an independently
supplied aperiodicity theorem. A second bridge transports finite expanded-offset
bounds to all infinite source-aligned chunks.

For `100/110`, the exact language and nine-step expansions give:

| Source window | Expanded odd count | Expanded offset |
|---|---:|---:|
| 001 | 5 | 319 |
| 010 | 5 | 527 |
| 011 | 4 | 133 |
| 100 | 5 | 761 |
| 101 | 4 | 211 |
| 110 | 4 | 419 |

`UnequalCertificates.lean` kernel-checks closure and occurrence of every row
in a bounded prefix. Therefore this is the exact length-three language.
`unequal100110_nine_offset_sharp` proves the infinite cap 761, attained at
index zero. `no_rational_seed_unequal_100_110_via_certificate` independently
applies the finite-language interface. An actual aligned two-source window
starting at index ten is `00`, with image weight four and `3^4>2^6`; thus the
shorter two-source uniform criterion fails.

## Second kernel-proved example: `1 -> 110`, `0 -> 100`

`Unequal110100.lean` proves literal weights two and one, distinctness and
prolongability. Its indexed recurrences have the same forced endpoint columns
and the identity middle column: `w(3*n+1)=w(n)`. The generic
`ternary_columns_not_eventually_periodic` theorem in `ColumnAperiodic.lean`
proves non-eventual-periodicity whenever the middle-column map is injective.
It uses the same explicit period reduction, with no rationality premise.

The exact six-window language above has selected image weights at most five.
The one image is locally expanding (`9>8`), but all nine-step chunks contract
(`243<512`) and have offset at most 761. All these facts and the true affine
recurrence are kernel-checked. `no_rational_seed_realizes_unequal_110_100`
proves universal rational exclusion, with all finite shifts, eventual shifted
tails, and integer forward-orbit corollaries. An actual positive integer
`1357326276294383431942267` has its first 81 parity bits, ending at
`20475100934524160408`, as kernel-checked independently of the exclusion.

## Bounded exhaustive finite exploration

`phase10/search_unequal.py --check` reproduces `phase10/search-summary.json`.
It tests every binary length-2..6 image pair prolongable at one with unequal
weights: **2092 pairs**, **16736 languages** at `h=1..8`. There are at most
256 rows in any language. Each language is the least closure of the initial
window under child offsets. Every added row has an actual occurrence by
substitution; the generic strong-induction proof explains coverage. Exact
integer products determine contraction; no floating-point threshold or seed
interval is used.

| Length | Unequal pairs | Some h<=8 contracts | Includes locally expanding image | No h<=8 certificate |
|---|---:|---:|---:|---:|
| 2 | 5 | 1 | 0 | 4 |
| 3 | 22 | 12 | 11 | 10 |
| 4 | 93 | 46 | 24 | 47 |
| 5 | 386 | 181 | 0 | 205 |
| 6 | 1586 | 1044 | 653 | 542 |
| Total | 2092 | 1284 | 688 | 808 |

Only the two explicitly named examples are claimed kernel-proved exclusions
at this checkpoint. All other counts are deterministic finite analysis, without
an aperiodicity conclusion. In particular the rational `101/010` control has
an exact contracting two-source certificate (`3^3<2^6`) and remains periodic.
This confirms why contraction alone only proves periodicity.

Selected further data: `1000/1110` first contracts at `h=4`, with `R=10`
and `3^10=59049<65536=2^16`; `1100/1110` has the same first bound.
Neither is yet claimed as an exclusion. `10000/11110` has no certificate in
the prescribed `h<=8` range, despite its candidate limiting one-frequency
one-half. This distinguishes a search cutoff from failure of every possible
uniform-block argument. Contraction need not be monotone in h:
`1000/1110` passes at h=4 and h=8, but fails the all-window maxima at h=5,6,7.

## Signed denominator normalization

The original predicate still requires a positive odd denominator. The new
`SignedContraction.lean` uses the unchanged `numIter_equiv` to prove
`seedParity (-q) (-p) n = seedParity q p n` for every odd signed `q` and every
index. `positive_odd_denominator_normalization` explicitly constructs the
equivalent positive odd representation and cross-product equality. The two
examples therefore also exclude raw eventual shifted-tail parity agreement
for either sign of an odd denominator. Zero/even denominators are outside the
existing rational 2-adic model, and no claim is made for them.

Uniform frequency bounds and a focused primary-literature comparison remain
the next research checkpoint.
