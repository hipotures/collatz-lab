# Phase 12: prior-art coverage and two-return limitations

Issue: <https://github.com/hipotures/collatz-lab/issues/24>.
This is AI-assisted mathematical research, not human peer review.

## Verdict and evidence levels

**No new rational exclusion found.** The literal length-six candidate is
already covered by earlier **density-sensitive** shadow and complexity
criteria. Its failure of the Phase 11 weight-only return ledger and contraction
criterion does not place it beyond the checked prior art.

The proposed seed-eliminating determinant has a stronger limitation: its
congruence is true for **every binary word with the two finite matches**.
Consequently a genuinely nonzero determinant smaller than the proposed
modulus is impossible even without assuming infinite rational realization.
This precise no-go statement is kernel checked in `TwoReturn.lean`.

| Headline | Classification | Evidence |
|---|---|---|
| Candidate irrationality | **Follows from earlier preprints**, not a new exclusion | Independent written reductions in §3; Allikvere 2026 and De Jesús 2026 |
| Literal word, aperiodicity, counts, discrepancy, all-shift contraction obstruction | **Independent new repository formalization** of elementary structure; mathematical priority unverified | Kernel theorems in `FrontierSix.lean` |
| Two-return congruence | **Known elementary consequence** of finite parity compatibility / isometry | Kernel proof, plus separate reconstruction in §4 |
| Small determinant forces zero, without rationality | **Independent new repository formalization of a rigorous no-go**; no first-discovery claim | `returnDet_small_iff_zero` |
| Global return cap, absence of initial squares | **Kernel-checked structural result**, mathematical priority unverified | `frontierSix_return_bound`, `frontierSix_no_square_prefix` |
| Exact global languages at specified finite lengths | **Finite exact certificates plus written coverage proof** | Independent Python closure and occurrence witnesses; not a new Lean language theorem |
| Candidate transcendence, optimal approximation exponent | **Unresolved in this development** | Stronger external claims are separately recorded, not kernel conclusions |

Here **K** means the exact Lean proposition was kernel checked; **H** means a
written mathematical deduction; **F** means reproducible finite arithmetic;
**S** means the identified primary source portions were read. H is not K,
and F never substitutes for a universally quantified proof. Exact sources,
versions, sign domains and proof-access limits are in the
[coverage matrix](phase12-prior-art-matrix.md).

## 1. Literal candidate and structural hypotheses

Put `mu(1)=100111`, `mu(0)=111110`, and select the fixed word starting at one.
The six columns, including index zero, are

```text
w(6n) = w(6n+3) = w(6n+4) = 1,
w(6n+1) = w(6n+2) = 1-w(n),
w(6n+5) = w(n).
```

These are **K**, derived from literal images and the existing indexed-word
recursion. Prolongability and both letters (indices zero and one) are checked.
`FrontierSixChecks.literal_semantics` compares three independent list
substitutions with the indexed word (lengths 6, 36 and 216). Actual positive,
negative and unreduced 81-step witnesses are also K, separately from any
infinite exclusion. The Python checker independently verifies signed odd
denominators and normalization. `RealizesWord`, `numStep`, `numIter` and
`seedParity` are unchanged.

The column incidence matrix, with rows/columns ordered zero, one, is
`[[1,2],[5,4]]`; it is strictly positive and has characteristic polynomial
`(X-6)(X+1)`. Thus `(r1,r0,D,Delta)=(4,5,7,-1)`. Exact aligned power counts
are **K**:

```text
7 W(6^k*a,6^k) = 5*6^k + (-1)^k*(7*w(a)-5).
```

For `W(n)=W(0,n)`, appending the first t bits of the next image gives
`W(6n+t)=5n-W(n)+H_(w(n))(t)`. For `0<=t<6`, the six possible local errors
`7H_b(t)-5t` are `(0,2,4,6,8,10)` for b=0 and
`(0,2,-3,-8,-6,-4)` for b=1. Hence **K**, for every `n<6^k`,

```text
-10k <= 7W(n)-5n <= 10k.
```

The ordinary frequency is therefore 5/7 (**H** deduction, no Lean real-limit
export). Uniform frequency also follows **H**: every complete length-S power
image, S=6^k, has absolute integer balance at most 5. Partition any length-h
window into those images and two boundary pieces of total length below 2S.
Each boundary symbol has balance magnitude at most 5, giving
`|7W(a,h)-5h| <= 5h/S+10S`, uniformly in a. Choose S first, then let h grow.
This verifies Allikvere's uniform-upper-density premise, not merely an average
along aligned prefixes.

**Independent aperiodicity proof (H and K).** For an eventual period p>0
after start s, write p=6d+r. If r=0, compare identity columns at 6n+5 to get
the smaller positive period d. For r=1,4, use the zero at `6*(6s)+2`;
for r=2,3,5 use the zero at `6*(6s)+1`. Its shifted column is respectively
3,0,3,4,0, all forced ones. These indices lie beyond s. Strong descent
excludes every nonzero period residue and every positive period. No rational
seed, frequency theorem or empirical prefix is assumed.

**K contraction obstruction.** Specialize the full existing
`uniform_contraction_iff_subcritical`, with D=7 and `3^5=243>128=2^7`.
It rules out every positive fixed chunk size after every finite shift. This
is a limitation of uniform contraction, not an irrationality proof.

## 2. Global returns and the failed weight-only ledger

For m>0 let R(m) be the exact length of the common prefix at positions 0,m.
The six columns give a complete recursive calculation (**H**):

```text
R(6n)   = 6 R(n)+1                  (n>0)
R(6n+1) = R(6n+2) = 1-w(n)
R(6n+3) = 1
R(6n+4) = 2-w(n)
R(6n+5) = w(n).
```

For the aligned case, equal parents have equal six-bit images; the first
unequal parents have images agreeing exactly at their first column. The
other five cases follow by inspecting at most three columns. Descent ends
because m/6<m. This is a global return computation, not a search cutoff.
In particular `m=3*6^k` has `R(m)=(6^(k+1)-1)/5`.

The stronger universally quantified bound is **K**: for any m>=1 and any
actual match length ell, `5ell+1<=2m`. For a multiple of six, a length-ell
match forces a parent match of length `floor((ell+4)/6)` through complement
column one. The induction bound at the parent gives the displayed inequality.
Nonzero residues have at most two matching symbols; the small m cases are
checked separately. In particular **there are no initial square prefixes at
any positive half-length**. Starting with 10 alone would not prove that.

This rigorously explains the unsuccessful Phase 11 sharp **weight-only**
ledger. Its gain is `G(m)=ell-W(m)*log2(3/2)`. As m grows, the return bound and
frequency give

```text
limsup G(m)/m <= 2/5 - (5/7)*log2(3/2) < 0.
```

The last strict sign is exactly `3^25>2^39`, with no numerical threshold
decision. Therefore the gain tends to minus infinity uniformly over available
initial return lengths; its supremum is finite. This is **H** from the K
integer estimates, not a formal Lean logarithm theorem. It rules out unbounded
certificates from that particular height cap. It does not rule out the sharper
density-sensitive height estimate in §3 or periodic shadows with a preperiod.

**F reproduction.** On exactly 60,000 symbols, the scan over 1<=m<7500 finds
5,356 positive returns, largest match 1,555. The maximum scanned exact ratio
`2^(ell+W(m))/3^W(m)` is 4/3 at m=3. This is not asserted as the global maximum.
Every scanned match ends at an observed mismatch, so none was truncated.

## 3. Exact reduction to earlier criteria

### Density-sensitive shadows already suffice

Let `rho=(5/7)*log2(3)>1`. For a prefix U of length m, every term of its
offset is `2^d*3^(W(m)-W(d+1))`. The all-prefix discrepancy bound in §1
implies, uniformly for d<m, that its binary logarithm is at most

```text
d + (5/7)*(m-d)*log2(3) + O(log m) <= rho*m + O(log m).
```

There are at most m terms. Thus both the offset and the closing coefficient
`2^m-3^W(m)` have magnitude at most `2^(rho*m+O(log m))`. For a hypothetical
signed rational p/q, q>0 odd, their closing form E has that same exponential
rate, with an additional constant depending on `|p|+q`. Independent
aperiodicity makes E nonzero; an actual return forces `2^(m+ell)|E`.
At m=3*6^k, `ell=(6^(k+1)-1)/5`, so `(m+ell)/m -> 7/5`.
But `rho<5/4<7/5`: the first strict inequality follows from `3^20<2^35`.
The resulting height/divisibility inequalities contradict each other.

This is an **H proof of a known implication**, namely the elementary rational
subcase of Allikvere's density-sensitive height/shadow framework (§4 Lemma 4.1
and Theorem 4.2, and §5 Theorem 5.3), or Cassidy's Theorem R with these actual
shadow heights. It needs no unchecked transcendence theorem and does not
identify real and 2-adic infinite limits. It shows why the weak ledger's
failure in §2 cannot establish a known-method gap.

### Global complexity supplies another known reduction

For S=6^k, a length-S factor is determined by its starting residue modulo S
and the two parent letters of the power images it intersects. There are S
residues and at most four binary pairs. Therefore **H**
`P(6^k)<=4*6^k` for every k, giving `liminf P(n)/n<=4`.
Together with uniform density and `rho<5/4`, this meets Allikvere's §5
Corollary 5.7 premise `liminf P(n)/n<1/(rho-1)`.

A further original found during this pass states this implication directly:
De Jesús, *A drift-sensitive complexity bound for rational points of the
3x+1 conjugacy map*, revision 1, 30 September 2026,
[Zenodo 23071770](https://doi.org/10.5281/zenodo.23071770), Lemmas 7–8,
Theorem 9 and Corollary 15. Its statement and elementary relevant proofs were
read. For existing frequency d, its drift is `max(0,d*log2(3)-1)`; a signed
nonperiodic rational realization requires
`liminf P(n)/n >= 1/(d*log2(3)-1)` in the supercritical case. Hence it excludes
this candidate as well. This is an earlier **preprint theorem**, not a new
quantitative obstruction discovered here. Pham's earlier pressure theorem
also anticipates the mechanism; its printed asymptotic corollary uses limsup.

For a separate direct audit with exact integer constants, use 36-step power
images: their weights are 25 and 26. Put A=2^36, B=3^26, C=3^36-A, R=B/A>1.
The actual signed affine recurrence and the universal offset cap imply

```text
A*|y_(36(n+1))| <= B*|y_(36n)| + C*q.
```

For `z_n=|y_(36n)|+Cq`, one gets `A*z_(n+1)<=B*z_n`, since B>=A+1.
Between boundaries, `|y_(j+1)|+q <= (3/2)(|y_j|+q)`. Consequently
`|y_j| <= H*R^(j/36)` for fixed `H=(3/2)^35*(|p|+Cq)`.
Among 4S+1 length-S factors starting at 0 through 4S two agree. Their states
are distinct by non-eventual-periodicity, so their difference is a nonzero
multiple of 2^S and

```text
2^S <= 2H*R^(S/9),
2^(45S) <= (2H)^9 * 3^(26S).
```

This contradicts unbounded S because
`2^45=35184372088832>2541865828329=3^26`. This independent **H** reconstruction
checks the density-aware collision mechanism without relying on the source's
analytic extensions. It covers both numerator signs and unreduced odd
denominators. Finite shifts and eventual tails follow by rational closure
under the existing inverse/forward branches. These exclusions are **not new
Lean exports in this phase**.

### Finite languages: exact at these lengths, not an asymptotic inference

| Length | Observed in the 60,000 prefix | Exact global closure count |
|---|---:|---:|
| 2 | 4 | 4 |
| 6 | 17 | 17 |
| 36 | 118 | 118 |
| 216 | 724 | 724 |
| 864 | 2,676 | 2,676 |

Start from the actual initial length-n factor and close under every child
offset r=0,...,5. A positive starting position a descends to floor(a/6)<a,
and its factor is one of those children, proving coverage by strong induction.
Conversely a row occurring at a has each child at 6a+r, proving occurrence
of every generated row. The checker retains and independently checks these
occurrence witnesses with the indexed recursion. This proves exactness of
the finite global-language certificates, without assuming prefix saturation.
Their deterministic hashes are in `phase12/evidence.json`.
Only the separate general bound on P(6^k) above supplies the asymptotic premise.

## 4. Two-return determinant: a universal compatibility no-go

For arbitrary Boolean v put `a_m=2^m-3^weight(v,m)`, `c_m=offset(v,m)` and
`D_(m,n)=a_m*c_n-a_n*c_m`. Positive m makes a_m odd (**K**).
The exact identity is

```text
a_n*E_m-a_m*E_n = D_(m,n)*q,   E_m=a_m*p-c_m*q.
```

This checks the sign before any divisibility test. The existing actual-return
theorem gives `2^(m+ell)|E_m`, `2^(n+f)|E_n`. Put K=min(m+ell,n+f).
Subtract, then cancel odd q using a power-of-two Bezout identity. The resulting
necessary congruence is **K**, `two_return_divisibility`.

But an infinite rational seed was unnecessary. Set N=max(m+ell,n+f) and
truncate v after its first N symbols, then append zeros. Repeated rational
inverse branches construct a positive odd denominator and an actual rational
seed for this eventually-zero word (**K**, `finiteWord_realized`). It has the
same two matches and the same two offsets/counts. Applying the congruence to
it proves `returnDet_automatic` for v itself, with **no rationality premise**.
The finite witness depends on N and is never claimed to realize the infinite v.

An independent reconstruction uses periodic shadows: `c_m/a_m` and `c_n/a_n`
have parity agreeing with v through their respective return precisions.
The classical parity isometry makes their difference divisible by 2^K in
the 2-adic sense. Their denominators are odd, so the numerator determinant
is divisible by 2^K. This also explains the result without seed elimination.

Any integer divisible by 2^K is either zero or has magnitude at least 2^K.
Thus the precise strongest exported no-go is **K**:

```lean
-- assuming only the two finite prefix matches:
absInt (returnDet v m n) < (2 : Int)^min (m+ell) (n+f)
  ↔ returnDet v m n = 0
```

It includes m or n zero, empty matches, equal return positions, overlaps
ell>m, equal precisions and zero determinants. Positive return positions are
needed only for the separate odd-coefficient lemma. Zero determinant does
not make an arbitrary infinite word periodic: an initial run of ones has
zero determinants before an arbitrary later nonperiodic continuation.

The proposed nonzero/small-determinant rational exclusion is therefore
vacuous for genuine matches, rather than a stronger irrationality criterion.
This does **not** rule out methods that retain a fixed denominator, seed
height, positivity, or a quantitative lattice approximation constraint across
infinitely many scales. Those extra premises are exactly what simple
elimination discarded. Nor does it rule out every multi-return argument.

**F adversarial evidence:** all 1,023 binary words of lengths 0 through 9,
574,327 pairs of all admissible finite matches, including 46,390 overlapping
pairs; 149,500 nonzero and 424,827 zero determinants. All congruences and
magnitude dichotomies pass. An unjustified extra precision bit fails in
85,484 cases. There are also 1,016 signed finite realizations and 7,168
closing-form checks, independent affine sums/iteration, and exact elimination
identity checks. A fabricated match on 10 yields determinant -2, failing the
claimed modulus 4. Dropping oddness from the forms-cancellation lemma fails
at p=0,q=4,K=2, with closing forms -4,-4 and determinant -2.

The mandatory controls remain: 101/010 has the alternating itinerary at 1/1;
the all-one itinerary is realized by -1/1. Their signed equivalents and odd
unreduced scalings are checked. Repeated-period returns have zero determinant;
no spurious exclusion is drawn from them.

## 5. Two routes tested, remaining question and handoff

**Route B: eliminate the seed using two returns.** The arithmetic is correct,
but generic finite compatibility already forces its conclusion. Proved the
no-go above instead of manufacturing a nonzero/small example. Valuation
improvements based only on actual word matches still need an additional
fixed-seed or height premise to address rationality.

**Route C: exact overlap/return structure and factor-language closure.** The
return recursion proves the limitation of the original weight-only ledger
globally; the separate closure computation verifies the reported complexity
counts exactly. Both temptations were actively falsified: finite lower counts
do not defeat a global upper-bound criterion, and a weak height cap does not
defeat a sharper known shadow theorem. Density-sensitive methods already
exclude the candidate, so no further qualitative exclusion implementation
was commissioned.

A precise next structural question, currently **unresolved here**, is to
determine the optimal asymptotic growth of

```text
H_N = min { max(|p|,q) : q>0 odd, gcd(p,q)=1,
                        seedParity(q,p,j)=w(j) for every j<N }.
```

The set is nonempty by finite compatibility. Does
`log2(H_N)/N` have a limit for this candidate, and what is its liminf?
This asks for a sharp rational approximation invariant of an already excluded
seed, not another qualitative irrationality proof. No novelty is claimed for
this question. Before an implementation, compare the exact scope of
Molchanov-type measures and the multi-approximant sources in the coverage
matrix. The present no-go does not answer it. No replacement morphism is
advertised as unaddressed without comparable triage.

The new trusted surface is 29 explicitly audited public definitions/theorems
in `TwoReturn.lean`, `FrontierSix.lean` and `FrontierSixChecks.lean`; CI's
exact count is 593. All 564 baseline audit names remain in their original
order. Standard foundations remain the only permitted assumptions. No proof
escapes or new dependencies are introduced. `phase12/Signatures.lean` checks
the key quantifiers separately. The exact executed validation record, pushed
SHAs, CI and next review task are maintained in
[the progress journal](phase12-progress.md).

No general Collatz/Periodicity theorem, all-automatic or all-morphic exclusion,
new transcendence result, publication readiness, merge permission or author
identity decision is inferred from this work.
