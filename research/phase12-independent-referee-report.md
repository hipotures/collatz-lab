# Independent Phase 12 mathematical referee report — issue #26

**Verdict: PASS for the exact Phase 12 mathematical statements and their
documented rational-irrationality reductions at the pinned head.** Both
priority results have independent proofs below. No blocking mathematical
error, hidden realization hypothesis, or proof bypass was found. This is a
fresh, adversarial, AI-assisted review, not human peer review.

**Integration recommendation:** PR #25 is suitable for owner consideration
as scoped formal research, with no required theorem repair. This is not an
authorization to merge. **Publication recommendation:** a new-irrationality
claim is unsupported; the exclusion follows from earlier preprints. A
formalization note would require a separate contribution assessment and human
review. The stronger external transcendence arguments are not certified here.

- Task: [issue #26](https://github.com/hipotures/collatz-lab/issues/26).
- Reviewed [PR #25](https://github.com/hipotures/collatz-lab/pull/25), branch
  `codex/phase12-novelty-frontier`, exact source
  [`37d94195119353799c69714a337c4ed2ac7c8752`](https://github.com/hipotures/collatz-lab/commit/37d94195119353799c69714a337c4ed2ac7c8752).
- Base and review-branch origin:
  [`47f34bdff38d876c394dc7326e457f686d112c13`](https://github.com/hipotures/collatz-lab/commit/47f34bdff38d876c394dc7326e457f686d112c13).
  Live remote refs and PR metadata agreed with the issue snapshot. PR #25
  remained open and unmerged throughout the review.
- Review date: 14 November 2026 UTC. Review branch:
  `review/phase12-independent-audit`; separate [review PR #27](https://github.com/hipotures/collatz-lab/pull/27),
  **open and unmerged**. The [resume journal](phase12-referee-progress.md)
  records pushed checkpoints and the separate review PR.
- The review clone and detached source worktree are separate from every
  preexisting checkout. No other agent was used. Only the three new review
  artifacts changed; implementation, existing reports, issues and manuscript
  were preserved.

Evidence labels: **H** independent written proof; **K** locally kernel-checked
exact proposition; **F** finite exact computation; **S** identified original
statement/proof portions actually read; **U** outside the verified scope.
K establishes the specified proposition; the semantic audit is additional.
F is never substituted for a universal proof.

## 1. Adversarial findings and scope restrictions

| Test or suspected failure | Result | Consequence |
|---|---|---|
| Does determinant divisibility secretly require one infinite rational seed? | No. Finite zero extensions supply actual signed rational witnesses, independently constructed below. | `returnDet_automatic` passes; the suggested nonzero/small-determinant exclusion premise is impossible for genuine matches. |
| Does the global return bound overlook overlaps, short returns or rounding? | No. Parent descent uses precisely `floor((ell+4)/6)`; equality occurs infinitely often. | `frontierSix_return_bound` passes and its constant cannot be increased. |
| Is one more determinant precision bit automatic? | False: `0010`, `(m,n,ell,f)=(1,3,1,1)`, has D=4 and K=2. | Minimal word length with two distinct positive nonempty returns; even the extra-bit strengthening fails. |
| Can one cancel an even denominator, or invent a return? | False in both cases; D=-2 is not divisible by 4. | The hypotheses of the forms and actual-match lemmas are substantive. |
| Do the two finite complexity counts establish an asymptotic premise? | No. A separate global two-parent-block argument does. | The PR uses that valid argument, rather than extrapolating 724/2676. |
| Does absence of fixed-chunk contraction or initial squares establish an exclusion-method gap? | No. Density-sensitive height/counting already exclude this word. | The PR correctly reports no new rational exclusion. |

Two nonblocking editorial clarifications would improve a future revision:
the auxiliary periodic-shadow explanation in findings §4 should explicitly
restrict `c_m/a_m` to m>0 (at m=0 it is 0/0); and De Jesús's internal draft
date, 30 September, should be distinguished from the Zenodo publication-date
field, 1 October 2026. Neither affects the finite-extension proof, attribution
priority, or any Lean statement. No implementation edit is requested here.

## 2. Actual rational Collatz semantics

The source is the shortcut map

\[
T(x)=x/2\quad(x\equiv0\pmod2),\qquad T(x)=(3x+1)/2\quad(x\equiv1\pmod2).
\]

For any integer p and odd integer q, set y_0=p and
`y_(j+1)=y_j/2` if y_j is even, otherwise `(3*y_j+q)/2`.
Every division is exact, including for negative values, and
`T^j(p/q)=y_j/q`. The rational parity equals `y_j mod 2` because q is odd.
These are precisely `numStep`, `numIter` and `seedParity`, with argument
order **q,p**. `RealizesWord` instead takes **p,q**, requires **q>0 odd**,
and asserts equality at **every** natural index. It imposes no numerator
positivity, reducedness, or orbit boundedness. See
[Word.lean:297](https://github.com/hipotures/collatz-lab/blob/37d94195119353799c69714a337c4ed2ac7c8752/CollatzLab/Word.lean#L297).

Lean uses Euclidean remainder: `(-5 : Int) % 2 = 1`. The algebraic helpers
requiring only oddness genuinely include negative odd q. `RealizesWord` with
negative q is false by its positivity conjunct; meaningful negative-denominator
coverage comes by simultaneous normalization `(p,q)->(-p,-q)`.
`numIter_equiv` proves representation invariance without a sign restriction.
Odd unreduced scalings are also valid. Even raw denominators do not supply
this numerator-parity semantics, even when the fraction reduces to an odd
denominator. No even-denominator counterexample is a rational counterexample
to the theorems as stated.

The independent checker evaluates **reduced `Fraction` values using T itself**.
It compares their states against affine integer formulas, tests both signs
and odd unreduced representations, and reproduces all three actual 81-step
witnesses. The negative q=-5 witness was additionally checked directly by
Lean reduction. The infinite rational controls survive: seed 1/1 has
`(10)^infinity`, the fixed word of `1->101,0->010`; seed -1/1 has the
constant-one itinerary. Neither is an aperiodic counterexample.

## 3. Gate A: finite compatibility proves the two-return congruence

### 3.1 Independent affine and elimination calculation

For bits b_j, let r_m be the number of ones before m, and

\[
c_m=\sum_{\substack{j<m\\b_j=1}}2^j3^{r_m-r_{j+1}},\qquad
a_m=2^m-3^{r_m}.
\]

Appending a zero leaves c unchanged; appending a one gives
`c_(m+1)=3*c_m+2^m`. Induction on actual rational steps yields

\[
2^m y_m=3^{r_m}p+c_mq,\quad
E_m=a_mp-c_mq=2^m(p-y_m). \tag{1}
\]

If the first ell bits recur at m, apply the length-ell affine identity at
0 and m and subtract. With s=r_ell,

\[
2^\ell(y_{m+\ell}-y_\ell)=3^s(y_m-p).
\]

Since 3 is odd, `2^ell | y_m-p`. Thus `2^(m+ell) | E_m`, without any
aperiodicity or disjointness requirement. In particular ell may exceed m.
For a second match of length f at n, set K=min(m+ell,n+f). Direct expansion
fixes the determinant sign:

\[
a_nE_m-a_mE_n=(a_mc_n-a_nc_m)q=D_{m,n}q. \tag{2}
\]

Both forms are divisible by 2^K; cancel odd q to obtain `2^K | D`.
This is `two_return_divisibility`. The cancellation in
`returnDet_of_forms` needs only `q % 2 = 1`: the explicit Bézout identity
is `2*(-(q/2))+q=1`, also for negative odd q. Raising the first Bézout
argument to K and Euclid's lemma is legitimate; K=0 causes no exception.
The existing helpers in `Tower.lean:97,131` were read, not inferred from
their names.

### 3.2 Remove the infinite realization hypothesis

Fix **any** binary word v with the two finite matches. Let
N=max(m+ell,n+f) and u=v below N, with u=0 at and after N.
There is an actual rational realization of the **whole** word u:
start at 0/1 and prepend its N bits backwards, using

\[
F_0(p/q)=2p/q,\qquad F_1(p/q)=(2p-q)/(3q).
\]

The first branch is even and maps to p/q; the second has odd numerator and
maps to p/q after cancellation of 3. Each denominator remains positive odd.
This finite induction reaches zero after N steps and stays there forever.
It proves `finiteWord_realized`; it assumes no periodicity conjecture.
The seed can be nonpositive: e.g. `1000...` is realized by -1/3. Requiring
a positive numerator would invalidate that witness construction, but that
restriction is absent from the exact theorem and from its use.

All indices in either finite match lie below N. Moreover m,n<=N, so u and v
have identical r_m,c_m,r_n,c_n. The `common_prefix` induction preserves
**both** count and offset and is valid at length zero. Apply (2) to u and
transfer these four quantities back to v. Therefore

\[
\boxed{2^{\min(m+\ell,n+f)}\mid D_{m,n}}
\]

depends solely on the two finite combinatorial matches. This proves the
exact `returnDet_automatic` statement independently. The witness depends on
N. The quantifiers `for every N, there exists a rational seed` do not become
`there exists one rational seed realizing every N`. No bounded height or
common denominator across N was established or used.

### 3.3 The precise small-determinant equivalence and degeneracies

Let B=2^K>0. Divisibility means D=Bd with integer d. If D!=0, then d!=0
and |d|>=1, hence |D|>=B. If D=0, then |D|=0<B. This proves both directions
of `returnDet_small_iff_zero`, with the actual integer absolute value
`absInt x = if x>=0 then x else -x`. Neither direction is vacuous:
the checker supplies many zero and nonzero determinants with true matches.

| Case | Exact analysis |
|---|---|
| m=0 or n=0 | a_0=c_0=0, so D=0 regardless of the other return. No odd-coefficient lemma is applied at zero. |
| m=n | Alternating determinant is zero. |
| ell=0 or f=0 | Empty match is allowed; the corresponding precision is m or n. |
| N=0 | Empty word extended by zeros; seed 0/1 realizes it. |
| ell>m, f>n | The same subtraction and finite-prefix transfer work. No non-overlap premise occurs. |
| Swapping returns | D changes sign; divisibility and absolute-value statements remain valid. |
| Periodic / eventual-zero words | Compatible, including zero determinants. Nothing excludes their rational controls. |
| Zero determinant with nonperiodic continuation | Possible: begin with 111, then append an aperiodic tail. Returns m=1,n=2 with ell=f=1 have D=0. D=0 is not a theorem of periodicity of the full word. |

The no-go is exactly a limitation of this **seed-free congruence plus
nonzero/small premise**. It does not prohibit arguments retaining one fixed
seed, height, signs, denominator bounds, or additional arithmetic relations
over infinitely many returns. No theorem excluding all multi-return methods
has been proved.

### 3.4 Small hostile witnesses

Exhausting all binary words of lengths 0..9, ordered by length then literal
lexicographic order, gives the shortest meaningful extra-bit counterexample
with `0<m<n`, ell>0 and f>0:

```text
word 0010: m=1, n=3, ell=f=1
(a_1,c_1)=(1,0); (a_3,c_3)=(5,4)
D=4; K=min(2,4)=2; 4 divides D, 8 does not.
```

No length below four meets these conditions with a nonzero extra-bit failure.
If the word must start at one, the shortest lexicographic witness is `1011`:
`m=2,n=3,ell=f=1`, `(a_2,c_2)=(1,1)`, `(a_3,c_3)=(-1,7)`, D=8, K=3.
Without nonempty matches, `10` at m=1,n=2 already gives D=-2,K=1.

Dropping the actual-match hypothesis fails on `101`: the alleged length-one
return at m=1 is false, while that at n=2 is true; D=-2,K=2 is not divisible
by 4. Separately, for prefix `10`, m=1,n=2,p=0,q=4,K=2, both E values are
-4 but D=-2. This refutes cancellation without oddness. The latter is an
algebraic false-premise control, not a valid odd-denominator realization.

## 4. Gate B: global return bound for the literal substitution

### 4.1 Structure and independent aperiodicity

The literal images are exactly `mu(1)=100111`, `mu(0)=111110`, and the
one-image begins with one. Let w be this selected fixed word, not the older
four-letter `CollatzLab.w`. Its columns, including n=0, are

\[
(w(6n),\ldots,w(6n+5))=(1,1-w(n),1-w(n),1,1,w(n)). \tag{3}
\]

In particular w(0)=1,w(1)=w(2)=0. The recurrence determines the fixed point
by descent n/6<n at n>0 and agrees with literal substitution. Both symbols
occur. The incidence matrix with rows/columns zero,one is
`[[1,2],[5,4]]`; its eigenvalues are 6,-1. The exact parameter tuple is
`(L,r1,r0,D,Delta)=(6,4,5,7,-1)`.

Here is a second aperiodicity proof, independent of the source's individual
residue calculation. The only consecutive zeros in any image concatenation
occupy columns 1,2 of a parent-one image; a parent-zero image has one isolated
zero in column 5, followed by a forced one. There are arbitrarily late
parent ones, since w(6a)=1. An eventual positive period must preserve a late
00, so it is divisible by six. For p=6d, compare the injective column 1
(or identity column 5) beyond the tail start: this gives the smaller positive
eventual period d. Infinite descent is impossible.

I also checked each source residue branch, where the available zeros are at
`36*start+1` and `36*start+2`:

| p mod 6 | Chosen zero column | Shifted forced-one column |
|---|---:|---:|
| 1 | 2 | 3 |
| 2 | 1 | 3 |
| 3 | 1 | 4 |
| 4 | 2 | 0 of next block |
| 5 | 1 | 0 of next block |

Residue zero descends through column 5 with the same sufficient tail start.
All indices meet the eventual-period hypothesis. Neither proof assumes a
rational seed or infers aperiodicity from finite experiments.

### 4.2 Independent global bound, including overlap attempts

Write M(m,ell) for actual agreement of the first ell symbols at positive m.
If ell>=3, the matched prefix starts 100. Its 00 forces m divisible by six
by (3). If m=6d, column 1 forces a parent match of length

\[
s=\left\lfloor\frac{\ell+4}{6}\right\rfloor. \tag{4}
\]

Indeed j<s implies 6j+1<ell, and equality of the two complement columns
implies w(d+j)=w(j). Conversely the floor gives ell<=6s+1. The constant
column at position 6s explains the +1: it need not force another parent match.

Use strong induction on positive m. For 1<=m<6, shifts 1,2 permit only
ell=0; shifts 3,4,5 permit at most ell=1. Each satisfies `5ell+1<=2m`.
For m>=6 and ell<=2 the inequality is immediate. Otherwise m=6d, with
1<=d<m, and (4) gives a genuine parent match. The induction hypothesis yields

\[
5\ell+1\le30s+6=6(5s+1)\le12d=2m. \tag{5}
\]

This proves `frontierSix_return_bound` for **every** positive shift and every
true match length, including hypothetical ell>m. Equation (5) rules those
overlaps out; it did not assume their absence. Setting ell=m contradicts
`5m+1<=2m`, proving `frontierSix_no_square_prefix` universally. Internal
squares at other starting positions are outside that corollary.

The bound is sharp. If R(m) is the actual longest match, the first unequal
parent images agree in exactly their first column, so
`R(6d)=6R(d)+1`. Since R(3)=1,

\[
m=3\cdot6^k,\quad R(m)=(6^{k+1}-1)/5,\quad 5R(m)+1=2m.
\]

Thus replacing +1 by +2 fails already at (3,1). Replacing the floor in (4)
by ceil(ell/6) fails at (m,ell)=(18,7): the parent return at 3 has length
one, not two. The m>0 safeguard matters: m=0 matches every prefix but cannot
satisfy the proposed inequality even at ell=0.

For completeness the exact remaining return recurrence is
`R(6d+1)=R(6d+2)=1-w(d)`, `R(6d+3)=1`,
`R(6d+4)=2-w(d)`, `R(6d+5)=w(d)`. This follows from at most three columns.
These exact longest-match identities are H, whereas (5) and the square
corollary are K. Aperiodicity ensures every positive-shift mismatch exists.

### 4.3 Counts, signed discrepancy and every fixed-chunk shift

For the kth image of symbol b, the count recurrence is
`W_(k+1)=5*6^k-W_k`. Solving its integer error gives

\[
7W(6^k a,6^k)=5\cdot6^k+(-1)^k(7w(a)-5). \tag{6}
\]

This is exactly `frontierSix_power_count`, including k=0, every a, and both
parent symbols. No frequency limit is assumed. The polynomial identity
`frontierSix_incidence` is K; identifying it as this incidence characteristic
polynomial additionally uses the literal image counts.

For prefix weight W, full images give `W(6n)=5n-W(n)`.
With a remainder t<6, the extra local errors `7H_b(t)-5t` are respectively
`(0,2,4,6,8,10)` and `(0,2,-3,-8,-6,-4)` for b=0,1.
Consequently e(6n+t)=-e(n)+local_error, and induction gives
`|7W(n)-5n|<=10k` for n<6^k. This checks the sign -1 and strict endpoint
in `frontierSix_prefix_discrepancy`. At n=6^k use k+1 or (6).
`frontierSix_prefix_step` itself allows **any t**, as it adds an actual
length-t segment after 6n; only the short-boundary lemma restricts t<6.

The ordinary frequency 5/7 is an H limit deduction. Uniform frequency also
follows H: for S=6^k, each complete aligned S-block has absolute integer
error at most five by (6). Every window has complete blocks and at most two
partial boundary pieces, of total length below 2S. Hence for every a,h,

\[
|7W(a,h)-5h|\le5h/S+10S. \tag{7}
\]

First choose S large, then h large. This is uniform in a, not merely a
prefix average, and verifies the uniform-density premise used below.

For every finite shift t and fixed positive chunk length k, a count cap R
on all chunks forces R/k>=5/7 by summing and taking the prefix frequency.
If `3^R<2^k`, raising to power seven contradicts `3^5>2^7` and `7R>=5k`.
This independently reconstructs the necessary direction of the Phase 11
spectral iff used in `frontierSix_no_uniform_contraction`. Its exact negated
existential retains all t,k,R and `1<=k`. It does not classify partitions
with changing chunk lengths, or establish irrationality by itself.

Finally the weak weight-only gain is bounded by
`ell-W(m)*log2(3/2)`. Equations (5) and the prefix discrepancy make its
asymptotic coefficient at most `2/5-(5/7)*log2(3/2)<0`, the strict sign being
equivalent to `3^25>2^39`. This proves the written ledger limitation H.
It does not eliminate the sharper height argument in the next section.

## 5. Gate C: checked earlier coverage, without an originality claim

### 5.1 Quantified global complexity and direct signed reductions

For every k, let S=6^k. A length-S factor beginning at a has residue a mod S
and intersects at most two adjacent kth power images. Those images are
determined by two parent bits. Thus **globally**, for every k,

\[
P(6^k)\le4\cdot6^k,\qquad C:=\liminf_{n\to\infty}P(n)/n\le4. \tag{8}
\]

No recurrence or empirical saturation premise is missing: every starting
position is covered by division by S. The finite closure certificates are
different evidence. Start with the true initial length-n factor and close
under the six child offsets. Occurrence is preserved at positions 6a+r;
every positive start descends to floor(a/6)<a, proving coverage. Both
inductions work at n=2,6,36,216,864. The independently recomputed exact
counts are **4,17,118,724,2676**. These are finite global-language facts, not
an asymptotic extrapolation; (8) supplies the asymptotic upper bound.

Here are two independent rational deductions, checking the PR's written
reductions without importing an external analytic theorem.

**Density-sensitive closing height.** Put rho=(5/7)*log2(3)>1.
The prefix discrepancy bounds every term `2^j*3^(W(m)-W(j+1))` of c_m
by `2^(rho*m+O(log m))`, uniformly in j<m. Summing at most m terms preserves
that exponential rate. The same holds for |a_m|. For a hypothetical fixed
signed rational seed, |E_m|<=`2^(rho*m+O(log m))` with a seed-dependent
constant. Aperiodicity makes E_m nonzero: E_m=0 would give y_m=p by (1),
forcing a periodic itinerary by determinism. At m=3*6^k the true return
precision has `(m+ell)/m -> 7/5`, whereas
`rho<5/4<7/5` (`3^20<2^35`). The nonzero integer divisibility from §3.1
contradicts the height bound. This is an H irrationality proof for either
numerator sign, not a new K exclusion export.

**Exact integer collision check.** Both 36-step image weights are at most
26. Let A=2^36, B=3^26, C0=3^36-A, R=B/A>1. The actual signed dynamics give
`A*|y_(36(n+1))|<=B*|y_(36n)|+C0*q`. For
z_n=|y_(36n)|+C0*q, B>=A+1 implies `A*z_(n+1)<=B*z_n`.
The intermediate one-step bound
`|y_(j+1)|+q<=(3/2)(|y_j|+q)` therefore gives
`|y_j|<=H*R^(j/36)` with fixed H=(3/2)^35*(|p|+C0*q).
Among 4S+1 factors starting at 0..4S, (8) forces a repeated length-S
factor. Its numerator states are distinct by aperiodicity, and their
difference is a nonzero multiple of 2^S. Thus

\[
2^S\le2H R^{S/9},\qquad
2^{45S}\le(2H)^9 3^{26S}.
\]

This fails along unbounded S since `2^45>3^26` exactly. The argument uses
absolute values, so it covers negative seeds and odd unreduced denominators;
negative q is normalized first. The inference to finite shifts/eventual
tails uses actual rational inverse/forward branches. Both reductions agree
with the Phase 12 written claims; neither is a theorem about every automatic
or morphic word.

### 5.2 Original-source match and actual inspection limits

Originals were freshly fetched. Web HTML navigation failed for the two
Zenodo records; their public APIs provided complete texts and metadata.
The exact checked portions, rather than entire source bibliographies, are
listed below. The no-new-exclusion classification is justified by direct
earlier statements and their valid premises, not by absence of a named example.

| Original and exact location | Premises and match | What this review checked |
|---|---|---|
| J. Allikvere, *Periodic shadows, drift pressure, and transcendence of the 3x+1 conjugacy map*, [Zenodo 21543841](https://doi.org/10.5281/zenodo.21543841), deposited 25 July, updated 13 August 2026; Lemma 4.1, Theorem 4.2(i) | Existing one-density and aperiodicity; shadow precision/length exceeds max(1,d*log2(3)) to exclude a rational seed, either numerator sign. The returns and height in §5.1 meet this literally. | Original TeX statement, height proof and rational-case proof read and independently reconstructed. Earlier preprint, not journal peer review. |
| Same original, Theorem 5.3 and Corollary 5.7 | Non-eventual-periodicity and uniform upper density d; `liminf P(n)/n < 1/(max(1,d*log2(3))-1)` is sufficient. Equations (7),(8), and rho<5/4 make the inequality strict. | Exact statements, density-to-height step and repetition/complexity reduction read; rational case checked independently. The full Subspace Theorem/transcendence application is U here. |
| E. De Jesús, *A drift-sensitive complexity bound for rational points of the 3x+1 conjugacy map*, [Zenodo 23071770 revision-1 PDF](https://zenodo.org/api/records/23071770/files/Drift_Sensitive_Complexity_3x1_Conjugacy_Revision_1.pdf/content), draft 30 September 2026, metadata publication date 1 October; Lemmas 1–3,7–8, Theorem 9, Corollary 15 | For a non-eventually-periodic word with existing frequency d, signed rationality forces `C*(d*log2(3)-1)>=1` when C is finite. Here C<=4 but d*log2(3)-1<1/4. | Original §§2–7 statements and relevant proofs read: numerator congruence, maximal drift from frequency, signed growth, dyadic confinement/counting and the strict tradeoff. No positivity assumption on numerator. Reduced q>0 odd is obtained by normalization. This is an earlier technical-note/preprint result. |
| E. Cassidy, [pinned note 6b805eed, §4.3](https://github.com/eliottcassidy2000/math/blob/6b805eed1613edaedd87965e2b1986390fa84f0e/05-knowledge/results/collatz_procgen_20260922_transversality_foundry.md), 22 September 2026, Lemma G / Theorem R | Not eventually periodic, rational periodic approximants with unbounded precision minus logarithmic height. §5.1 supplies the premise. | Original exact statements and short proofs read; positive denominator normalization is needed in its written height formula. No numerator-sign restriction. Earlier author note. |
| A. Dubickas, *On integer sequences generated by linear maps*, Glasgow Math. J. **51** (2009), 243–252, [DOI](https://doi.org/10.1017/S0017089508004655), Theorem 5 and proof §5 | Literal theorem assumes positive integer orbit tending to infinity; the proof gives the worst-case complexity threshold `1/log2(3/2)`. | Publisher statement and full relevant proof read. Signed density-sensitive reasoning here is an explicit extension of its mechanism, not its literal published theorem. Bound C<=4 alone does not meet its worst-case threshold, and the two finite counts do not prove global inapplicability. |
| K. G. Monks–J. Yazinski, *The autoconjugacy of the 3x+1 function*, Discrete Math. **275** (2004), 219–236, [author text](https://monks.scranton.edu/files/pubs/AutoConjV13.pdf), Theorem 2.7(b), §4.1 | Infinite rational odd-denominator orbits have lower one-density at least log(2)/log(3), with both signs addressed. | Original statement and positive/negative density proof read. Frequency 5/7 exceeds this threshold, so that theorem alone supplies no exclusion here. |

The original Allikvere TeX SHA-256 is
`629e9de77b6ccb06a7dc27193fbee4f6bcaa97bad0e1a697a593fe53d805c522`;
the De Jesús PDF hash is
`6bce09245a13fdf478ce834cbb80762a3a76c379b63b3555e83216aa23939362`.
These fresh bytes match the reviewed `sources.json`. Cassidy, Dubickas and
Monks–Yazinski also matched its recorded hashes. No third-party full text is
redistributed in this review.

The older Phase 11 referee report and corrected findings were read as
dependencies, not treated as independent proof of Phase 12. The broader
Phase 12 source matrix is properly qualified: Molchanov's Mahler hypotheses
are not automatically supplied by unequal-weight automaticity; López–Stoll's
real/2-adic limit transfer is not assumed; the rStation automatic-word
positive-rational claims remain uncertified stronger claims. Their complete
proofs were not newly audited here. No conclusion depends on them, and no
claim of worldwide priority or comprehensive literature coverage is made.
The equal-weight Phase 9 manuscript is outside this review.

The findings' **H/K/F/S distinction passes**: real and uniform limits,
exact longest-return recurrence, ledger asymptotics, global factor argument
and known-method exclusions are H; the explicit integer theorems are K;
bounded enumerations are F; identified source portions are S. Their limited
use of S does not certify every stronger theorem in those originals.

## 6. All 29 new declarations: semantic and quantifier audit

Every source line below refers to the pinned head. Names in the first table
are in `CollatzLab`, in the second `CollatzLab.Morphism`, and in the third
`CollatzLab.FrontierSixChecks`. The appendix preserves exact source signatures.
There are six public definitions and 23 theorems. Each row passes its exact
stated scope; stronger interpretations in the last column are excluded.

`0` in the axioms column means none; `PQ` means `propext, Quot.sound`;
`PCQ` additionally includes `Classical.choice`.

| TwoReturn.lean line / name | Actual type and independent audit | Axioms |
|---|---|---|
| 7 `cycleCoeff` | Int-valued `2^m-3^weight`; negative coefficients allowed; a_0=0. | 0 |
| 10 `returnDet` | Int alternating cross product, with precisely the sign in (2). | 0 |
| 13 `cycleCoeff_odd` | Every Boolean word and m>=1; no assertion at m=0. | PQ |
| 21 `returnDet_elimination` | All p,q:Int and all m,n:Nat; no realization or oddness premise for the identity. | PQ |
| 28 `returnDet_of_forms` | Odd q, same p,q and same K for both divisibilities; q positivity and reducedness absent. | PQ |
| 43 `two_return_divisibility` | Actual infinite realization plus both finite matches; natural m,n,ell,f may be zero. | PQ |
| 59 `finiteWord` | Equal to v exactly below N; false at N and beyond. | 0 |
| 64 `finiteWord_realized` | Every N and every Boolean v has p,q:Int realizing the entire zero extension, not just N bits. | PQ |
| 93 `returnDet_automatic` | Only two match premises; no p,q, frequency, aperiodicity or realization assumption. §3.2 checks transfer endpoints. | PQ |
| 115 `returnDet_zero_or_large` | Disjunction zero or **inclusive** lower bound on absInt D. | PQ |
| 131 `returnDet_small_iff_zero` | **Strict** smallness iff zero; both directions checked in §3.3, including K=0. | PQ |

| FrontierSix.lean line / name | Actual type and independent audit | Axioms |
|---|---|---|
| 7 `frontierSix` | Literal `Images 6`, zero-image first field; orientation checked. | 0 |
| 11 `frontierSix_images` | Lists, prolongability, r1=4,r0=5,D=7,Delta=-1; no inferred analytic limit. | 0 |
| 19 `frontierSix_columns` | Six simultaneous Int parity identities for **every n**, including zero. | PQ |
| 37 `frontierSix_both_letters` | Selected word at 0=true and 1=false. | 0 |
| 42 `frontierSix_not_periodic_from` | Every p, every start, p>=1 and eventual equality imply False; all residues and descent checked. | PQ |
| 81 `frontierSix_not_eventually_periodic` | Exact negation of existing `EventuallyPeriodic`, not just no pure period. | PQ |
| 86 `frontierSix_power_count` | Every k,a; length and start both use 6^k, signed (-1)^k retained. | PQ |
| 93 `frontierSix_incidence` | Int polynomial identity for every x; matrix identification uses literal counts separately. | PQ |
| 97 `frontierSix_prefix_step` | Every n,t; no hidden t<6 premise. Adds the actual tail segment. | PQ |
| 110 `frontierSix_boundary_discrepancy` | Every n,t with t<6, two signed Int bounds; both images exhausted. | PQ |
| 122 `frontierSix_prefix_discrepancy` | Every k,n with **n<6^k**; signed casts, k=0 and alternating error checked. | PCQ |
| 136 `frontierSix_no_uniform_contraction` | No existential t,k,R with k>=1, all-chunk cap and strict `3^R<2^k`. All shifts retained. | PQ |
| 150 `frontierSix_return_bound` | All m,ell:Nat with m>=1 and true initial-prefix match; no rationality or non-overlap premise. | PQ |
| 212 `frontierSix_no_square_prefix` | Every positive m; negates exact initial length-m repeat, by the global bound. | PQ |

| FrontierSixChecks.lean line / name | Actual type and independent audit | Axioms |
|---|---|---|
| 7 `literalStep` | List Int substitution, b=1 selects one-image and every other b selects zero-image. Used only on binary lists. | 0 |
| 10 `literalIter` | Start `[1]`; recursively applies literalStep. | 0 |
| 16 `literal_semantics` | List equalities of lengths 6,36,216 only; no infinite equality asserted by this finite check. | 0 |
| 23 `signed_finite_semantics` | Exact 81 parities at q=1,5,15 and two endpoint numerators; no infinite realization asserted. Third endpoint additionally verified by independent Fraction arithmetic. | 0 |

Definitions/dependencies also read: `weight`, `offset`, `word`, `word_rec`,
`word_block`, `common_prefix`, `affine_prefix`, `matching_prefix_divisibility`,
`prefixCycleForm_nonzero`, `invBranch_step_props`, `realizes_shiftWord_pred`,
`numIter_equiv`, `power_image_count`, `balance_power`, and the necessary
direction of `uniform_contraction_iff_subcritical`. They use the actual map,
not a free symbolic recurrence or a replacement parity convention.

## 7. Reproducible validation and trust evidence

At the **exact detached PR head**, I executed `lake clean` followed by
`bash research/phase12/validate.sh`: **exit 0**. Lean was 4.18.0, with no
external Lake packages. The clean build completed all 85 jobs and performed the
following inherited checks; these rows are commands **inside the script**,
not claims of separate invocations:

| Executed validation | Observed result |
|---|---|
| `lake build`; full FamilyAudit and parser self-test at exact CI count 593 | Pass; 2 valid and 8 hostile parser cases pass. |
| Forbidden-proof scan over `CollatzLab` and `CollatzLab.lean` | No forbidden tokens: no sorry/admit/new axiom/opaque/unsafe/native_decide/implemented_by/extern. |
| `cargo fmt --check`; `cargo clippy --locked --all-targets --all-features -- -D warnings` | Pass. |
| `cargo test --locked --all-targets` | All 94 tests pass; zero failures. |
| `research/phase8/verify_polynomial.py`; `research/mahler-uncovered/verify_uncovered.py --check` | Pass. |
| `research/phase9/verify_independent.py`; `paper/check_tex.py` and generated Lean-name compilation | Pass; all 32 named declarations compile. This is a static manuscript check, not PDF review. |
| Phase 10 `verify_unequal.py`, `search_unequal.py`, `verify_spectral.py`, `verify_sparse_family.py`, `generate_catalogue.py`, each with `--check` | Pass. |
| Phase 11 `verify_noncontracting.py`, `verify_spectral_boundary.py`, `verify_partial_return.py`; Phase 11 and Phase 12 signature files | Pass. |
| Phase 12 `verify_returns.py --check`; declaration-inventory comparison; `git diff --check` | Deterministic evidence matches; inventory agrees; pass. |

Additional, **separate** invocations passed:

```bash
lake env lean research/phase12/Signatures.lean
set -o pipefail
lake env lean research/lean-audit/FamilyAudit.lean |
  tee /tmp/phase12-referee-axioms.log |
  python3 research/lean-audit/check_axioms.py --expected-count 593
```

Every one of the 593 actual axiom records was checked against its exact
ordered manifest and foundation allowlist. The 564 baseline entries are
preserved in order; all 29 new public source declarations occur exactly once.
The changed-path audit shows no changed older proof bodies or semantic
definitions. An independent `#check` pass printed all 29 interfaces and
`#print` printed all six new definition bodies. Across all 593 declarations:
128 have no axioms, 21 use only propext, 271 use propext/Quot.sound, and
173 use propext/Classical.choice/Quot.sound. Among the new 29 these numbers
are respectively **10,0,18,1**. No arithmetic oracle or unproved mathematical
assumption is hidden in those foundations. `family_ring` expands integer
algebra and calls kernel-checked tactics; the finite checks use ordinary
`decide`, not native execution as a proof bypass.

The standalone checker, runnable from this review branch or any directory,
imports no project arithmetic or evidence:

```bash
python3 research/phase12/referee_checks.py > /tmp/phase12-referee-checks.json
```

It exited 0. Its explicit deterministic output contains:

```text
1023 words, lengths 0..9
574327 ordered return pairs, including 46390 overlapping pairs
149500 nonzero and 424827 zero determinants
85484 failures of an unjustified extra precision bit
16368 signed finite witnesses; 36868 affine-form checks
8 substitution levels 0..7; 279936 indexed symbols at level 7
335915 maximal finite return checks across those levels
660 uniform-window checks; all three signed 81-step witnesses
exact closed languages 4,17,118,724,2676 at 2,6,36,216,864
```

Language witnesses, both sides of the iff, the determinant sign, degenerate
positions, signed/reducible fractions, false matches, and even-denominator
cancellation controls are explicit assertions. Full byte encoding is **0/1
bytes**, so its hashes differ intentionally from the author's ASCII `0/1`
encoding; this is not an evidence disagreement. The JSON output SHA-256 is
`1699d278be65c3a1a2d553ca9a3ab187dd7e8f93e69c71386abc0378d75c07bf`.

Supplementary local logs (regenerable; not required tracked artifacts):
`/tmp/phase12-referee-validation.log` SHA-256
`329fc68e3a2beded5a8e67de3c68637b7400159a14886dfae0dc2904e69173e3`;
`/tmp/phase12-referee-axioms.log` SHA-256
`d21b58b4544ffe1261730e366fd97a1e7fa79dbf22511f8bb3926c98c929e44e`;
`/tmp/phase12-referee-interfaces.log` SHA-256
`96257b93766cc82084a2e0c341ac24ebc09800f75b6790af65d9c73f2c3e5e75`.
Build timings can change the validation log hash on another run. The script,
proofs, exact outputs, primary URLs and source hashes provide durable evidence.

The required validation had no failure. A reviewer-only printing command
initially failed on an unsupported `pp.width` formatting option; removing
that option made it pass. An initial SSH clone failed and HTTPS succeeded.
Neither was a theorem failure. The exact source remained clean throughout.
The author's earlier green CI was not substituted for this local validation.
Its exact-head [run 43638392392](https://github.com/hipotures/collatz-lab/actions/runs/43638392392)
was also read live: both `lean` and `check`, including their individual steps,
were completed/success. This is separate evidence from the local clean run.

## 8. Recommendations and remaining owner decisions

1. Consider PR #25 as a correct structural/no-go formalization at this SHA;
   retain its no-new-exclusion framing. No theorem repair is required by this
   audit. The two small editorial suggestions in §1 are nonblocking.
2. Keep the all-multi-return, all-automatic-word, general Periodicity and
   transcendence claims outside the verified result. Preserve H/K/F/S labels
   and the exact signed domain.
3. Re-fetch and review overlap in Lean imports, audit manifest and CI before
   any future integration. If the reviewed source or base changes, refresh
   validation and reconcile changes rather than applying this verdict to an
   unseen head. The owner alone decides integration of either PR.
4. Do not treat this AI-assisted audit as human peer review or approval for
   submission. A separate formalization publication would need a human
   mathematical/editorial assessment of contribution and disclosures.

No new exclusion target, optimal reconstruction-height investigation, Phase 13
work, manuscript edit, publication, merge, issue closure, or external referee
contact was performed. The report completes the requested audit; the source
PR and existing issues remain open for their owner's decisions.


## Appendix A. Exact new source interfaces

The following headers are extracted from the pinned source, preserving types,
implicit parameters and quantifiers. Proof bodies are omitted. Definition bodies
are included. Namespace context is stated for each file; `open Morphism`
applies to the first and third blocks, as in the source.

### TwoReturn.lean — namespace `CollatzLab`

```lean
-- TwoReturn.lean:7
def cycleCoeff (v : Nat → Bool) (m : Nat) : Int :=
  (2 : Int) ^ m - (3 : Int) ^ weight v m

-- TwoReturn.lean:10
def returnDet (v : Nat → Bool) (m n : Nat) : Int :=
  cycleCoeff v m * offset v n - cycleCoeff v n * offset v m

-- TwoReturn.lean:13
theorem cycleCoeff_odd (v : Nat → Bool) (m : Nat) (hm : 1 ≤ m) :
    cycleCoeff v m % 2 = 1

-- TwoReturn.lean:21
theorem returnDet_elimination (v : Nat → Bool) (m n : Nat) (p q : Int) :
    cycleCoeff v n * prefixCycleForm v m p q -
      cycleCoeff v m * prefixCycleForm v n p q = returnDet v m n * q

-- TwoReturn.lean:28
theorem returnDet_of_forms (v : Nat → Bool) (m n K : Nat) (p q : Int)
    (hq : q % 2 = 1)
    (hm : (2 : Int) ^ K ∣ prefixCycleForm v m p q)
    (hn : (2 : Int) ^ K ∣ prefixCycleForm v n p q) :
    (2 : Int) ^ K ∣ returnDet v m n

-- TwoReturn.lean:43
theorem two_return_divisibility (v : Nat → Bool) (m n ell f : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    (2 : Int) ^ min (m + ell) (n + f) ∣ returnDet v m n

-- TwoReturn.lean:59
def finiteWord (v : Nat → Bool) (N j : Nat) : Bool :=
  if j < N then v j else false

-- TwoReturn.lean:64
theorem finiteWord_realized : ∀ N (v : Nat → Bool),
    ∃ p q : Int, RealizesWord p q (fun j => bit (finiteWord v N j))

-- TwoReturn.lean:93
theorem returnDet_automatic (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    (2 : Int) ^ min (m + ell) (n + f) ∣ returnDet v m n

-- TwoReturn.lean:115
theorem returnDet_zero_or_large (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    returnDet v m n = 0 ∨
      (2 : Int) ^ min (m + ell) (n + f) ≤ absInt (returnDet v m n)

-- TwoReturn.lean:131
theorem returnDet_small_iff_zero (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    absInt (returnDet v m n) < (2 : Int) ^ min (m + ell) (n + f) ↔
      returnDet v m n = 0

```

### FrontierSix.lean — namespace `CollatzLab.Morphism`

```lean
-- FrontierSix.lean:7
def frontierSix : Images 6 where
  zero := fun j => decide (j.val < 5)
  one := fun j => decide (j.val = 0 ∨ 3 ≤ j.val)

-- FrontierSix.lean:11
theorem frontierSix_images :
    List.ofFn frontierSix.one = [true, false, false, true, true, true] ∧
    List.ofFn frontierSix.zero = [true, true, true, true, true, false] ∧
    image frontierSix true 0 = true ∧
    weight (image frontierSix true) 6 = 4 ∧
    weight (image frontierSix false) 6 = 5 ∧
    frequencyDen frontierSix = 7 ∧ weightDelta frontierSix = -1

-- FrontierSix.lean:19
theorem frontierSix_columns (n : Nat) :
    parityWord frontierSix (6 * n) = 1 ∧
    parityWord frontierSix (6 * n + 1) = 1 - parityWord frontierSix n ∧
    parityWord frontierSix (6 * n + 2) = 1 - parityWord frontierSix n ∧
    parityWord frontierSix (6 * n + 3) = 1 ∧
    parityWord frontierSix (6 * n + 4) = 1 ∧
    parityWord frontierSix (6 * n + 5) = parityWord frontierSix n

-- FrontierSix.lean:37
theorem frontierSix_both_letters :
    word frontierSix 0 = true ∧ word frontierSix 1 = false

-- FrontierSix.lean:42
theorem frontierSix_not_periodic_from (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → parityWord frontierSix (n + p) = parityWord frontierSix n) → False

-- FrontierSix.lean:81
theorem frontierSix_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord frontierSix)

-- FrontierSix.lean:86
theorem frontierSix_power_count (k a : Nat) :
    7 * (weight (fun j => word frontierSix (6 ^ k * a + j)) (6 ^ k) : Int) =
      5 * (6 ^ k : Nat) + (-1 : Int) ^ k * (7 * bit (word frontierSix a) - 5)

-- FrontierSix.lean:93
theorem frontierSix_incidence (x : Int) :
    (x - 1) * (x - 4) - 10 = (x - 6) * (x + 1)

-- FrontierSix.lean:97
theorem frontierSix_prefix_step (n t : Nat) :
    (weight (word frontierSix) (6 * n + t) : Int) =
      5 * (n : Int) - (weight (word frontierSix) n : Int) +
        (weight (fun j => word frontierSix (6 * n + j)) t : Int)

-- FrontierSix.lean:110
theorem frontierSix_boundary_discrepancy (n t : Nat) (ht : t < 6) :
    -10 ≤ 7 * (weight (fun j => word frontierSix (6 * n + j)) t : Int) - 5 * (t : Int) ∧
      7 * (weight (fun j => word frontierSix (6 * n + j)) t : Int) - 5 * (t : Int) ≤ 10

-- FrontierSix.lean:122
theorem frontierSix_prefix_discrepancy : ∀ k n : Nat, n < 6 ^ k →
    -10 * (k : Int) ≤ 7 * (weight (word frontierSix) n : Int) - 5 * (n : Int) ∧
      7 * (weight (word frontierSix) n : Int) - 5 * (n : Int) ≤ 10 * (k : Int)

-- FrontierSix.lean:136
theorem frontierSix_no_uniform_contraction :
    ¬ ∃ t k R : Nat, 1 ≤ k ∧
      (∀ n, weight (fun j => word frontierSix (t + k * n + j)) k ≤ R) ∧
      (3 : Int) ^ R < (2 : Int) ^ k

-- FrontierSix.lean:150
theorem frontierSix_return_bound (m : Nat) : ∀ ell, 1 ≤ m →
    (∀ j, j < ell → parityWord frontierSix (m + j) = parityWord frontierSix j) →
    5 * ell + 1 ≤ 2 * m

-- FrontierSix.lean:212
theorem frontierSix_no_square_prefix (m : Nat) (hm : 1 ≤ m) :
    ¬ (∀ j, j < m → parityWord frontierSix (m + j) = parityWord frontierSix j)

```

### FrontierSixChecks.lean — namespace `CollatzLab.FrontierSixChecks`

```lean
-- FrontierSixChecks.lean:7
def literalStep (xs : List Int) : List Int :=
  xs.flatMap (fun b => if b = 1 then [1, 0, 0, 1, 1, 1] else [1, 1, 1, 1, 1, 0])

-- FrontierSixChecks.lean:10
def literalIter : Nat → List Int
  | 0 => [1]
  | k + 1 => literalStep (literalIter k)

-- FrontierSixChecks.lean:16
theorem literal_semantics :
    (List.range 6).map (parityWord frontierSix) = literalIter 1 ∧
    (List.range 36).map (parityWord frontierSix) = literalIter 2 ∧
    (List.range 216).map (parityWord frontierSix) = literalIter 3

-- FrontierSixChecks.lean:23
theorem signed_finite_semantics :
    (List.range 81).map (seedParity 1 553314936599421495781373) = (literalIter 3).take 81 ∧
    numIter 1 553314936599421495781373 81 = 119765852333396201932225031 ∧
    (List.range 81).map (seedParity 5 (-2069128595461409219917839)) = (literalIter 3).take 81 ∧
    numIter 5 (-2069128595461409219917839) 81 = -447866004387740064765897887 ∧
    (List.range 81).map (seedParity 15 (-6207385786384227659753517)) = (literalIter 3).take 81

```

## Appendix B. Additional kernel semantic controls

These reviewer examples were compiled independently with exit 0. To reproduce,
write the block to `/tmp/Phase12RefereeSemantics.lean` and run
`lake env lean /tmp/Phase12RefereeSemantics.lean` from the pinned source checkout.
They add no declarations to the trusted project.

```lean
import CollatzLab
open CollatzLab CollatzLab.Morphism

example : (-5 : Int) % 2 = 1 := by decide

example (p q : Int) (hq : q % 2 = 1) (j : Nat) :
    seedParity (-q) (-p) j = seedParity q p j := by
  exact (numIter_equiv (p := -p) (q := -q) (p' := p) (q' := q)
    (by omega) hq (by family_ring) j).2

example : ¬ RealizesWord 1 (-1) (fun _ => 1) := by
  intro h
  have := h.1
  omega

example (j : Nat) (hj : j < 1) :
    let v : Nat → Bool := fun i => decide (i = 2)
    v (1 + j) = v j ∧ v (3 + j) = v j := by
  have h : j = 0 := by omega
  subst j
  decide

example :
    let v : Nat → Bool := fun i => decide (i = 2)
    returnDet v 1 3 = 4 ∧ ¬ (2 : Int)^3 ∣ returnDet v 1 3 := by decide

example :
    let v : Nat → Bool := fun i => decide (i ≠ 1)
    returnDet v 2 3 = 8 ∧ ¬ (2 : Int)^4 ∣ returnDet v 2 3 := by decide

example :
    let v : Nat → Bool := fun i => decide (i = 0)
    prefixCycleForm v 1 0 4 = -4 ∧ prefixCycleForm v 2 0 4 = -4 ∧
    returnDet v 1 2 = -2 ∧ ¬ (2 : Int)^2 ∣ returnDet v 1 2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example :
    (List.range 81).map (seedParity (-5) 2069128595461409219917839) =
      (FrontierSixChecks.literalIter 3).take 81 ∧
    numIter (-5) 2069128595461409219917839 81 = 447866004387740064765897887 := by decide
```
