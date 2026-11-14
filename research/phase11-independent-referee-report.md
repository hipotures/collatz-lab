# Independent Phase 11 mathematical referee report — issue #21

Review date: 14 November 2026 (UTC). This is an independent AI-assisted review,
not independent human peer review or journal acceptance.

## Executive verdict and exact scope

**Mathematical verdict: PASS for the exact formal statements. Overall
integration recommendation: CONDITIONAL — correct attribution and the
specific documentation error below, then merge as formal research if the owner
approves. Publication verdict: FAIL as a separate new-theorem paper on this
evidence; a formalization note is a conditional possibility.**

I found no counterexample, missing mathematical lemma, semantic substitution,
or proof bypass in the four principal results. I reconstructed their arithmetic
and spectral arguments independently, checked their actual quantifiers and
rational dynamics, and reproduced the local validation on the exact PR head.
This verdict does not rely on the earlier green CI or on any external
irrationality claim.

The originality assessment is materially different from “unverified” alone:
the sharp offset bound, the general partial-repetition inequality, and the
unbounded-square exclusion already occur in an earlier accessible preprint.
Both concrete exclusions are elementary applications of that criterion.
Their explicit instantiation and Lean formalization can still be useful.
Moreover, §2.4 gives a separate deduction of both examples, and a larger
single-variable-column family, from the published 2009 counting mechanism.
First discovery of those particular corollaries has not been established.

- Audited PR: [#20](https://github.com/hipotures/collatz-lab/pull/20), **open,
  unmerged**, branch `codex/phase11-noncontracting`, exact head
  `d270b4466794badc49da6feebefeda77f5793e16`.
- Base: `main` at `2efdd2b531d511a8c6204e1f43179761585ab066`.
- Review task: [issue #21](https://github.com/hipotures/collatz-lab/issues/21).
  Implementation [issue #19](https://github.com/hipotures/collatz-lab/issues/19)
  remains open. Issue #15 and all Phase 9/manuscript artifacts are untouched.
- Review branch: `review/phase11-independent-audit`, created from that main in
  `/home/user/DEV/collatz-lab-phase11-review`. Validation used the separate,
  detached clone `/home/user/DEV/collatz-lab-phase11-audit`.
- All source references below mean the pinned PR head, not an unspecified
  current version. No changes to PR #20's implementation are proposed here.

Evidence labels: **H** independently reconstructed human-readable proof;
**K** locally kernel-checked proposition; **F** finite exact computation;
**S** original source statement and specified proof portions read;
**U** unresolved or unchecked claim. These labels are independent: K alone is
not a semantic audit, and F is never an infinite theorem.

## Findings and required corrections

| ID | Severity | Finding and evidence | Required action |
|---|---|---|---|
| P1 | High for originality/publication; no correctness defect | Earlier exact overlap: Allikvere, Lemma 2.1, Theorem 2.3 and Corollary 3.2; Cassidy, Theorem R. The core inequalities and signed scope precede Phase 11. The published Dubickas mechanism also yields both examples (§2.4). | Add these primary citations and exact overlap to Phase 11 findings and any future publication framing. Describe the core exclusion as an independent elementary formalization of an earlier criterion. |
| M1 | Medium, scientific interpretation | `research/phase11-findings.md:53,102–105` claims that deleting either safeguard makes the theorem false. Both listed rational controls are periodic. They cannot falsify a theorem that still assumes non-eventual-periodicity. | Change “Both conditions are essential” to “Both conditions are used in this criterion”, and replace the line-105 sentence by: “Dropping non-eventual-periodicity is false, as the all-one control shows. Dropping repetition while retaining non-eventual-periodicity would assert the open rational Periodicity Conjecture.” |
| L1 | Low, editorial | The “Research in progress” paragraph at `research/phase11-findings.md:42–47` still says the square-prefix proof is being developed, while later sections correctly record its completion. | Mark it as historical or update it. |
| L2 | Scope reminder, not a defect | The real-frequency limit is deduced from integer estimates; a conjugacy-value formulation additionally uses the published parity bijection. Neither is a Lean real/2-adic analysis theorem here. | Preserve those distinctions. Do not label the analytic or transcendence statements Lean-verified. |

**Critical findings: none.** No change to a Lean proof or its assumptions is
needed for the results audited here. M1 is a correction to prose, not a
counterexample to an exported theorem.
PR #20 already disclaims priority. P1 asks that newly established overlap be
documented precisely; it does not accuse that PR of making a first-discovery
claim.

## 1. Independent arithmetic reconstruction

### 1.1 Actual rational dynamics and the affine identity

Let `q > 0` be odd and `p` any integer. Put `y_0=p` and

\[
y_{j+1}=\begin{cases}y_j/2,&y_j\equiv0\pmod2,\\
(3y_j+q)/2,&y_j\equiv1\pmod2.\end{cases}
\]

Both divisions are exact. Thus `y_j/q` is precisely the j-th iterate of the
shortcut/accelerated map `T(x)=x/2` or `(3x+1)/2` on `Q ∩ Z_2`.
This is not the odd-only map that divides out all powers of two.
Since every odd integer is 1 modulo two, the parity of `y_j/q` is `y_j mod 2`.
No positivity or reducedness assumption on `p/q` is needed.

For a binary block U of length m with ones at positions
`d_0 < … < d_(r-1)`, define

\[
A=2^m,\quad B=3^r,\quad
c(U)=\sum_{i=0}^{r-1}2^{d_i}3^{r-1-i}.
\]

Induction on the block length, appending a zero or one, gives respectively
`c(U0)=c(U)` and `c(U1)=3c(U)+2^m`. For any actual occurrence beginning at a,

\[
2^m y_{a+m}=3^r y_a+c(U)q. \tag{1}
\]

This derives the recurrence from the rational map itself. The prefix offset
is independent of the seed. It is not a freely chosen symbolic orbit.

### 1.2 Matching prefixes give precision m+ell

Suppose the actual parity word v satisfies
`v(m+j)=v(j)` for `0 ≤ j < ell`. Let s and d be the one-count and offset of
that length-ell prefix. Applying (1) at positions zero and m and subtracting,

\[
2^\ell(y_{m+\ell}-y_\ell)=3^s(y_m-p).
\]

Since `gcd(2^ell,3^s)=1`, `2^ell | (y_m-p)`. Define the integer closing form

\[
E_m=(2^m-3^r)p-c(U)q=2^m(p-y_m).
\]

It follows that

\[
2^{m+\ell}\mid E_m. \tag{2}
\]

Here `ell=0`, `ell<m`, `ell=m`, and overlapping returns `ell>m` are all
permitted. For a square prefix UU, the two equations requested in issue #21
are exactly

\[
Ay_m=Bp+cq,\qquad Ay_{2m}=By_m+cq,
\]

and (2) becomes `4^m | E_m`. An m-step return in the word is not itself a
return of the orbit state; the divisibility argument is necessary.
For m>0 the match also says that v agrees with `U^infinity` through m+ell:
repeatedly subtract m from a matched index. This includes ell>m and supplies
the exact connection to the earlier periodic-approximation criteria.

### 1.3 Nonzero requires determinism, not the Periodicity Conjecture

Assume `m≥1` and v is not eventually periodic. If `E_m=0`, then the equality
above and `2^m≠0` imply `y_m=p`. The numerator recurrence with this same fixed
q is deterministic, so `y_(m+j)=y_j` for every j by induction. Its entire
parity itinerary is periodic with period m, contradicting realization of v.
Thus `E_m≠0`.

Only “this orbit returns, therefore its itinerary is periodic” is used.
There is no assertion that arbitrary rational seeds must return. In fact,
“v is not purely periodic” would suffice for this particular nonzero step;
the formal assumption “not eventually periodic” is stronger and safe.
For `m=0`, `E_0=0`; the formal divisibility theorem permits this, while every
nonzero/exclusion use explicitly requires `1≤m`.

### 1.4 Universal and sharp offset bounds

For all length-m words, `0≤c≤3^m-2^m`. One proof is induction: in the one
case use `3(3^m-2^m)+2^m=3^(m+1)-2^(m+1)`; in the zero case the old bound
is no larger than the next bound. Also `r≤m` and
`|2^m-3^r|≤3^m`. Therefore, with `C=|p|+q`,

\[
|E_m|\le |2^m-3^r||p|+cq\le C3^m. \tag{3}
\]

This is uniform over numerator signs and unreduced odd-denominator fractions.
For a signed q replace q in the bound by `|q|`, or normalize `(p,q)` to
`(-p,-q)` first. A height bound with a negative q on the right is not claimed.

Retaining r yields the sharper exact offset cap. There are `r-1-i` ones
strictly after `d_i`, so `d_i≤m-r+i`. Consequently

\[
c\le\sum_{i=0}^{r-1}2^{m-r+i}3^{r-1-i}
 =2^{m-r}(3^r-2^r)=2^{m-r}3^r-2^m. \tag{4}
\]

Equality is attained by `0^(m-r)1^r`. For `r=0`, both sides are zero.
The natural subtraction `m-r` in Lean is ordinary nonnegative subtraction
because `weight_le` proves `r≤m`; no truncated negative exponent is hidden.
Set `H=2^(m-r)3^r`. Both A and B are at most H, so

\[
|E_m|\le |A-B||p|+cq\le CH. \tag{5}
\]

The offset cap is sharp. The final triangle-inequality height bound need not
be sharp for a specified p or for the two concrete substitutions.
Combining (2), nonzero and (5), then cancelling positive `2^(m-r)`, gives

\[
2^{\ell+r}\le C3^r. \tag{6}
\]

This is the precise partial-return criterion, not a claim that every finite
partial return excludes a rational seed.

### 1.5 Unbounded square prefixes exclude rational realization

If v is not eventually periodic and has square prefixes UU with unbounded
positive half-lengths m, (2)–(3) imply

\[
4^m\le |E_m|\le C3^m. \tag{7}
\]

This is impossible for one fixed finite C: by the binomial theorem,
`(4/3)^m=(1+1/3)^m≥1+m/3`, which exceeds C for sufficiently large m.
The formal proof uses an explicit larger integer witness rather than a real
limit. Thus no rational seed realizes v. No one-density hypothesis,
contraction estimate, or unproved periodicity principle occurs.

For a prolongable length-L substitution starting with 11, equality of parent
letters gives equal iterated images. With `U=mu^k(1)`, the word starts UU
and `|U|=L^k→∞`. Independent non-eventual-periodicity then gives the general
initial-double corollary. Starting with 11 is sufficient; it is not claimed
necessary for having unbounded square prefixes.

### 1.6 Independent finite instance

Take `U=110`, `m=3`, `r=2`, `c=5`, `p=39`, `q=5`. Actual numerator iteration is

```text
39 -> 61 -> 94 -> 47 -> 73 -> 112 -> 56
```

The six parities are `110110`.
`8*47=9*39+5*5=376` and `8*56=9*47+5*5=448`.
`E=(8-9)*39-5*5=-64=8*(39-47)`, divisible by `4^3=64`.
The crude height is `44*27=1188`; the sharper height is `44*18=792`.
The exact triangle bound here is `39+25=64`.
This verifies a nonzero square instance by rational arithmetic. It does not
assert that this finite witness realizes either infinite substitution word.

The second independent instance uses the length-eight block `10111111`, a
length-four return at m=8, and signed denominator `(p,q)=(1203,-5)`.
Its closing form is `-2306048=-563*4096`, giving precisely the guaranteed
`2^(8+4)` modulus. See the reproducible independent computation in Appendix B.

## 2. The two concrete words

### 2.1 The 110/111 word

The literal images are `mu(1)=110`, `mu(0)=111`, with columns
`w(3n)=w(3n+1)=1`, `w(3n+2)=1-w(n)`. Both symbols occur at indices zero and two.

Here is a different aperiodicity proof. If `a=v_3(n+1)` then n has exactly a
trailing base-three digits equal to two. Repeatedly using the variable column
therefore gives

\[
w(n)=1\quad\Longleftrightarrow\quad v_3(n+1)\text{ is even}. \tag{8}
\]

Suppose p>0 were an eventual period and put `a=v_3(p)`. Choose arbitrarily
large n with `v_3(n+1)=a+1`. Then `v_3(n+p+1)=a`, so the two values in (8)
differ, a contradiction. This proof is about the word alone and uses no seed
or exclusion theorem. The Lean period-residue descent is a second correct proof.

Every three consecutive letters contain two forced ones. If all length-k
chunks starting at any t had at most R ones, summing three such chunks and
partitioning the same length-3k interval into triples gives `2k≤3R`.
Thus `3^(3R)≥3^(2k)>2^(3k)` for k>0, incompatible with `3^R<2^k`.
This rules out **every positive fixed chunk length, at every finite shift**,
not only multiples of three.

Writing W(n) for its prefix count, the forced first two columns give
`W(3n+r)+W(n)=3n+r` for `r=0,1,2`. For `D(n)=4W(n)-3n`, this is
`D(3n+r)=r-D(n)`, whence `|D(n)|≤2k` for `n<3^k` by induction.
Taking k just above `log_3 n` proves `W(n)/n→3/4` for all prefixes.
The integer inequality is K; this real-limit deduction is H, not K.
The exact power count is `4W_k(b)=3*3^k+(-1)^k(4b-3)`.

The initial 11 gives squares with half-length `3^k`. Applying §1 proves the
universal rational exclusion even though no uniform contraction can apply.
The two affine maps are `(9y+5q)/8` and `(27y+19q)/8`, exactly as actual
numerator dynamics requires; no equal-multiplier substitution has been made.

### 2.2 The 1011/1111 word and the genuine partial return

Here `mu(1)=1011`, `mu(0)=1111`. The variable column is **index one**:
`w(4n+1)=1-w(n)`; columns zero, two and three are one. Its initial word is 101,
with both symbols at indices zero and one.

For an independent aperiodicity description, let `v_4(a)` mean the largest t
with `4^t | a` (equivalently `floor(v_2(a)/2)` for a≠0). Then

\[
w(n)=1\quad\Longleftrightarrow\quad v_4(3n+1)\text{ is even}. \tag{9}
\]

Indeed index `4n+1` multiplies `3n+1` by four, whereas each forced column has
valuation zero in this convention. Given a proposed eventual period p, put
`a=v_2(p)`. Choose b>a with `floor(b/2)` of opposite parity to `floor(a/2)`.
There are arbitrarily large n with `v_2(3n+1)=b`, since three is invertible
modulo `2^(b+1)`. Then `v_2(3(n+p)+1)=a`, contradicting (9).
The Lean modulo-four descent also handles each residue and is correct.

The equality of letters at indices zero and two gives, for `S=4^k`,
`w[0,S)=w[2S,3S)`. This is a return at **m=2S, ell=S**, rather than an
invocation of the initial-double theorem. For `r=W(2S)`, balance gives the
exact identity

\[
5r=8S-3(-1)^k,\qquad 8S-3\le5r\le8S+3. \tag{10}
\]

A hypothetical realization has fixed `C=|p|+q≥1`. Equation (6) gives
`2^(S+r)≤C3^r`. Raising to five and using both sides of (10),

\[
2^{13S}\le 8\,2^{5(S+r)}
 \le8C^5 3^{5r}\le216C^5 3^{8S}. \tag{11}
\]

Since `2^13=8192>6561=3^8`, (11) is impossible along unbounded `S=4^k`.
The constant 216 is `2^3*3^3`, not a suppressed asymptotic term.
This correctly applies the partial-return theorem. It neither assumes nor
needs a proof that all square prefixes are absent.

Its spectral parameters are `(L,r0,r1,D,Delta)=(4,4,3,5,-1)` and
`3^4=81>32=2^5`. The generic theorem in §3 therefore rules out every shifted
fixed-length contraction partition. Aperiodicity and exclusion remain
separate from that obstruction.

### 2.3 Shifts, eventual tails, signs and non-vacuity

The inverse branches `z↦2z` and `z↦(2z-1)/3` take rational 2-adic integers
to rational 2-adic integers with the prescribed parity. In integer pairs they
are `(2p,q)` and `(2p-q,3q)`. Repeatedly prepend the missing t bits to a
hypothetical seed for the t-shift. It would realize the original excluded
word. This proves **all finite shifts** without presuming that the shifted
word itself still has square prefixes.

After s actual iterations, a rational seed is still `(y_s,q)` and its parity
word is the corresponding tail. This gives **all eventual shifted tails**,
with independently quantified `s,t≥0`. Equivalent odd-denominator fractions
have identical parities, proved by cross-multiplication and exact division.
For negative odd q, replace `(p,q)` by `(-p,-q)`; both numerator signs and
unreduced representations are included. `RealizesWord` itself requires
positive q: the signed raw-tail corollaries are what give non-vacuous coverage
of negative denominators.

The domain is all of `Q ∩ Z_2`, not rationals with a genuinely even reduced
denominator. Equivalent even/even representations are covered through their
odd-denominator representation, not by pretending the raw even-denominator
numerator map has the same parity interpretation.

Every finite binary prefix has an actual integer realization: at each stage
exactly one of the two residue lifts supplies the next parity. Such finite
witnesses are consistent with excluding an infinite itinerary. The published
parity bijection also supplies a unique 2-adic seed for every infinite word;
this existence/uniqueness result is external, not a new Lean theorem here.

Mandatory controls are retained: `1/1` realizes `(10)^infinity`, the fixed
word of `1->101,0->010`, and `-1/1` realizes the all-one word. Both are
periodic. They demonstrate that neither unequal weights nor arbitrarily long
squares alone imply exclusion. They supply no counterexample to the open
claim that every non-eventually-periodic parity word has irrational seed.
The alternating control itself has unbounded squares at even half-lengths;
its failed initial-double condition must not be confused with absence of
square prefixes in the general theorem.

### 2.4 A broader exclusion from the published counting mechanism

This is an additional **H proof, not a new K export**. It adapts the argument
of Dubickas, Theorem 5, Section 5 (2009), which is stated for escaping positive
integer orbits. The extension to signed rationals is supplied explicitly here;
it is not attributed to the original theorem's literal statement. [Original
paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/C40C0C07FEC20797475BB2899C436C9A/S0017089508004655a.pdf/on_integer_sequences_generated_by_linear_maps.pdf).

Let a non-eventually-periodic word v be realized by p/q, q>0 odd, and let
P(n) be its number of distinct length-n factors. Actual numerator states obey

\[
|y_{j+1}|+q\le\tfrac32(|y_j|+q),\quad
|y_j|+q\le C(3/2)^j,\qquad C=|p|+q.
\]

Among the P(n)+1 length-n factors beginning at indices 0 through P(n), two
are equal, at a<b≤P(n). The same affine subtraction as §1.2 gives
`2^n | (y_b-y_a)`. The difference is nonzero, since equal states would imply
eventual periodicity. Hence

\[
2^n\le |y_b-y_a|\le2C(3/2)^{P(n)}. \tag{14}
\]

In particular `liminf P(n)/n≥log(2)/log(3/2)`. Negative p and unreduced
representations cause no change; signed q is normalized as before.

Now consider **any** L≥2 and `1≤c<L`, with images
`mu(0)=1^L`, `mu(1)=1^c 0 1^(L-c-1)`. Its fixed word begins with one.
It is not eventually periodic: for a period p not divisible by L, choose
an arbitrarily late zero at `L*(L a)+c`; adding p sends it to a forced-one
column. If L divides p, comparing the complement column c gives the smaller
positive eventual period p/L. Strong descent excludes every p.

The two t-fold images differ in just one position
`h_t=c(1+L+...+L^(t-1))` of their length `S=L^t`; off that position their
letters are identical, and at that position they are a fixed bijection of the
parent bit. This follows by induction under substitution. A factor of length
LS contains exactly L such variable positions, belonging to consecutive parent
letters. The whole factor is determined by its starting residue modulo S and
that length-L parent factor. Every length-L factor has at most one zero, so
there are at most L+1 of them. Therefore

\[
P(L^{t+1})\le (L+1)L^t. \tag{15}
\]

Substitute n=LS and this cap into (14) and multiply by `2^((L+1)S)`:

\[
2^{(2L+1)S}\le2C\,3^{(L+1)S}. \tag{16}
\]

For L≥2, `2^(2L+1)>3^(L+1)`: at L=2 this is 32>27, and increasing L
multiplies the ratio by 4/3. Equation (16) is impossible along S=L^t.
Thus **every word in this single-variable-column family excludes all rational
seeds**, including the two Phase 11 examples, with the same shift/tail closure.
This says nothing about arbitrary unequal-weight substitutions.
All these words are supercritical: `r0=L,r1=L-1,D=L+1` and
`3^L>2^(L+1)` for L≥2. The spectral iff rules out uniform contraction
throughout this family as well. The argument is a deduction from the earlier
complexity criterion, not a priority claim for a new family theorem.

The finite closed-language check in Appendix B found exactly 4*3^(k-1)
and 5*4^(k-1) factors at lengths 3^k and 4^k for k=1 through 6. The proof
of (15), rather than extrapolation of those counts, establishes the universal
claim. This route also reaches the length-six example whose particular
partial-return height ledger fails in the Phase 11 findings. That ledger
failure is a limitation of that proof, not evidence of rationality.

## 3. Independent spectral classification

Let `L≥2`, with `mu(1)` beginning at one, image weights `r0,r1`,
`Delta=r1-r0`, and `D=L-r1+r0=L-Delta>0`. The incidence matrix is
`[[L-r0,L-r1],[r0,r1]]`, whose characteristic polynomial is
`(X-L)(X-Delta)`. Image counts obey `W_(e+1)=r0 L^e+Delta W_e`, hence

\[
D W_e(b)=r0 L^e+\Delta^e(Db-r0). \tag{12}
\]

The same induction on a source window of length h gives
`D W(L^e a,L^e h)-r0 L^e h = Delta^e(D W(a,h)-r0 h)`.
Prolongability implies `r1≥1`; `D>0` implies `Delta<L`, and `r1≥1,r0≤L`
imply `Delta>-L`. Thus `|Delta|<L` without primitivity.

### 3.1 Necessity, including every shift and chunk size

Suppose every length-k aligned chunk beginning after t has count at most R.
Summing chunks and retaining the initial prefix gives
`W(k L^e)≤W(t)+R L^e`. Applying the source-window form of (12) yields

\[
(r0 k-DR)L^e\le D W(t)+|\Delta|^e |D W(k)-r0 k|. \tag{13}
\]

If `r0 k>DR`, its positive integer gap is at least one. Put
`B=max(1,|Delta|)<L`. The right of (13) is at most a fixed constant times
`B^e`, whereas `L^e/B^e` is unbounded by the binomial theorem. Contradiction.
Therefore every uniform cap satisfies **`r0*k≤D*R`**. This argument includes
the finite boundary t and does not replace a uniform premise by an average.

If k>0 and `3^R<2^k`, raise this strict inequality to D. In the supercritical
case `3^r0>2^D`, raising that inequality to k and using `r0 k≤DR` gives
`2^(Dk)<3^(r0 k)≤3^(DR)<2^(Dk)`, impossible.
Equality `3^r0=2^D` cannot occur for D≥1 because its sides are odd and even.
Thus contraction implies **`3^r0<2^D`**.

### 3.2 Sufficiency and an effective, nonminimal witness

Suppose `3^r0<2^D`. Choose positive d and natural s satisfying
`dr0<Ds` and `3^s<2^d`. One explicit construction is

```text
t = 3*3^r0 + 1
s = r0*t + 1
d = D*t
```

The integer base gap and Bernoulli show
`(2^D)^t≥4(3^r0)^t>3(3^r0)^t=3^s`; also `dr0<Ds`.
Set

```text
B = max(1, abs(Delta))
C = d*(D+r0) + D*d
e = B*C + 1
S = L^e
R = floor(s*S/d).
```

Since `1≤B<L`, Bernoulli gives `(C+1)B^e≤S`. From (12),
`D W_e(b)≤r0 S+(D+r0)B^e`. The integer margin `Ds-dr0≥1`, the last
bound, and `S≥(C+1)B^e` imply

\[
dD W_e(b)\le DsS-Dd\le Dd\lfloor sS/d\rfloor=DdR.
\]

The middle inequality is exactly the floor error; `dR≥sS-d` suffices.
Thus every selected aligned S-block has count at most R, including either
parent. Finally
`3^(dR)≤3^(sS)<2^(dS)` implies `3^R<2^S`.
The witness is finite and explicit, usually very large. Neither the Lean
statement nor this proof asserts a smallest level or an efficient search.

Together §§3.1–3.2 prove the exact iff claimed in PR #20, for the **selected
fixed point starting at one**, with all stated assumptions. They do not
classify nonuniform substitutions, all automatic words, or arbitrary words
in a substitution subshift. Rational exclusion additionally needs aperiodicity.

### 3.3 Degeneracies and hostile cases

| Case | Exact outcome |
|---|---|
| D=0 | Weight bounds force `r0=0,r1=L`; both images preserve their parent everywhere. The selected word is all ones and no positive chunk contracts. The ratio r0/D is undefined. |
| D<0 | Impossible since `r1≤L` and `r0≥0`. |
| Negative Delta | Included in (12) with its alternating sign. Its absolute value is strictly below L under the actual hypotheses. |
| Delta=-L | Would require `r1=0`, incompatible with prolongability on one. |
| Identical images / Delta=0 | The fixed word is periodic; positive power-image counts have no spectral transient. The iff still classifies contraction, not irrationality. |
| All-one selected word, D>0 | Possible when `r1=L,r0>0`; ratio r0/D=1, hence supercritical and no contraction. |
| All-zero / absent-one issue | An all-zero selected word is impossible because `w(0)=1`. Eventually zero is possible: `1->10,0->00`, with density zero, realized by -1/3 (one odd step reaches zero). |
| Nonprimitive, r0=0,r1<L | Density zero and subcritical, even though the word may be periodic or eventually periodic. No primitivity assumption is needed. |
| Only one occurring symbol | Covered. Count bounds do not assert both parents occur, and the selected all-one case agrees with the criterion. |
| k=0 in the necessary-cap lemma | Permitted and harmless; `r0*k≤D*R` is trivial. The contraction iff requires `1≤k`. |
| Critical threshold | `3^r0=2^D` is excluded exactly; no floating-point or logarithmic equality test is used. |

For a real-frequency interpretation, split any window into length-L^e blocks
plus at most two boundary pieces. Equation (12) bounds the interior error by
`O((|Delta|/L)^e)` times its length and the boundary error by `O(L^e)`.
First choose e, then let the window length grow. This gives uniform frequency
`r0/D` for every starting position. It is an H deduction, distinct from the
K integer iff and its finite amplification proof.

## 4. Validation and formal trust audit

The fresh validation clone had no `.lake` cache and used the pinned Lean
`leanprover/lean4:v4.18.0`. `lake-manifest.json` has no external packages.
The complete `bash research/phase11/validate.sh` exited **0** at the exact
PR head. It built 82 jobs, ran all 94 Rust tests, all required legacy and
Phase 11 Python verifiers, formatting/Clippy, manuscript static checks and
all 32 generated manuscript Lean-name checks. No PDF was built or claimed
ready; this task does not edit the manuscript.

A separate audit invocation, with `set -o pipefail`, piped
`lake env lean research/lean-audit/FamilyAudit.lean` through
`python3 research/lean-audit/check_axioms.py --expected-count 564` and exited
zero: **564 exact declarations, only approved standard foundations**.
The parser's two valid and eight adversarial cases passed. All 487 baseline
audit names remain in exact order; all 70 new theorems and seven new
definitions are explicitly audited. The only reported axioms are
`propext`, `Classical.choice`, `Quot.sound` (some declarations need fewer).
The forbidden-proof scan returned no matches.

`lake env lean research/phase11/Signatures.lean` also exited zero, printing all
21 interfaces. An earlier premature attempt during the fresh build failed
because the root `CollatzLab.olean` had not yet been built. It was rerun after
build completion and passed. This was sequencing, not a Lean proof failure.

Local evidence is in `/home/user/DEV/collatz-lab-phase11-evidence`:
`validate.log`, `axioms.log`, `signatures.log`, `adversarial.py`,
`adversarial.log`, and downloaded primary texts/metadata. The journal records
commands, checksums and final handoff. Build logs establish actual execution;
GitHub CI is separately identified and is not substituted for local evidence.

The independent Fraction-based checker imports no repository code. It checked
2047 binary offset blocks (lengths zero through ten), 36,800 signed actual
partial-return witnesses (including ell=0, overlaps, q divisible by three,
unreduced and negative-denominator cases), and 680 literal prolongable
substitutions of lengths two through five at levels zero through four.
It additionally checked both concrete return patterns and mandatory rational
controls. These are F evidence, not replacements for §§1–3.

## 5. Lean statement and semantic audit matrix

The exact source signatures for every principal declaration below are copied
in Appendix A, preserving implicit parameters, types, signs and quantifier
order. The namespace of each block is stated there. The table adds the
intended meaning and the independent check; it is not a replacement signature.
All rows marked PASS have H+K evidence unless specified otherwise.

| Declaration(s); exact signature in Appendix A | Intended proposition and independent proof check | Status / gap or hostile case |
|---|---|---|
| `matching_prefix_divisibility`, `square_prefix_divisibility` | Actual realization and a match of ell bits at m imply `2^(m+ell)` divides the specified closing form; §1.2 checks coprimality and offsets. | PASS; m=0/ell=0 are harmless, including overlaps. No nonperiodicity premise is needed for divisibility. |
| `prefixCycleForm_nonzero` | For m≥1, realization of a word that is not eventually periodic prevents the actual return `y_m=p`; §1.3. | PASS; all-one at -1 gives the minimal counterexample if the nonperiodicity safeguard is removed. m=0 always has E=0. |
| `prefixCycleForm_height` | For every Boolean v, every m,p,q with q≥0, `absInt E≤(absInt p+q)3^m`; §1.4. | PASS; q need not be odd for this algebraic bound. Negative q is not in this signature. |
| `offset_weight_upper`, `prefixCycleForm_weight_height` | The exact fixed-weight offset cap (4) and the safe height bound (5). | PASS; `m-weight` is nonnegative. Offset sharpness does not assert sharpness of the whole triangle bound. |
| `rational_matching_prefix_weight_bound`, `rational_matching_prefix_bound`, `rational_square_prefix_bound` | Positive m, actual infinite realization, independent nonperiodicity and the finite match yield (6), its crude counterpart, and (7). | PASS; C is fixed by the same p,q in all uses. Finite prefix witnesses do not discharge infinite realization. |
| `no_rational_seed_unbounded_square_prefix` | For every K there is a positive square half-length m≥K; this and non-eventual-periodicity exclude each p,q. | PASS; no hidden density, equal-weight or contraction premise. Unboundedness is essential to this proof; omitting it leaves an open stronger assertion, not a known false one. |
| `word_power_congr`, `initial_double_square`, `no_rational_seed_morphism_initial_double` | L≥2, prolongability on one, the selected second letter true and independent nonperiodicity produce the unbounded squares. | PASS; the selected fixed point starts at one. Neither unequal weights alone nor distinct images alone is the hypothesis. |
| `nonContracting_images`, `nonContracting_columns`, `nonContracting_not_eventually_periodic` | Literal 110/111 orientation, correct complement column two, and independent eventual aperiodicity. | PASS; §2.1 also gives an independent valuation proof. No use of the exclusion theorem in aperiodicity. |
| `nonContracting_group_expands`, `nonContracting_no_uniform_chunks` | All positive complete-image groups expand; more strongly, no cap with a strict contraction gap for any t,k>0. | PASS; the three-chunk proof covers unaligned starts and all fixed k, rather than a bounded search. |
| `nonContracting_prefix_discrepancy`, `nonContracting_power_count` | The integer all-prefix error and signed power-count formula. | PASS for integers; the ordinary limit 3/4 is H only. The count formula does not assume both parent letters occur at each level. |
| `nonContracting_variable_cocycle` | Actual image-selected multipliers are 9 and 27, with offsets 5 and 19. | PASS; no equal-weight replacement of the actual dynamics. |
| `no_rational_seed_realizes_nonContracting110111`, its shifted and signed eventual-tail theorems | Universal p,q exclusion plus all t and all independent s,t; §2.3. | PASS; negative q coverage comes from the raw signed-tail result, not a vacuous negative-q `RealizesWord`. |
| `nonContracting1011_images`, `nonContracting1011_columns`, `nonContracting1011_not_eventually_periodic` | Literal 1011/1111, complement at index one, independent aperiodicity. | PASS; §2.2 supplies a different valuation proof and both bits occur. |
| `nonContracting1011_partial_return`, `nonContracting1011_prefix_weight` | For each k, return length 4^k at 2*4^k and `abs(5W(2S)-8S)≤3`; §2.2. | PASS; the exact signed error is `-3(-1)^k`. This is not a false claim that the initial-double hypothesis holds. |
| `nonContracting1011_no_uniform_chunks` | All shifts and positive fixed chunk sizes fail contraction because 81>32. | PASS by §3.1; no hypothesis of rational realization. |
| `no_rational_seed_realizes_nonContracting1011`, shifted and signed eventual-tail forms | Return inequality plus the exact base gap 8192>6561 and all tail/sign closures. | PASS; equation (11) checks each exponent and the constant 216. |
| `power_image_count`, `prolongable_spectral_gap` | Exact count (12) and `abs Delta<L` from prolongability and D>0. | PASS; Delta=-L is excluded by `r1≥1`, not by an unstated primitivity assumption. |
| `uniform_chunks_frequency_necessary` | Every shifted uniform cap has `r0*k≤D*R`, including the initial t boundary. | PASS; equation (13) reconstructs the integer-gap argument. This theorem itself allows k=0. |
| `exists_power_ratio_bound`, `subcritical_has_contracting_power` | An explicit rational slope, spectral gap and floor margin yield a finite aligned power-block cap. | PASS; §3.2 checks the witness. No minimality or efficient-runtime guarantee is exported. |
| `uniform_contraction_iff_subcritical` | Exactly the existential t,k,R proposition, with k≥1, is equivalent to `3^r0<2^d`, under explicit `D=d≥1`. | PASS; no aperiodicity hypothesis and no rational-exclusion conclusion. |
| `frequencyDen_zero_word` | D=0 makes the selected word identically true. | PASS; no division by zero or limiting frequency is claimed in this case. |
| Literal check declarations and two rational controls | Ordinary `decide` checks finite lists/numerator states; alternating and all-one are infinite rational controls. | K+F for finite checks; H+K for the two controls. No finite integer witness is described as an infinite realization of an excluded word. |

The actual semantic definitions in `Word.lean:297–314` are:

```lean
def numStep (q p : Int) : Int :=
  if p % 2 = 0 then p / 2 else (3 * p + q) / 2
def numIter (q p : Int) : Nat → Int
  | 0 => p
  | j + 1 => numStep q (numIter q p j)
def seedParity (q p : Int) (j : Nat) : Int := (numIter q p j) % 2
def RealizesWord (p q : Int) (v : Nat → Int) : Prop :=
  q > 0 ∧ q % 2 = 1 ∧ ∀ j : Nat, seedParity q p j = v j
```

The argument order `RealizesWord p q` versus `seedParity q p` was checked.
`numStep_eq`, `numIter_equiv`, `repeated_numIter_periodic`,
`numIter_add`, `realizes_shiftWord_pred` and the signed normalization proofs
were read as part of the dependency audit. The fuel-based word definition is
connected to literal substitution by `word_block` and `word_unique`; it is
not defined by assuming a rational itinerary. `family_ring` only expands
integer algebra and calls `omega`; ordinary `decide` is kernel reduction.
The imported older Mahler proofs introduce no new axioms into these arguments.
There is no general rational-periodicity assumption in this dependency chain.

## 6. Primary-source comparison and priority

The search covered Collatz conjugacy, rational parity coding, repeated
prefixes, periodic approximants, low factor complexity, p-adic stammering,
Mahler values and uniform substitutions, including 2026 deposits. Records
were inspected on 14 November 2026. “Known” below specifies whether the source
is a published journal article or an unrefereed preprint; it does not imply
journal acceptance of Phase 11 or of another 2026 manuscript.

The decisive exact overlap is Allikvere's July preprint. Its
`s,h,L,B_V,D_V,a,b` are our `m,r,m+ell,c,3^r-2^m,p,q`, so its cross product
is `-E_m`. Its Theorem 2.3 is precisely (6) after cancellation, and its
Corollary 3.2 is the universal square exclusion. Both signs are covered.
The elementary proofs were checked. In the height proof, a displayed
single-summand geometric rewrite reverses an index; the sum and claimed
bound remain correct, as independently derived in (4). No stronger
transcendence claim is needed for this priority conclusion. [Original
record and downloadable PDF/TeX](https://doi.org/10.5281/zenodo.21543841).

| Primary source, stable identifier and location | Actual hypotheses / conclusion; portions read | Exact relation and priority classification |
|---|---|---|
| D. J. Bernstein, *A non-iterative 2-adic statement of the 3N+1 conjecture*, Proc. AMS **121** (1994), 405–408, DOI [10.2307/2160415](https://doi.org/10.2307/2160415); [author text](https://cr.yp.to/papers/231.pdf), Theorem 1 and Corollary 1, pp. 2–3 of that text | Read the series construction, bijectivity, conjugacy proof and eventual-periodic-to-rational consequence. Theorem 1 uses an ordinary-step C/H convention; the inverse-parity series is the same. | **Known foundation**, not a universal nonperiodic-to-irrational theorem. Confirms periodic rational controls and the direction of the open conjecture. |
| D. J. Bernstein and J. C. Lagarias, *The 3x+1 conjugacy map*, Canad. J. Math. **48** (1996), 1154–1169, DOI [10.4153/CJM-1996-060-x](https://doi.org/10.4153/CJM-1996-060-x); [author PDF](https://websites.umich.edu/~lagarias/doc/bernstein.pdf), §1 equations (1.5)–(1.6), Appendix A, Corollary A.3 | Read the parity-map definition, inverse series, solenoidal bijection/isometry proof and Periodicity Conjecture statement. Matches the shortcut T exactly. | **Known**: equal n-bit parity prefixes mean equal seed residues modulo 2^n. The congruence machinery is classical; the conjectured reverse preservation of rationality is not a theorem. |
| L. Halbeisen and N. Hungerbühler, *Optimal bounds for the length of rational Collatz cycles*, Acta Arith. **78** (1997), 227–239, DOI [10.4064/aa-78-3-227-239](https://doi.org/10.4064/aa-78-3-227-239); [author PDF](https://math.ch/norbert.hungerbuehler/publications/Optimal_bounds_for_the_length_of_rational_Collatz_cycles.pdf), §2, Lemmas 1–2, pp. 228–229 | Read the rational domain, offset recurrence, concatenation formula, affine iterate and rational-cycle formula with proof (also in the earlier author typescript). | **Known** affine and periodic-approximant arithmetic. The paper's cycle bounds do not by themselves give all nonperiodic square exclusions. |
| K. G. Monks and J. Yazinski, *The autoconjugacy of the 3x+1 function*, Discrete Math. **275** (2004), 219–236, DOI [10.1016/S0012-365X(03)00125-0](https://doi.org/10.1016/S0012-365X(03)00125-0); [author PDF](https://monks.scranton.edu/files/pubs/AutoConjV13.pdf), Theorem 2.7(b), PDF p. 6; Lemmas 3.2, 3.4, §4.1, pp. 8–11 | Read the statement and relevant complete proof. Every infinite rational odd-denominator orbit has lower odd density at least log(2)/log(3), including negative rational starts. | **Known** subcritical exclusion once nonperiodicity is supplied. Gives no contradiction at densities 3/4 or 4/5. It is not the exact fixed-chunk spectral iff. |
| A. Dubickas, *On integer sequences generated by linear maps*, Glasgow Math. J. **51** (2009), 243–252, DOI [10.1017/S0017089508004655](https://doi.org/10.1017/S0017089508004655); [publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/C40C0C07FEC20797475BB2899C436C9A/S0017089508004655a.pdf/on_integer_sequences_generated_by_linear_maps.pdf), Theorem 5, p. 246; proof §5, pp. 249–250 | Read the exact positive-integer escape premise and full proof: equal factors force a power-of-two state difference; growth gives `liminf P(n)/n≥log(2)/log(3/2)`. | **Known published mechanism**. The signed-rational extension and factor bound are proved in §2.4 here, rather than silently attributed to his literal statement. Both examples are direct corollaries of that extension. |
| B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer bases*, Ann. Math. **165** (2007), 547–565, DOI [10.4007/annals.2007.165.547](https://doi.org/10.4007/annals.2007.165.547); [author PDF](https://adamczewski.perso.math.cnrs.fr/ComplexityI.pdf), §4 Condition (*) and §6 Theorem 6, pp. 561–562 | Read the stammering condition, p-adic theorem and proof outline using Schlickewei. It applies to actual Hensel digits of a p-adic number, with bounded preperiod/period ratio and exponent >1. | **Known method; direct applicability mismatch**. Parity letters are digits of the parity vector, not generally the Hensel digits of its Collatz seed. It does not directly imply the Phase 11 claims by calling the word automatic. |
| J. López and P. Stoll, *The 3x+1 conjugacy map over a Sturmian word*, Integers **9** (2009), A13, 141–162, DOI [10.1515/integ.2009.014](https://doi.org/10.1515/integ.2009.014); [journal PDF](https://math.colgate.edu/~integers/j13/j13.pdf), Theorem 1 and Corollary 2, pp. 143–144, §4 | Read the introduction, principal continued-fraction/series formulas, and the distinction between real and 2-adic evaluations in the examples/§4. | **Known structured-word approximants**, with irrational-slope mechanical words rather than these rational-frequency uniform fixed points. It does not supply a checked exclusion of the two examples. |
| J. López and P. Stoll, *The 3x+1 Periodicity Conjecture in R*, [arXiv:2101.12747v1](https://arxiv.org/html/2101.12747v1), 29 January 2021, Theorem 1, §2 equations (15)–(16), §6 | Read the exact density claim, the transfer at (15)–(16), and its use in the proof. It would exclude both supercritical nonperiodic examples. | **Undetermined claim with a concrete proof gap**: a real irrational limit of rational sums need not force their 2-adic limit irrational. It is not a verified stronger theorem from which Phase 11 may be deduced. See the counterargument below. |
| O. Rozier and C. Terracol, *Paradoxical behavior in Collatz sequences*, [arXiv:2502.00948v5](https://arxiv.org/html/2502.00948v5), 17 May 2026, Theorem 2.4 and proof, §2 | Read the ordering argument and sharp remainder extrema. Their remainder is c/2^m, and its maximum at fixed r is `(3^r-2^r)/2^r`, attained by zeros followed by ones. | **Known exact offset bound** (4), expressed in different normalization. The positive-integer formulation covers every binary block through finite parity compatibility; the cap itself is combinatorial and sign independent. No journal status is inferred from its acknowledgements. |
| S. M. Molchanov, *On the p-adic transcendence measure of the values of functions satisfying some functional equations*, Vestnik Moskov. Univ. Ser. I Mat. Mekh. (1983), no. 2, 31–37; [Math-Net primary scan/record](https://www.mathnet.ru/eng/vmumm3467), unnumbered theorem, pp. 31–32 | Read original Russian OCR of the hypotheses and the auxiliary-proof outline, not only the abstract. It requires a transcendental analytic f over the completed algebraic p-adic field, a fractional-linear Mahler relation, a nonnegative monomial matrix with the stated irreducible dominant-root hypothesis, algebraic coordinates with p-adic norms strictly between zero and one, and nonvanishing denominator along the orbit. | **Known p-adic Mahler theorem; applicability to these unequal-weight seeds undetermined.** No validated scalar specialization/nonrationality reduction is supplied here. Full proof and the displayed numerical measure were not checked line by line; scan images/download attempts failed. Preserve the separate Phase 9 equal-weight discussion without importing its conclusion here. |
| Y. Bugeaud and J.-Y. Yao, *Hankel determinants, Padé approximations, and irrationality exponents for p-adic numbers*, Ann. Mat. Pura Appl. **196** (2017), 929–946, DOI [10.1007/s10231-016-0602-7](https://doi.org/10.1007/s10231-016-0602-7); [author PDF](https://irma.math.unistra.fr/~bugeaud/travaux/p-adic18.pdf), Theorem 3.1, PDF pp. 6–7 | Read statement, nonvanishing/Hankel assumptions, and opening transcendence deduction. Points are `b=p^w`, f has integral coefficients and an order-one scalar Mahler equation. | **Known related results; no direct implication established.** An automatic parity word alone supplies none of the required seed specialization/Hankel hypotheses. Their cited Wang–Xu (2006) source was not obtained or treated as independently checked. |
| J. Allikvere, *Periodic shadows, drift pressure, and transcendence of the 3x+1 conjugacy map*, [Zenodo 21543841](https://doi.org/10.5281/zenodo.21543841), created 25 July 2026, updated 13 August 2026 | Lemma 2.1 / Theorem 2.3, pp. 2–3, and Corollary 3.2 checked above. Section 5, Theorem 5.3 and Corollary 5.5, statement and main argument inspected. | **Known prior-preprint criterion and square theorem.** The stronger transcendence extension is not assumed in the review verdict. No journal peer review verified. |
| B. Pham, *Landmark Resolution Strategies and a Pointwise Collatz Advance*, dated 22 July 2026, [pinned author note](https://github.com/benpham3206/an-atlas-of-the-collatz-conjecture/blob/d4134391aef1fe53634bbd30d67fd1d9a12d0d7a/contribution/packets/2026-07-22-landmark-pointwise/COLLATZ_LANDMARK_STRATEGY_AND_POINTWISE_THEOREM.md), Parts III–V, Lemmas 1–2, Theorem 3, Corollaries 4–5 | Read numerator collision and growth proofs, pressure bound and universal complexity consequence. Rational numerators may be signed. Corollary 4 literally states **limsup**, not liminf. | **Known earlier preprint extension of the collision method**; the precise liminf result used here is explicitly proved in §2.4 and also stated in De Jesús §9. No first-discovery adjudication is made between these authors. |
| E. Cassidy, *Transversality foundry: the divergence target is Lagarias's Periodicity Conjecture…*, dated 22 September 2026, [pinned author note](https://github.com/eliottcassidy2000/math/blob/6b805eed1613edaedd87965e2b1986390fa84f0e/05-knowledge/results/collatz_procgen_20260922_transversality_foundry.md), §4.3 Lemma G, Theorem R, second route after Theorem S | Read the actual general affine 2-adic map, periodic approximant and proof of the repetition criterion. For a word not eventually periodic, unbounded common-prefix precision minus log height excludes rational values of either sign. | **Known earlier preprint framework**, not merely a Sturmian analogy. Empty preperiod plus the general offset cap yields the square theorem. No human/journal review is established by the repository note. |
| E. De Jesús, *The 3x+1 Conjugacy Map Sends Every Sturmian Word to an Irrational 2-adic Integer*, [Zenodo 23108370](https://doi.org/10.5281/zenodo.23108370), file `sturmian_irrationality_v3.pdf`; [SSRN DOI](https://doi.org/10.2139/ssrn.7662483), manuscript date 23 September 2026, Zenodo creation 2 October, updated 8 November | Full PDF obtained; read §§4–6, §9 Lemma 9.1 / Proposition 9.2 / Corollary 9.3, pp. 13–14, and §10 initial-square proof, pp. 14–16. In particular Corollary 9.3 treats arbitrary non-eventually-periodic words of lower complexity ratio below 1/log2(3/2), with signed rational seed. | **Known stronger preprint exclusion criterion**: together with (15), it directly covers both examples and the larger family. Its Sturmian-specific main result need not be misapplied to rational-frequency words. No formal-verification or journal-acceptance claim is inferred. |
| E. De Jesús, *Transcendence of the 3x+1 conjugacy map on Sturmian words*, [hexagon:2611.00108v2](https://hexagonmath.org/2611.00108v2), November 2026, PDF pp. 1–4, §§2–3 and §8.3 | Read scope, isometry/height setup, the characteristic-word repetition/Ridout argument and prior-work discussion. The main characteristic/shift-orbit slope range is below `(3+sqrt(5))/(4 log2(3))`; arbitrary intercepts are not silently included. | **Known related preprint method**, not an immediate theorem about these two substitutions. Its bibliography led to the actual earlier general criteria; a restricted Sturmian theorem alone would not settle Phase 11. Its Lean component assumes an external Ridout theorem and is not an audit of PR #20. |
| `lyapunov_weaver`, *Automatic parity and primitive substitutions in rational Collatz dynamics*, [rStation paper 16 v2](https://rstation.ai/problems/collatz/papers/16/v2), 22 October 2026; *Automatic, primitive, and nonprimitive parity in rational Collatz dynamics*, [v3](https://rstation.ai/problems/collatz/papers/16), 27 October 2026 | Read Theorems 1, 1c–1f and finite-modification scope, v2 §§3–10 local coherence/specialization argument, and v3's added nonprimitive statements and interfaces. The main consumer is a **positive** rational orbit with automatic or specified substitutive parity. | **Undetermined stronger claimed overlap**, sufficient for the positive-seed halves if sound; not a checked theorem for both numerator signs. The long analytic lifting/regularity argument was not fully independently certified. “Accepted” means rStation platform review, not verified journal publication. PR #20 needs none of it. |
| J. P. Bell, *The upper density of an automatic set is rational*, J. Théor. Nombres Bordeaux **32** (2020), 585–604, DOI [10.5802/jtnb.1135](https://doi.org/10.5802/jtnb.1135); [journal PDF](https://numdam.org/item/10.5802/jtnb.1135.pdf), Corollary 1.2 and Proposition 2.1, pp. 587–590 | Read the rational effective density result and spectral decomposition proof of Proposition 2.1. General automatic sets may lack an ordinary density; their power-prefix errors have effective subdominant spectral bounds after a suitable power. | **Known spectral background**. It does not state this exact binary shifted contraction iff. The latter is a direct elementary consequence of the special two-dimensional count recurrence and uniform boundary control (§3); priority of that exact formulation is **undetermined**, not established new. |

### 6.1 Why the López–Stoll 2021 transfer is not a usable theorem

Their equations (15)–(16) construct compatible residues of rational partial
sums. Convergence of those sums in the real norm does not identify the real
limit with their 2-adic limit. For a putative rational seed x and affine
prefix with count r and offset c, the exact rational identity is

\[
x-(-c/3^r)=(2^m/3^r)T^m(x).
\]

Even when the left partial sums have a real limit and `2^m/3^r→0` in R,
that right side need not tend to zero: the hypothetical rational orbit can
escape. This is precisely the case the transfer must rule out, not a
justification for discarding it. No counterexample to their full conjectured
density conclusion is asserted. PR #20's integer arguments avoid this step.
[Original equations and proof](https://arxiv.org/html/2101.12747v1#S2).

### 6.2 Claim-by-claim originality judgment

| Phase 11 item | Referee judgment |
|---|---|
| Affine numerator recurrence; parity precision; deterministic nonzero step | Classical mechanisms, faithfully kernel formalized. |
| Arbitrarily long initial squares exclude rational seeds, irrespective of density | **Known prior-preprint theorem**, exact overlap with Allikvere; also a direct instance of Cassidy's criterion. A new formalization/independent proof is plausible, not a new mathematical statement. |
| Sharp fixed-weight offset cap and partial-return inequality | **Known** bound (Rozier–Terracol and Allikvere); the full signed inequality is already in Allikvere's Theorem 2.3. The Lean integer formulation is independently useful. |
| Concrete 110/111 and 1011/1111 rational exclusions | **Corollaries of earlier general criteria**. In addition to periodic approximation, De Jesús Corollary 9.3 plus (15), using the published Dubickas mechanism, covers both. Exact earlier named instantiations were not located; that does not make these new exclusion theorems. |
| Either numerator sign, either odd-denominator sign; unreduced pairs | Present in the earlier general rational criteria or immediate representation invariance. **Not an independently novel strengthening** of those criteria. |
| Arbitrary finite shifts/eventual shifted tails | Elementary rational closure under inverse and forward branches; an auditable formal corollary, not evidence of priority. |
| Spectral count identity and 3/4 frequency | Standard incidence arithmetic and an elementary all-prefix estimate. Possible formalization contribution. |
| Exact contraction iff, with D=0, nonprimitive cases, every shift and explicit witness | Sound and useful **formal classification of a sufficient-method boundary**. Exact priority **undetermined**; §3 shows why its mathematical proof is routine from the known count recurrence, rather than a new general irrationality principle. No minimal level is proved. |
| Transcendence or general rational Periodicity Conjecture | Not a Phase 11 Lean result. Stronger preprint claims and digit-based published theorems must keep their separate hypotheses and trust status. |

### 6.3 Access limits and provenance

SSRN HTML for 7662483 refused access. The full v3 text was obtained instead
from its public Zenodo record API, not inferred from its abstract. Zenodo HTML
and DOI navigation also failed in the web tool, but the public API returned
metadata and the complete Allikvere PDF/TeX and De Jesús PDF. Local checksums
are recorded in the journal. Cassidy and Pham were read at exact Git commits,
not moving default branches. rStation v2 and v3 were both obtained, so the
review does not mistake the earlier v2 for the latest version.

Molchanov's original OCR was readable, but PDF image retrieval repeatedly
redirected to the metadata page and direct download returned HTTP 403. The
scan's displayed numerical measure and proof details are not independently
certified here. Wang/Wang–Xu and the general Loxton–van der Poorten sources
were not read in full; no claim of direct Phase 11 implication is based on
them. No MathSciNet/zbMATH completeness claim is made. Search failure is never
used as evidence of novelty.

## 7. Merge decision, publication decision and next task

**Merge: revise the documentation, then merge as formal research if the owner
authorizes.** All four principal mathematical claims pass the independent
reconstruction and local formal/semantic checks. No proof repair is demanded.
Before merge, correct M1 and record P1's exact earlier results. Refresh the
pinned-head comparison and rerun relevant checks if the proof branch changes.
A change to a head SHA or to shared audit/CI files requires fresh validation;
this report approves no unseen future revision. Green CI is not merge approval.

**Separate new-result publication: not justified on this evidence.** The main
exclusion criteria and signed scope have direct earlier statements; both
examples even follow a published counting mechanism via an elementary
extension. The spectral iff is mathematically clean but too close to its
incidence recurrence to carry a substantial new-theorem claim without a
more specific comparison and contribution. A distinct Phase 11 **formalization
or research note** could be worthwhile if it openly leads with prior results,
explains the exact Lean trust/semantic work and the effective boundary theorem,
and is reviewed by a human mathematical author/referee. That is a conditional
editorial possibility, not a recommendation to submit now.

Keep this material separate from the Phase 9 equal-weight manuscript. Its
mechanism and review status differ, and adding it would not restore the old
novelty claim. No manuscript, author identity, disclosure, journal submission,
preprint upload, announcement or journal/referee contact has been made in this task.
The owner still decides whether to authorize PR #20's merge and whether to
commission any separate note.

The recommended next task is narrowly defined: update the Phase 11 findings
with the exact prior-art correspondence and M1 correction, then have a human
mathematician review the claims and the choice between a formalization note
and no separate paper. If more formal research is wanted, §2.4 identifies a
broader, already methodologically covered single-variable-column family; it
must not be presented as solving the global conjecture.

Issue #19, PR #20 and issue #15 remain open; the review PR itself is a separate,
unmerged documentation artifact. A PASS mathematical audit is not permission
to merge either PR or to publish a manuscript.

## Appendix A. Exact source signature inventory

These are the 77 new public declaration signatures at the audited SHA,
including helper and finite-check interfaces. Proof/definition bodies are
omitted. Unqualified names resolve in the indicated original namespace, with
its original imports and `open Morphism` in scope where used; this is a type
inventory, not a standalone executable Lean file. In particular powers marked
`(2 : Int)` or `(3 : Int)` remain integer powers. The canonical source links
are pinned, and the separate elaborated 21-interface output also passed.


### NonContracting110111.lean

[Pinned source](https://github.com/hipotures/collatz-lab/blob/d270b4466794badc49da6feebefeda77f5793e16/CollatzLab/NonContracting110111.lean).


Original namespace: `CollatzLab.Morphism`.

```lean
-- Source line 7: CollatzLab.Morphism.nonContracting110111
def nonContracting110111 : Images 3

-- Source line 11: CollatzLab.Morphism.nonContracting_images
theorem nonContracting_images :
    List.ofFn nonContracting110111.one = [true, true, false] ∧
    List.ofFn nonContracting110111.zero = [true, true, true] ∧
    image nonContracting110111 true 0 = true ∧
    weight (image nonContracting110111 true) 3 = 2 ∧
    weight (image nonContracting110111 false) 3 = 3

-- Source line 18: CollatzLab.Morphism.nonContracting_columns
theorem nonContracting_columns (n : Nat) :
    word nonContracting110111 (3 * n) = true ∧
    word nonContracting110111 (3 * n + 1) = true ∧
    word nonContracting110111 (3 * n + 2) = !(word nonContracting110111 n)

-- Source line 30: CollatzLab.Morphism.nonContracting_parity_columns
theorem nonContracting_parity_columns (n : Nat) :
    parityWord nonContracting110111 (3 * n) = 1 ∧
    parityWord nonContracting110111 (3 * n + 1) = 1 ∧
    parityWord nonContracting110111 (3 * n + 2) = 1 - parityWord nonContracting110111 n

-- Source line 38: CollatzLab.Morphism.nonContracting_both_bits
theorem nonContracting_both_bits :
    word nonContracting110111 0 = true ∧ word nonContracting110111 2 = false

-- Source line 43: CollatzLab.Morphism.nonContracting_not_periodic_from
theorem nonContracting_not_periodic_from (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → parityWord nonContracting110111 (n + p) =
      parityWord nonContracting110111 n) → False

-- Source line 70: CollatzLab.Morphism.nonContracting_not_eventually_periodic
theorem nonContracting_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord nonContracting110111)

-- Source line 75: CollatzLab.Morphism.nonContracting_group_weight
theorem nonContracting_group_weight (a h : Nat) :
    2 * h ≤ weight (fun j => word nonContracting110111 (3 * a + j)) (3 * h)

-- Source line 85: CollatzLab.Morphism.nonContracting_three_weight
theorem nonContracting_three_weight (a : Nat) :
    2 ≤ weight (fun j => word nonContracting110111 (a + j)) 3

-- Source line 107: CollatzLab.Morphism.nonContracting_window_lower
theorem nonContracting_window_lower (a : Nat) : ∀ h,
    2 * h ≤ weight (fun j => word nonContracting110111 (a + j)) (3 * h)

-- Source line 120: CollatzLab.Morphism.nonContracting_group_expands
theorem nonContracting_group_expands (h R : Nat) (hh : 1 ≤ h) (hR : 2 * h ≤ R) :
    (2 : Int) ^ (3 * h) < (3 : Int) ^ R

-- Source line 131: CollatzLab.Morphism.nonContracting_no_uniform_chunks
theorem nonContracting_no_uniform_chunks (t k R : Nat) (hk : 1 ≤ k)
    (hw : ∀ n, weight (fun j => word nonContracting110111 (t + k * n + j)) k ≤ R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ k

-- Source line 165: CollatzLab.Morphism.nonContracting_power_count
theorem nonContracting_power_count (k a : Nat) :
    4 * (weight (fun j => word nonContracting110111 (3 ^ k * a + j)) (3 ^ k) : Int) =
      3 * (3 ^ k : Nat) + (-1 : Int) ^ k *
        (4 * bit (word nonContracting110111 a) - 3)

-- Source line 181: CollatzLab.Morphism.nonContracting_prefix_step
theorem nonContracting_prefix_step (n r : Nat) (hr : r < 3) :
    weight (word nonContracting110111) (3 * n + r) +
      weight (word nonContracting110111) n = 3 * n + r

-- Source line 201: CollatzLab.Morphism.nonContracting_prefix_discrepancy
theorem nonContracting_prefix_discrepancy : ∀ (k n : Nat), n < 3 ^ k →
    -2 * (k : Int) ≤ 4 * (weight (word nonContracting110111) n : Int) - 3 * (n : Int) ∧
    4 * (weight (word nonContracting110111) n : Int) - 3 * (n : Int) ≤ 2 * (k : Int)

-- Source line 224: CollatzLab.Morphism.nonContracting_nine_prefix_height
theorem nonContracting_nine_prefix_height (n j : Nat) (hj : j < 9) :
    weight (word nonContracting110111) (9 * n + j) =
      6 * n + weight (word nonContracting110111) n + 2 * (j / 3) + j % 3

```


### NonContractingChecks.lean

[Pinned source](https://github.com/hipotures/collatz-lab/blob/d270b4466794badc49da6feebefeda77f5793e16/CollatzLab/NonContractingChecks.lean).


Original namespace: `CollatzLab.NonContractingChecks`.

```lean
-- Source line 8: CollatzLab.NonContractingChecks.literalStep
def literalStep (xs : List Int) : List Int

-- Source line 11: CollatzLab.NonContractingChecks.literalIter
def literalIter : Nat → List Int

-- Source line 17: CollatzLab.NonContractingChecks.literal_semantics
theorem literal_semantics :
    literalIter 2 = [1,1,0,1,1,0,1,1,1] ∧
    (List.range 3).map (parityWord nonContracting110111) = literalIter 1 ∧
    (List.range 9).map (parityWord nonContracting110111) = literalIter 2 ∧
    (List.range 27).map (parityWord nonContracting110111) = literalIter 3 ∧
    (List.range 81).map (parityWord nonContracting110111) = literalIter 4

-- Source line 24: CollatzLab.NonContractingChecks.rational_control_preserved
theorem rational_control_preserved : RealizesWord 1 1 (parityWord unequalAlternating)

-- Source line 34: CollatzLab.NonContractingChecks.signed_finite_semantics
theorem signed_finite_semantics :
    (List.range 81).map (seedParity 1 721013141537229946329339) = literalIter 4 ∧
    numIter 1 721013141537229946329339 81 = 37923644741691456159576389081 ∧
    (List.range 81).map (seedParity 5 (-1230637570772366967178009)) = literalIter 4 ∧
    numIter 5 (-1230637570772366967178009) 81 = -64728725942839940287884653801 ∧
    (List.range 81).map (seedParity 15 (-3691912712317100901534027)) = literalIter 4

-- Source line 47: CollatzLab.NonContractingChecks.all_one_rational_control
theorem all_one_rational_control : RealizesWord (-1) 1 (fun _ => 1) ∧
    EventuallyPeriodic (fun _ => 1)

```


### RepeatedPrefix.lean

[Pinned source](https://github.com/hipotures/collatz-lab/blob/d270b4466794badc49da6feebefeda77f5793e16/CollatzLab/RepeatedPrefix.lean).


Original namespace: `CollatzLab`.

```lean
-- Source line 8: CollatzLab.prefixCycleForm
def prefixCycleForm (v : Nat → Bool) (m : Nat) (p q : Int) : Int

-- Source line 13: CollatzLab.matching_prefix_divisibility
theorem matching_prefix_divisibility (v : Nat → Bool) (m ell : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (hmatch : ∀ j, j < ell → v (m + j) = v j) :
    (2 : Int) ^ (m + ell) ∣ prefixCycleForm v m p q

-- Source line 39: CollatzLab.square_prefix_divisibility
theorem square_prefix_divisibility (v : Nat → Bool) (m : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (hsquare : ∀ j, j < m → v (m + j) = v j) :
    (2 : Int) ^ (m + m) ∣ prefixCycleForm v m p q

-- Source line 46: CollatzLab.prefixCycleForm_nonzero
theorem prefixCycleForm_nonzero (v : Nat → Bool) (m : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j))) :
    prefixCycleForm v m p q ≠ 0

-- Source line 65: CollatzLab.prefixCycleForm_height
theorem prefixCycleForm_height (v : Nat → Bool) (m : Nat) (p q : Int) (hq : 0 ≤ q) :
    absInt (prefixCycleForm v m p q) ≤ (absInt p + q) * (3 : Int) ^ m

-- Source line 86: CollatzLab.offset_weight_upper
theorem offset_weight_upper (v : Nat → Bool) : ∀ m,
    offset v m ≤ (2 : Int) ^ (m - weight v m) * (3 : Int) ^ weight v m - (2 : Int) ^ m

-- Source line 105: CollatzLab.prefixCycleForm_weight_height
theorem prefixCycleForm_weight_height (v : Nat → Bool) (m : Nat) (p q : Int) (hq : 0 ≤ q) :
    absInt (prefixCycleForm v m p q) ≤
      (absInt p + q) * ((2 : Int) ^ (m - weight v m) * (3 : Int) ^ weight v m)

-- Source line 133: CollatzLab.rational_matching_prefix_weight_bound
theorem rational_matching_prefix_weight_bound (v : Nat → Bool) (m ell : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j)))
    (hmatch : ∀ j, j < ell → v (m + j) = v j) :
    (2 : Int) ^ (ell + weight v m) ≤ (absInt p + q) * (3 : Int) ^ weight v m

-- Source line 159: CollatzLab.rational_matching_prefix_bound
theorem rational_matching_prefix_bound (v : Nat → Bool) (m ell : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j)))
    (hmatch : ∀ j, j < ell → v (m + j) = v j) :
    (2 : Int) ^ (m + ell) ≤ (absInt p + q) * (3 : Int) ^ m

-- Source line 177: CollatzLab.rational_square_prefix_bound
theorem rational_square_prefix_bound (v : Nat → Bool) (m : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j)))
    (hsquare : ∀ j, j < m → v (m + j) = v j) :
    (4 : Int) ^ m ≤ (absInt p + q) * (3 : Int) ^ m

-- Source line 189: CollatzLab.no_rational_seed_unbounded_square_prefix
theorem no_rational_seed_unbounded_square_prefix (v : Nat → Bool)
    (hsquares : ∀ K : Nat, ∃ m : Nat, K ≤ m ∧ 1 ≤ m ∧
      ∀ j, j < m → v (m + j) = v j)
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j))) (p q : Int) :
    ¬ RealizesWord p q (fun j => bit (v j))

```


Original namespace: `CollatzLab.Morphism`.

```lean
-- Source line 215: CollatzLab.Morphism.word_power_congr
theorem word_power_congr {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) : ∀ k a b,
    word M a = word M b → ∀ j, j < L ^ k →
    word M (L ^ k * a + j) = word M (L ^ k * b + j)

-- Source line 238: CollatzLab.Morphism.initial_double_square
theorem initial_double_square {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hdouble : word M 1 = true) (k j : Nat)
    (hj : j < L ^ k) : word M (L ^ k + j) = word M j

```


Original namespace: `CollatzLab`.

```lean
-- Source line 250: CollatzLab.no_rational_seed_morphism_initial_double
theorem no_rational_seed_morphism_initial_double {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true) (hdouble : Morphism.word M 1 = true)
    (haper : ¬ EventuallyPeriodic (Morphism.parityWord M)) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord M)

```


### NonContractingExclusion.lean

[Pinned source](https://github.com/hipotures/collatz-lab/blob/d270b4466794badc49da6feebefeda77f5793e16/CollatzLab/NonContractingExclusion.lean).


Original namespace: `CollatzLab`.

```lean
-- Source line 9: CollatzLab.nonContracting_square_prefix
theorem nonContracting_square_prefix (k j : Nat) (hj : j < 3 ^ k) :
    Morphism.word Morphism.nonContracting110111 (3 ^ k + j) =
      Morphism.word Morphism.nonContracting110111 j

-- Source line 15: CollatzLab.no_rational_seed_realizes_nonContracting110111
theorem no_rational_seed_realizes_nonContracting110111 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.nonContracting110111)

-- Source line 20: CollatzLab.no_rational_seed_shifted_nonContracting110111
theorem no_rational_seed_shifted_nonContracting110111 (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.nonContracting110111) t)

-- Source line 25: CollatzLab.no_eventually_shifted_nonContracting110111
theorem no_eventually_shifted_nonContracting110111 (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.nonContracting110111 (t + j))

-- Source line 31: CollatzLab.no_eventually_shifted_nonContracting110111_signed
theorem no_eventually_shifted_nonContracting110111_signed (s t : Nat) (p q : Int)
    (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.nonContracting110111 (t + j))

-- Source line 43: CollatzLab.nonContracting_variable_cocycle
theorem nonContracting_variable_cocycle {p q : Int}
    (hr : RealizesWord p q (Morphism.parityWord Morphism.nonContracting110111)) (n : Nat) :
    8 * numIter q p (3 * (n + 1)) =
      (if Morphism.word Morphism.nonContracting110111 n then 9 else 27) * numIter q p (3 * n) +
      (if Morphism.word Morphism.nonContracting110111 n then 5 else 19) * q

-- Source line 55: CollatzLab.nonContracting_no_common_center
theorem nonContracting_no_common_center :
    ¬ ∃ c : Int, 5 = (8 - 9) * c ∧ 19 = (8 - 27) * c

```


### SpectralThreshold.lean

[Pinned source](https://github.com/hipotures/collatz-lab/blob/d270b4466794badc49da6feebefeda77f5793e16/CollatzLab/SpectralThreshold.lean).


Original namespace: `CollatzLab.Morphism`.

```lean
-- Source line 10: CollatzLab.Morphism.power_image_count
theorem power_image_count {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (k a : Nat) :
    frequencyDen M * (weight (fun j => word M (L ^ k * a + j)) (L ^ k) : Int) =
      (weight (image M false) L : Int) * (L ^ k : Nat) +
        weightDelta M ^ k * (frequencyDen M * bit (word M a) -
          (weight (image M false) L : Int))

-- Source line 26: CollatzLab.Morphism.prolongable_spectral_gap
theorem prolongable_spectral_gap {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M) :
    absInt (weightDelta M) < (L : Int)

-- Source line 37: CollatzLab.Morphism.frequencyDen_zero_images
theorem frequencyDen_zero_images {L : Nat} (M : Images L) (hD : frequencyDen M = 0) :
    weight (image M false) L = 0 ∧ weight (image M true) L = L

-- Source line 44: CollatzLab.Morphism.weight_chunks_bound
theorem weight_chunks_bound (v : Nat → Bool) (k R : Nat)
    (hb : ∀ n, weight (fun j => v (k * n + j)) k ≤ R) : ∀ m,
    weight v (k * m) ≤ m * R

-- Source line 56: CollatzLab.Morphism.weight_prefix_shift_bound
theorem weight_prefix_shift_bound (v : Nat → Bool) (t k R : Nat)
    (hb : ∀ n, weight (fun j => v (t + k * n + j)) k ≤ R) (m : Nat) :
    weight v (k * m) ≤ weight v t + m * R

-- Source line 68: CollatzLab.Morphism.uniform_chunks_frequency_necessary
theorem uniform_chunks_frequency_necessary {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M)
    (t k R : Nat)
    (hb : ∀ n, weight (fun j => word M (t + k * n + j)) k ≤ R) :
    (weight (image M false) L : Int) * (k : Int) ≤ frequencyDen M * (R : Int)

```


Original namespace: `CollatzLab`.

```lean
-- Source line 133: CollatzLab.rational_ratio_contraction
theorem rational_ratio_contraction (s d R S : Nat) (_hd : 1 ≤ d) (hS : 1 ≤ S)
    (hgap : (3 : Int) ^ s < (2 : Int) ^ d) (hcap : d * R ≤ s * S) :
    (3 : Int) ^ R < (2 : Int) ^ S

-- Source line 150: CollatzLab.rational_ratio_no_contraction
theorem rational_ratio_no_contraction (s d R S : Nat) (hd : 1 ≤ d) (hS : 1 ≤ S)
    (hgap : (2 : Int) ^ d < (3 : Int) ^ s) (hcap : s * S ≤ d * R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ S

-- Source line 167: CollatzLab.rational_threshold_ne
theorem rational_threshold_ne (s d : Nat) (hd : 1 ≤ d) :
    (3 : Int) ^ s ≠ (2 : Int) ^ d

```


Original namespace: `CollatzLab.Morphism`.

```lean
-- Source line 179: CollatzLab.Morphism.spectral_no_uniform_contraction
theorem spectral_no_uniform_contraction {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (d : Nat) (hd : 1 ≤ d)
    (hD : frequencyDen M = (d : Int))
    (hgap : (2 : Int) ^ d < (3 : Int) ^ weight (image M false) L)
    (t k R : Nat) (hk : 1 ≤ k)
    (hb : ∀ n, weight (fun j => word M (t + k * n + j)) k ≤ R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ k

-- Source line 194: CollatzLab.Morphism.power_image_discrepancy_bound
theorem power_image_discrepancy_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M) (k a : Nat) :
    absInt (frequencyDen M *
      (weight (fun j => word M (L ^ k * a + j)) (L ^ k) : Int) -
      (weight (image M false) L : Int) * (L ^ k : Nat)) ≤
      absInt (weightDelta M) ^ k * (frequencyDen M + (weight (image M false) L : Int))

-- Source line 216: CollatzLab.Morphism.exists_power_ratio_bound
theorem exists_power_ratio_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M)
    (s d : Nat) (hd : 1 ≤ d)
    (hmargin : (d : Int) * (weight (image M false) L : Int) < frequencyDen M * (s : Int)) :
    ∃ k R : Nat, d * R ≤ s * L ^ k ∧
      ∀ a, weight (fun j => word M (L ^ k * a + j)) (L ^ k) ≤ R

-- Source line 289: CollatzLab.Morphism.exists_contracting_power_of_ratio
theorem exists_contracting_power_of_ratio {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M)
    (s d : Nat) (hd : 1 ≤ d)
    (hmargin : (d : Int) * (weight (image M false) L : Int) < frequencyDen M * (s : Int))
    (hgap : (3 : Int) ^ s < (2 : Int) ^ d) :
    ∃ k R : Nat, (3 : Int) ^ R < (2 : Int) ^ (L ^ k) ∧
      ∀ a, weight (fun j => word M (L ^ k * a + j)) (L ^ k) ≤ R

```


Original namespace: `CollatzLab`.

```lean
-- Source line 305: CollatzLab.rational_gap_thickening
theorem rational_gap_thickening (r d : Nat) (hd : 1 ≤ d)
    (hgap : (3 : Int) ^ r < (2 : Int) ^ d) :
    ∃ s d' : Nat, 1 ≤ d' ∧ d' * r < d * s ∧ (3 : Int) ^ s < (2 : Int) ^ d'

```


Original namespace: `CollatzLab.Morphism`.

```lean
-- Source line 334: CollatzLab.Morphism.subcritical_has_contracting_power
theorem subcritical_has_contracting_power {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (d : Nat) (hd : 1 ≤ d)
    (hD : frequencyDen M = (d : Int))
    (hgap : (3 : Int) ^ weight (image M false) L < (2 : Int) ^ d) :
    ∃ k R : Nat, (3 : Int) ^ R < (2 : Int) ^ (L ^ k) ∧
      ∀ a, weight (fun j => word M (L ^ k * a + j)) (L ^ k) ≤ R

-- Source line 349: CollatzLab.Morphism.uniform_contraction_iff_subcritical
theorem uniform_contraction_iff_subcritical {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (d : Nat) (hd : 1 ≤ d)
    (hD : frequencyDen M = (d : Int)) :
    (∃ t k R : Nat, 1 ≤ k ∧
      (∀ n, weight (fun j => word M (t + k * n + j)) k ≤ R) ∧
      (3 : Int) ^ R < (2 : Int) ^ k) ↔
        (3 : Int) ^ weight (image M false) L < (2 : Int) ^ d

-- Source line 371: CollatzLab.Morphism.frequencyDen_nonnegative
theorem frequencyDen_nonnegative {L : Nat} (M : Images L) : 0 ≤ frequencyDen M

-- Source line 378: CollatzLab.Morphism.frequencyDen_zero_word
theorem frequencyDen_zero_word {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (hD : frequencyDen M = 0) (n : Nat) : word M n = true

-- Source line 393: CollatzLab.Morphism.binary_incidence_characteristic
theorem binary_incidence_characteristic (L r0 r1 x : Int) :
    (x - (L - r0)) * (x - r1) - (L - r1) * r0 =
      (x - L) * (x - (r1 - r0))

```


### NonContractingPartialReturn.lean

[Pinned source](https://github.com/hipotures/collatz-lab/blob/d270b4466794badc49da6feebefeda77f5793e16/CollatzLab/NonContractingPartialReturn.lean).


Original namespace: `CollatzLab.Morphism`.

```lean
-- Source line 8: CollatzLab.Morphism.nonContracting1011
def nonContracting1011 : Images 4

-- Source line 12: CollatzLab.Morphism.nonContracting1011_images
theorem nonContracting1011_images :
    List.ofFn nonContracting1011.one = [true, false, true, true] ∧
    List.ofFn nonContracting1011.zero = [true, true, true, true] ∧
    image nonContracting1011 true 0 = true ∧
    frequencyDen nonContracting1011 = 5 ∧ weightDelta nonContracting1011 = -1 ∧
    weight (image nonContracting1011 false) 4 = 4

-- Source line 19: CollatzLab.Morphism.nonContracting1011_columns
theorem nonContracting1011_columns (n : Nat) :
    parityWord nonContracting1011 (4 * n) = 1 ∧
    parityWord nonContracting1011 (4 * n + 1) = 1 - parityWord nonContracting1011 n ∧
    parityWord nonContracting1011 (4 * n + 2) = 1 ∧
    parityWord nonContracting1011 (4 * n + 3) = 1

-- Source line 33: CollatzLab.Morphism.nonContracting1011_not_periodic_from
theorem nonContracting1011_not_periodic_from (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → parityWord nonContracting1011 (n + p) = parityWord nonContracting1011 n) → False

-- Source line 62: CollatzLab.Morphism.nonContracting1011_not_eventually_periodic
theorem nonContracting1011_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord nonContracting1011)

-- Source line 68: CollatzLab.Morphism.nonContracting1011_partial_return
theorem nonContracting1011_partial_return (k j : Nat) (hj : j < 4 ^ k) :
    word nonContracting1011 (2 * 4 ^ k + j) = word nonContracting1011 j

-- Source line 75: CollatzLab.Morphism.nonContracting1011_prefix_weight
theorem nonContracting1011_prefix_weight (k : Nat) :
    8 * (4 ^ k : Nat) - 3 ≤ 5 * (weight (word nonContracting1011) (2 * 4 ^ k) : Int) ∧
    5 * (weight (word nonContracting1011) (2 * 4 ^ k) : Int) ≤ 8 * (4 ^ k : Nat) + 3

-- Source line 96: CollatzLab.Morphism.nonContracting1011_no_uniform_chunks
theorem nonContracting1011_no_uniform_chunks (t k R : Nat) (hk : 1 ≤ k)
    (hb : ∀ n, weight (fun j => word nonContracting1011 (t + k * n + j)) k ≤ R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ k

```


Original namespace: `CollatzLab`.

```lean
-- Source line 108: CollatzLab.no_rational_seed_realizes_nonContracting1011
theorem no_rational_seed_realizes_nonContracting1011 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.nonContracting1011)

-- Source line 144: CollatzLab.no_rational_seed_shifted_nonContracting1011
theorem no_rational_seed_shifted_nonContracting1011 (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.nonContracting1011) t)

-- Source line 149: CollatzLab.no_eventually_shifted_nonContracting1011_signed
theorem no_eventually_shifted_nonContracting1011_signed (s t : Nat) (p q : Int)
    (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.nonContracting1011 (t + j))

```


Original namespace: `CollatzLab.NonContractingPartialChecks`.

```lean
-- Source line 160: CollatzLab.NonContractingPartialChecks.literalStep
def literalStep (xs : List Int) : List Int

-- Source line 163: CollatzLab.NonContractingPartialChecks.literalIter
def literalIter : Nat → List Int

-- Source line 169: CollatzLab.NonContractingPartialChecks.literal_semantics
theorem literal_semantics :
    word nonContracting1011 1 = false ∧
    (List.range 4).map (parityWord nonContracting1011) = literalIter 1 ∧
    (List.range 16).map (parityWord nonContracting1011) = literalIter 2 ∧
    (List.range 64).map (parityWord nonContracting1011) = literalIter 3 ∧
    (List.range 256).map (parityWord nonContracting1011) = literalIter 4

-- Source line 178: CollatzLab.NonContractingPartialChecks.signed_finite_semantics
theorem signed_finite_semantics :
    (List.range 81).map (seedParity 1 475541435535248609609897) = (literalIter 4).take 81 ∧
    numIter 1 475541435535248609609897 81 = 2026003878711805313935167780941 ∧
    (List.range 81).map (seedParity 5 (-40144461553015301362867)) = (literalIter 4).take 81 ∧
    numIter 5 (-40144461553015301362867) 81 = -171032067318510884297708363138 ∧
    (List.range 81).map (seedParity 15 (-120433384659045904088601)) = (literalIter 4).take 81

```

## Appendix B. Reproducible independent finite computations

These two scripts use only Python's standard library, with no repository
imports or cached Lean results. The first deliberately uses the rational map
and parity lifting rather than the PR checker's modular-inverse witness
construction. The second obtains the exact factor language by closure of the
actual initial window under every child offset. Every generated factor occurs
by substitution; coverage follows by descent of its starting index. Its finite
counts support the separately proved uniform bound (15).

Run the embedded scripts from the review clone with:

```bash
python3 - <<'PYRUN'
from pathlib import Path
import subprocess, sys
s = Path('research/phase11-independent-referee-report.md').read_text()
for name in ('adversarial.py', 'factor_check.py'):
    marker = '<!-- referee-script: ' + name + ' -->' + chr(10) + '```python' + chr(10)
    code = s.split(marker, 1)[1].split(chr(10) + '```', 1)[0]
    subprocess.run([sys.executable, '-c', code], check=True)
PYRUN
```

<!-- referee-script: adversarial.py -->
```python
from fractions import Fraction
from itertools import product
from hashlib import sha256
from pathlib import Path

# No repository imports. Evaluate the rational map itself and construct finite
# witnesses by parity lifting, without the repository's affine implementation.
def orbit(p,q,n):
    x=Fraction(p,q); states=[x]; bits=[]
    for _ in range(n):
        b=x.numerator%2; bits.append(b)
        x=(3*x+1)/2 if b else x/2
        states.append(x)
    return bits,states

def lift(bits,q):
    p=0
    for j,b in enumerate(bits):
        candidates=[a for a in (p,p+2**j) if orbit(a,q,j+1)[0]==list(bits[:j+1])]
        assert len(candidates)==1
        p=candidates[0]
    return p

def coefficients(bits):
    positions=[j for j,b in enumerate(bits) if b]
    r=len(positions)
    c=sum(2**j*3**(r-i-1) for i,j in enumerate(positions))
    return r,c

n_offsets=n_returns=0
for m in range(11):
    for u in product((0,1),repeat=m):
        r,c=coefficients(u); cap=2**(m-r)*3**r-2**m
        assert 0<=c<=cap<=3**m-2**m
        assert coefficients([0]*(m-r)+[1]*r)[1]==cap
        n_offsets+=1
for m in range(1,8):
    for u in product((0,1),repeat=m):
        r,c=coefficients(u)
        for ell in range(m+3):
            bits=[u[j%m] for j in range(m+ell)]
            for q in (-15,-5,-3,-1,1,3,5,15):
                p0=lift(bits,q)
                for p in (p0,p0-2**len(bits)):
                    got,states=orbit(p,q,len(bits)); assert got==bits
                    y=states[m]*q; assert y.denominator==1
                    E=(2**m-3**r)*p-c*q
                    assert E==2**m*(p-y)
                    assert E%2**(m+ell)==0
                    assert abs(E)<=abs(p)*abs(2**m-3**r)+abs(q)*c
                    assert abs(E)<=(abs(p)+abs(q))*2**(m-r)*3**r
                    if E: assert 2**(ell+r)<=(abs(p)+abs(q))*3**r
                    assert orbit(-p,-q,len(bits))[0]==bits
                    assert orbit(3*p,3*q,len(bits))[0]==bits
                    n_returns+=1
print('offset words:',n_offsets,'signed partial-return witnesses:',n_returns)
for u,q,ell in (([1,1,0],5,3),([1,0,1,1,1,1,1,1],-5,4)):
    bits=(u*3)[:len(u)+ell];p=lift(bits,q);r,c=coefficients(u)
    got,s=orbit(p,q,len(bits));E=(2**len(u)-3**r)*p-c*q
    print('instance:',dict(u=u,p=p,q=q,r=r,c=c,states=[str(x*q) for x in s],E=E,modulus=2**len(bits)))

morphism_cases=0
for L in range(2,6):
    for one_tail in product((0,1),repeat=L-1):
        one=(1,)+one_tail
        for zero in product((0,1),repeat=L):
            r0,r1=sum(zero),sum(one);D=L-r1+r0;delta=r1-r0
            images={0:zero,1:one}; power={0:(0,),1:(1,)}
            if D: assert abs(delta)<L and 3**r0!=2**D
            else: assert r0==0 and r1==L
            for k in range(5):
                for b in (0,1):
                    assert D*sum(power[b])==r0*L**k+delta**k*(D*b-r0)
                assert power[1][0]==1
                if k<4: power={b:tuple(x for a in power[b] for x in images[a]) for b in (0,1)}
            morphism_cases+=1
print('literal prolongable substitutions L=2..5:',morphism_cases)
for one,zero in (((1,1,0),(1,1,1)),((1,0,1,1),(1,1,1,1))):
    w=(1,);L=len(one)
    for _ in range(8):w=tuple(x for b in w for x in (one if b else zero))
    for k in range(7):
        S=L**k
        if L==3:assert w[:S]==w[S:2*S]
        else:
            assert w[:S]==w[2*S:3*S]
            assert 5*sum(w[:2*S])==8*S-3*(-1)**k
    for t in range(8):
        for k in range(1,41):
            R=max(sum(w[t+k*n:t+k*(n+1)]) for n in range(20))
            assert 3**R>=2**k
    print('literal return/window target:',one,zero,'PASS')
assert orbit(1,1,100)[0]==[1,0]*50
assert orbit(-1,1,100)[0]==[1]*100
# A finite square is compatible with rationality. Positive-time nonzero cannot
# be asserted at m=0; constant-one is the necessary periodic control.
assert orbit(1,1,4)[0]==[1,0,1,0]
assert (2**1-3)*(-1)-1==0
print('negative controls and finite-prefix distinction: PASS')
```

<!-- referee-script: factor_check.py -->
```python
from collections import deque
for one,zero in [('110','111'),('1011','1111')]:
    L=len(one);w='1'
    while len(w)<L**6:w=''.join(one if b=='1' else zero for b in w)
    print('target',one,zero)
    for k in range(1,7):
        n=L**k;seen={w[:n]};todo=deque(seen)
        while todo:
            y=''.join(one if b=='1' else zero for b in todo.popleft())
            for r in range(L):
                z=y[r:r+n]
                assert len(z)==n
                if z not in seen:seen.add(z);todo.append(z)
        cap=(L+1)*L**(k-1)
        assert len(seen)<=cap
        print('length',n,'exact closed language',len(seen),'bound',cap)
    assert 2**(2*L+1)>3**(L+1)
print('single-hole language bounds and Dubickas base gaps: PASS')
```

Verified outputs (all computations are finite):

```text
offset words: 2047 signed partial-return witnesses: 36800
instance: {'u': [1, 1, 0], 'p': 39, 'q': 5, 'r': 2, 'c': 5, 'states': ['39', '61', '94', '47', '73', '112', '56'], 'E': -64, 'modulus': 64}
instance: {'u': [1, 0, 1, 1, 1, 1, 1, 1], 'p': 1203, 'q': -5, 'r': 7, 'c': 3389, 'states': ['1203', '1802', '901', '1349', '2021', '3029', '4541', '6809', '10211', '15314', '7657', '11483', '17222'], 'E': -2306048, 'modulus': 4096}
literal prolongable substitutions L=2..5: 680
literal return/window target: (1, 1, 0) (1, 1, 1) PASS
literal return/window target: (1, 0, 1, 1) (1, 1, 1, 1) PASS
negative controls and finite-prefix distinction: PASS
target 110 111
length 3 exact closed language 4 bound 4
length 9 exact closed language 12 bound 12
length 27 exact closed language 36 bound 36
length 81 exact closed language 108 bound 108
length 243 exact closed language 324 bound 324
length 729 exact closed language 972 bound 972
target 1011 1111
length 4 exact closed language 5 bound 5
length 16 exact closed language 20 bound 20
length 64 exact closed language 80 bound 80
length 256 exact closed language 320 bound 320
length 1024 exact closed language 1280 bound 1280
length 4096 exact closed language 5120 bound 5120
single-hole language bounds and Dubickas base gaps: PASS
```
