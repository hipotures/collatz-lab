# Independent Phase 11 mathematical referee report — issue #21

Review date: 14 November 2026 (UTC). This is an independent AI-assisted review,
not independent human peer review or journal acceptance.

## Executive verdict and exact scope

**Mathematical verdict: PASS for the exact formal statements. Overall
integration recommendation: CONDITIONAL — correct attribution and the
specific documentation error below, then merge as formal research if the owner
approves. Publication recommendation: no separate new-theorem paper yet.**

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
Their explicit instantiation and Lean formalization can still be useful;
first discovery of either application has not been established.

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
| P1 | High for originality/publication; no correctness defect | Earlier exact overlap: Allikvere, Lemma 2.1, Theorem 2.3 and Corollary 3.2; Cassidy, Theorem R. The core inequalities and signed scope precede Phase 11. See the primary-source matrix and explicit parameter correspondence below. | Add these primary citations and exact overlap to Phase 11 findings and any future publication framing. Describe the core exclusion as an independent elementary formalization of an earlier criterion. |
| M1 | Medium, scientific interpretation | `research/phase11-findings.md:102–105` claims that deleting either safeguard makes the theorem false. Both listed rational controls are periodic. They cannot falsify a theorem that still assumes non-eventual-periodicity. | Replace the last sentence by: “Dropping non-eventual-periodicity is false, as the all-one control shows. Dropping repetition while retaining non-eventual-periodicity would assert the open rational Periodicity Conjecture.” |
| L1 | Low, editorial | The “Research in progress” paragraph at `research/phase11-findings.md:45–50` still says the square-prefix proof is being developed, while later sections correctly record its completion. | Mark it as historical or update it. |
| L2 | Scope reminder, not a defect | The real-frequency limit is deduced from integer estimates; a conjugacy-value formulation additionally uses the published parity bijection. Neither is a Lean real/2-adic analysis theorem here. | Preserve those distinctions. Do not label the analytic or transcendence statements Lean-verified. |

**Critical findings: none.** No change to a Lean proof or its assumptions is
needed for the results audited here. M1 is a correction to prose, not a
counterexample to an exported theorem.

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
| All-zero / absent-one issue | An all-zero selected word is impossible because `w(0)=1`. Eventually zero is possible: `1->10,0->00`, with density zero and a rational realization. |
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

To be completed with the exact signature inventory and pinned source links.

## 6. Primary-source comparison and priority

The decisive primary text obtained in this review is Jaan Allikvere,
*Periodic shadows, drift pressure, and transcendence of the 3x+1 conjugacy
map*, [Zenodo record 21543841](https://doi.org/10.5281/zenodo.21543841),
created 25 July 2026, updated 13 August 2026. Lemma 2.1 and Theorem 2.3
(pp. 2–3) were read with their proofs; Corollary 3.2 (p. 3) is the square
criterion. The substitutions are not needed in the source theorem.
Its `s,h,L,B_V,D_V,a,b` are our `m,r,m+ell,c,B-A,p,q`; its nonzero
cross product is `-E_m`. Its inequality is exactly (6) after cancellation.
Both numerator signs are covered. Thus these core results are **known in an
earlier unrefereed preprint**, independently reconstructed and formalized
here. The source's stronger transcendence claims are a separate evidence level.

The remaining source matrix, explicit applications and publication decision
will be completed before opening the review PR. The elementary source has
been checked, but no conclusion of this report depends on its authority.
