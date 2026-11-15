# Independent adversarial referee report: Phase 13 / issue #31

**Checkpoint draft: the mathematical derivation below and computational
checks are complete; the final source matrix, declaration-by-declaration
assessment and integration verdict are being assembled. This checkpoint is
not a final approval.**

Task: [#31](https://github.com/hipotures/collatz-lab/issues/31).
Implementation: [PR #29](https://github.com/hipotures/collatz-lab/pull/29),
exact commit `65b087dc62e4950e1c504fe34865acaacb9188c9`, based on
`93647176a526eb8660b4dbf2ac428b0053117659`.
Supplement: `76bf6136c334c1db9e52e399fcc33fd4c20b9c24` on
`codex/phase13-overnight`. Both live heads matched those pins at startup.
Review branch: `review/phase13-independent-referee`.
The implementation and overnight branches, issue states and `paper/` are
untouched. This is an AI-assisted independent review, not human peer review.

Evidence labels used below: **W** independently written mathematics;
**K** kernel-checked exact Lean statement; **F** finite exact integer
computation; **S** original source passages actually examined; **U** unresolved
or unchecked. A passing program establishes its finite checks, not the
universal mathematical interpretation. There is no formal real-limit theorem
in the audited implementation.

## 1. Independent definitions and the finite semantic bridge

Let

\[
T(x)=\begin{cases}x/2&x\equiv0\pmod2,\\(3x+1)/2&x\equiv1\pmod2.\end{cases}
\]

For integers p and odd q of either sign define integer states
`p_0=p`, `p_(j+1)=p_j/2` for even p_j and `(3p_j+q)/2` otherwise.
Every division is exact, including for negative numerators. Because q is a
2-adic unit, the parity of p_j/q is p_j mod 2. Python and Lean both use a
remainder in {0,1}; no truncation-toward-zero convention is being substituted.
Thus this is exactly `seedParity(q,p,j)`, while `RealizesWord(p,q,v)` reverses
the first two argument positions and additionally requires q>0.

Here is an independent inverse-branch derivation. Define
`F_0(t)=2t`, `F_1(t)=(2t-1)/3`. Each maps Z_2 bijectively onto its prescribed
parity cylinder and is inverse to the corresponding branch of T. For a
finite bit string X of length n, let r_j count its ones before j. Composition
in chronological order gives

\[
F_X(t)=F_{X_0}\circ\cdots\circ F_{X_{n-1}}(t)
 =\frac{2^nt-C_X}{3^{r_n}},\qquad
\frac{C_X}{3^{r_n}}=
 \sum_{\substack{0\le j<n\\X_j=1}}\frac{2^j}{3^{r_j+1}}.\tag{1}
\]

In particular, `F_X(Z_2)` is exactly one residue modulo 2^n, namely
`A_X=-C_X/3^r_n mod 2^n`. This proves both existence and the converse,
rather than assuming that an affine identity on a prescribed itinerary
already proves that itinerary. The 2^n finite parity strings give 2^n
disjoint nonempty cylinders, so the parity/residue correspondence is a
bijection.

For two odd-denominator fractions p/q and r/s, belonging to the same n-bit
cylinder is therefore equivalent to

\[
2^n\mid ps-rq.\tag{2}
\]

One can also verify (2) without introducing Q_2: if the first bits agree,
the next cross product is the old one multiplied by 1 or 3 and divided by
2. Conversely an even cross product forces the first bits to agree, and
then one precision bit can be removed. Induction proves the equivalence,
and if the first mismatch is at m its cross-product valuation is exactly m.
This is precisely the domain of `RationalHeight.prefix_cross_iff`.

All sign and reduction cases are material:

- Simultaneous negation `(p,q)->(-p,-q)` preserves the itinerary. A negative
  odd q is allowed in the finite equivalence, but is excluded by
  `RealizesWord` until normalized positive.
- Cancelling a positive common divisor d of an admissible pair preserves
  precision because q odd implies d odd, so d is invertible modulo 2^n.
  Common **even** factors cannot be cancelled with n unchanged.
- For example at n=8, A=128, `(0,2)` lies in the unrestricted lattice but
  `(0,1)` does not. It is not an admissible rational-seed certificate.
- Zero numerator is admissible: `(0,1)` realizes the zero word. There is no
  hidden numerator-positivity or nonzero-orbit assumption in the height.

For an infinite word v, put
`Lambda_n={(p,q):p-A_n*q is divisible by 2^n}`. Its complete integer basis
is `((2^n,0),(A_n,1))`, of absolute determinant 2^n. Restrict to positive
odd q and use height `max(|p|,q)`. At n=0 its minimum is 1. At n>=1 a
centered integer representative with q=1 has height at most 2^(n-1).
Consequently H_n exists and `1<=H_n<=2^(n-1)` for n>=1. Reducing an odd
common divisor strictly decreases height unless d=1, so every minimizing
pair is primitive. The unrestricted-odd-pair minimum in the Lean definition
equals exactly the primitive-pair minimum in the issue. Nested cylinders
give monotonicity.

If distinct rational values of heights h and h' share n bits, their nonzero
integer cross product has absolute value at least 2^n and at most 2hh'. Thus

\[
2^n\le2hh'.\tag{3}
\]

This proves strict bounded reconstruction uniqueness when `2B^2<2^n`; it
does not prove existence in that box. The hostile A=2^(n-1) family has
H_n=2^(n-1): every odd q has centered numerator magnitude 2^(n-1).
It disproves any uniform square-root existence bound for all cylinders.

Finally H_n is eventually bounded iff a single positive-odd-denominator
rational realizes v at every index. For the reverse direction, all bounded
candidate pairs form a finite set. If none realizes the whole word, select
one failing index per pair and take their finite maximum. A later nonempty
cylinder is then impossible. No Periodicity Conjecture or assertion that
every rational has eventually periodic **parity** is used. These arguments
independently justify the intended H, not just compilation of its definition.

## 2. Independent word and shadow construction

Let `mu(1)=100111`, `mu(0)=111110`, and w be the one-start fixed point.
These are unequal weights 4 and 5. For S=6^k define
`U=mu^k(100)`, `V=mu^k(1)`, and `z=UV^infinity`.
Their lengths are 3S and S. This gives a preperiod and a period, without
claiming either is minimal. U and V are prefixes of w, since 100 and 1
are prefixes and mu(w)=w. The first period after U is V, because w_3=w_0=1.

At k=0 the sequence is `100111111...`. The literal first twelve symbols of
w are `100111111110`; the signed seed -3 has states -3,-4,-2,-1,-1,...
and hence agrees at indices 0 through 10 and fails at index 11.
For any two words whose first mismatch is at m, their images agree through
the first column of that differing block, because both images start with 1;
their second columns are respectively 0 and 1. Their **exact** first
mismatch is consequently at 6m+1. Applying this to z and w proves

\[
L_0=11,\quad L_{k+1}=6L_k+1,\quad
L_k=\frac{56\,6^k-1}{5}.\tag{4}
\]

This checks the zero-based bit versus prefix-length distinction: the first
failing prefix lengths are 12,68,404,2420,14516,87092,522548,....
It is not merely a lower bound on agreement and is not inferred from an
experiment.

Independently count image weights. If a word X has length m and t ones,
then mu(X) has `5m-t` ones. The recurrence for its kth image is
`t_(k+1)=5m*6^k-t_k`, with solution

\[
t_k=\frac{5m6^k+(7t-5m)(-1)^k}{7}.
\]

It follows, with e=(-1)^k, that

\[
r_U=(15S-8e)/7,\quad r_V=(5S+2e)/7,\quad
R_k=r_U+r_V=(20S-6e)/7.\tag{5}
\]

The divisibility is not a rational exponent convention: 6=-1 mod 7,
so these numerators are divisible by 7, and the counts are nonnegative.

Write `a=3^r_U`, `b=3^r_V`, `c=C_U`, `d=C_V`, `m=2^S`.
Closing the period in (1) gives tail seed `-d/(b-m)`. Prepending U gives

\[
P=-(m^3d+c(b-m)),\quad Q=a(b-m).\tag{6}
\]

The denominator is odd: a and b are odd and m is even since S>=1.
It is positive at k=0 (b-m=1). For k>=1, every substituted block has at
least four ones, so `b>=3^(4S/6)>2^S`, because 3^4=81>64=2^6.
The inverse maps show that (6) realizes **all** of UV^infinity. Its period
seed returns exactly after S steps, not merely modulo a power of two.
Odd gcd reduction and sign normalization preserve the entire itinerary.

For independent arithmetic verification, our code uses the **forward**
summary `(2^|X|,3^r_X,C_X)`, with concatenation

\[
(m,a,c)\star(n,b,d)=(mn,ab,bc+md).\tag{7}
\]

This evaluates positive expanded sums and has the opposite affine viewpoint
to an inverse-matrix implementation. Literal rational inverse compositions
at levels 0 through 4 independently check it. The products do not commute.
Already F_1(F_0(t))=(4t-1)/3 differs from F_0(F_1(t))=(4t-2)/3.
At the first substituted level the inverse matrices have offsets 179 and
211 and denominators 81 and 243. On source string 10 the true 12-bit residue
is 2045, whereas replacing the second denominator by 81 gives 3965.
Thus the equal-weight scalar shortcut is demonstrably invalid here.

Early exact raw pairs are

| k | P | Q | gcd | reduced height |
|---|---:|---:|---:|---:|
| 0 | -9 | 3 | 3 | 3 |
| 1 | -297087259 | 81310473 | 1 | 297087259 |
| 2 | -16203862960316511395526276149762509540564489776907 | 4512998360485453372143261030379261148415376536153 | 1 | 16203862960316511395526276149762509540564489776907 |

## 3. Independent height estimate and the nonzero crossing

A full six-letter image contributes at least four ones. In a residual prefix
of length s=0,...,5 the minimum count is respectively `(0,1,1,1,2,3)`.
Checking these six cases and 2^6<=3^4 proves

\[
2^n\le4\,3^{r_n}\quad(n\ge0).\tag{8}
\]

Here is a separate summation derivation of the offset bound rather than a
copy of the source's offset induction. Divide the expanded sum in (1) by
3^r_n. At each one position j, (8) bounds its summand by 4/3. Hence
`C_X <= (4/3)n*3^r_n <= 2n*3^r_n` for prefixes X of w.
For U and V this gives `c<=6Sa`, `d<=2Sb`; also `m^3<=4a` and
`0<b-m<b`. Consequently

\[
|P|\le8Sab+6Sab=14Sab,\qquad
0<Q\le ab\le14Sab.
\]

Put `T_k=14*6^k*3^R_k`. Thus the unreduced pair already has height at most
T_k, and the primitive positive-denominator pair has no larger height. In
particular

\[
H_{L_k}\le T_k.\tag{9}
\]

Any minimum at precision N>L_k disagrees with the shadow at bit L_k,
while agreeing at every earlier bit. The rational values are therefore
different; their cross product is nonzero. Equation (2) and (3) give

\[
2^{L_k}\le2T_kH_N\qquad(N>L_k).\tag{10}
\]

There is no elimination of the two heights and no nonzero determinant
assumption imposed on a genuine return. Raw coordinates may be used because
their odd common divisor changes neither the itinerary nor the 2-adic
valuation. Equally, using reduced coordinates gives a stronger bound. A
negative seed causes no sign error: the archimedean bound is on the absolute
cross product and includes |P|.

The precise kernel endpoints corresponding to (9) and (10) are
`CollatzLab.FrontierHeight.H_shadow_upper` and `H_after_shadow`.
`shadow_realized`, `shadow_prefix`, `shadow_failure`, `shadow_weight_sum`
and `shadow_height_bound` discharge the all-k hypotheses. Their exact types
are in [the declaration inventory](phase13/referee/lean-statements.json).
The proof above is mathematical verification of their interpretation.

## 4. A standalone real asymptotics proof

All logarithms in this section have base 2. Let `a_N=log(H_N)/N` for N>=1
and

\[
c_*=\frac{25}{98}\log_2 3.
\]

The elementary bounds already give `0<=a_N<1`. Therefore finite liminf
and limsup exist. Equations (4) and (5) imply

\[
\frac{\log T_k}{L_k}
=\frac{\log14+k\log6}{L_k}+\frac{R_k}{L_k}\log3
\longrightarrow\frac{25}{98}\log3=c_* .\tag{11}
\]

Indeed the first term tends to zero since k/6^k tends to zero; for example
`k<=2^k` for k>=1 bounds it by a constant times 3^-k. For the second term,
`R_k/L_k=(100S-30e)/(392S-7)`; its difference from 25/98 is
`(175-2940e)/(98*(392S-7))`, tending to zero because |e|=1. Thus the
oscillating sign is explicitly accounted for. Strict separation requires
no floating-point approximation: `3^3=27<32=2^5` gives
`c_*<125/294<1/2`.

At the strictly increasing indices N=L_k, (9) and (11) show

\[
\liminf_{N\to\infty}a_N\le c_*.
\]

At the strictly increasing indices N=L_k+1, (10) shows

\[
a_{L_k+1}\ge\frac{L_k-1-\log T_k}{L_k+1}
\longrightarrow1-c_*.
\]

The displayed lower bound tends to 1-c_*; the a-values themselves need
not have that limit. Taking limsup yields `limsup a_N>=1-c_*`.
Since `c_*<1-c_*`, these two subsequences **alone disprove convergence**.
They use neither numerical trend extrapolation nor the external Klapper
theorem. All subsequence indices tend to infinity; no assumption about
different k yielding different rational shadows is needed here.

For the claimed uniform lower estimate, consider N>11 and choose the unique
k with `L_k<N<=L_(k+1)=6L_k+1`. The numerator
`E_k=L_k-1-log T_k` is positive for all sufficiently large k by (11).
For those k, (10) gives

\[
a_N\ge\frac{E_k}{N}\ge\frac{E_k}{6L_k+1}
\longrightarrow\frac{1-c_*}{6}.\tag{12}
\]

The finitely many N<=11 and any initial negative E_k do not affect liminf.
The direction of division in (12) would need care for negative E_k; the
eventual positivity supplies it. Also `L_k/N>=L_k/(6L_k+1)` approaches 1/6
from below. Replacing it by an exact finite inequality `L_k/N>=1/6` would
be wrong at N=6L_k+1, but the limiting deduction is valid.

Consequently the actual theorem established in written mathematics is

\[
\boxed{\frac{1-c_*}{6}\le\liminf a_N\le c_*<1-c_*\le\limsup a_N.}\tag{13}
\]

Decimal displays are approximately 0.09927880524, 0.40432716855 and
0.59567283145. The exact logarithmic expressions, not those decimals,
carry the proof. Neither endpoint equality nor an optimal exponent follows.

An additional non-circular observation is useful for the later source gate:
(10) at L_k+1 tends to an unbounded lower height because 1-c_*>0.
Monotonicity then forces H_N to infinity. By the finite bounded-height
criterion, x=Phi(w) cannot be rational. Thus the present proof independently
supplies the irrationality premise needed for digit-complexity and exponent
statements. Aperiodicity of w alone would not supply that premise.

## 5. Exact minima on the entire infinite shadow subsequence

Let `h_k=max(|P_k|,Q_k)/gcd(|P_k|,Q_k)`. This is the height of the unique
primitive positive-denominator representation, and `H_(L_k)<=h_k<=T_k`.

From (5), `R_(k+1)=6R_k+6(-1)^k<=6R_k+6`. If D=14*6^k, then

\[
T_{k+1}\le6\,3^6D(3^{R_k})^6\le D^6(3^{R_k})^6=T_k^6,
\]

because `6*3^6=4374<14^5<=D^5`. At k=2,
`T_2=504*3^102`, `L_2=403`, and exact integer comparison gives
`2*T_2^2<2^403`. If `2*T_k^2<2^L_k`, then

\[
2T_{k+1}^2\le2T_k^{12}\le(2T_k^2)^6
 <2^{6L_k}<2^{6L_k+1}=2^{L_{k+1}}.
\]

Thus this strict uniqueness region holds for every k>=2. A different
rational of height <=h_k in the L_k cylinder would contradict (3), since
`2*h_k^2<=2*T_k^2<2^L_k`. A pair representing the **same** rational cannot
have smaller height than its primitive positive-denominator representation.
Existence of a minimum now gives H_(L_k)=h_k, including uniqueness of its
rational value and of its primitive positive-denominator pair.

The initial k=0,1 checks must use h_k, not T_k. Exactly,
`2*3^2<2^11` and `2*297087259^2<2^67`. Both hold; `2*T_k^2<2^L_k`
fails at those early levels. Therefore the claimed all-k formula is valid:

\[
\boxed{H_{L_k}=\frac{\max(|P_k|,Q_k)}{\gcd(|P_k|,Q_k)}\quad(k\ge0).}\tag{14}
\]

This is a written all-level deduction, not a Lean theorem about exact
subsequence minima and not evidence for an asymptotic formula with the gcd
removed. The numerator and denominator are given explicitly; a still
uncontrolled integer gcd remains in the expression.

## 6. Odd-denominator approximation exponent and digit convention

For irrational x in Z_2, use only reduced fractions p/q with q>0 odd,
height H=max(|p|,q)>1. Define

\[
\mu_2(x)=\limsup_{H(p/q)\to\infty}
 \frac{v_2(x-p/q)}{\log_2 H(p/q)}.
\]

The valuation is finite for every such rational, and agrees with the exact
length of common initial Collatz parities by (2). This definition counts
distinct rational values; allowing arbitrary unreduced scalings or log H=0
would require a different convention.

Here is the complete reciprocal argument. Irrationality implies H_N tends
to infinity by the finite candidate argument. If `mu_2<infinity`, then for
each epsilon>0 all sufficiently large-height fractions have precision at
most `(mu_2+epsilon)*log H`. Apply this to a minimum at N, whose precision
is at least N, to get `liminf a_N>=1/(mu_2+epsilon)`. Conversely for every
positive t<mu_2 there are arbitrarily large-height fractions with precision
m>t*log H; those precisions go to infinity, and `H_m<=H` gives
`a_m<1/t`. Hence `liminf a_N<=1/mu_2`. If mu_2 is infinite, let t tend
to infinity; the reciprocal is zero. Equivalently, a zero liminf forces an
infinite exponent by the minimizing subsequence. Thus

\[
\liminf a_N=1/\mu_2(x),\qquad 1/\infty=0.\tag{15}
\]

Applied to (13), this yields the stated weak finite bounds
`1/c_*<=mu_2(Phi(w))<=6/(1-c_*)`. They are not optimality statements.

Write `x=sum d_i*2^i` with its ordinary binary digits d_i. Classical finite
2-adic complexity of **d**, with the same signed minimax norm and an odd
denominator, is exactly log H_N by (2). The input is d, not w. For example
the three-bit parity string 100 has seed residue 5 mod 8 and minimum height
3, whereas the ordinary three-bit digit string 100 represents residue 1
mod 8 and has height 1. Automaticity of w supplies no automaticity statement
about d. Rationality of x would mean eventual periodicity of d, not a
generally proved eventual periodicity of its Collatz parity w.

With irrationality established independently above, Klapper's Corollary 3.4
for base 2 applies to d and gives its accumulation interval `[B,1-B]`,
where `B=liminf a_N`. In particular `limsup a_N=1-B` and B<=1/2.
This equality is an attributed external theorem; (13) and nonconvergence
were already proved without it. The exact value B, subexponential shadow
gcd cancellation and possible better intermediate approximants remain open.

## 7. Modular certificates and their actual scope

Modulo m coprime to 6, consider the inverse maps F_0,F_1. Our independent
checker represents an affine map by its values at 0 and 1 and composes these
values through the literal image strings in reverse order. This avoids
copying a stored matrix-state trace. It exactly verifies:

| modulus | initial repeated level a | repeated level a+t | identity level b for F_(mu^b(1)) |
|---|---:|---:|---:|
| 347 | 1 | 87 | 7 |
| 120409=347^2 | 62 | 14940 | 5425 |

The complete state includes both image maps. Since its update is
deterministic, equality at a and a+t implies equality at a+j and a+t+j
for every j>=0 by induction. The identity at b therefore recurs at b+tj
for all j>=0. An inverse map for V has coefficients `2^S/b` and `-d/b`,
where the denominator b=3^r_V is invertible modulo m. Its being the identity
means `b-2^S=0` and `d=0 mod m`. Formula (6) then makes both P and Q
divisible by m. This proves the two stated infinite arithmetic progressions:

\[
347\mid\gcd(P_k,Q_k)\ (k=7+86j),\quad
347^2\mid\gcd(P_k,Q_k)\ (k=5425+14878j).
\]

The finite state identities are exact Python computations with a written
induction; they are not separately formalized Lean theorems. The two
progressions are statements about fixed divisors. They do not say that
v_347(gcd) grows with k. Nor does finding a cycle modulo 347 imply the
claimed lift modulo 347^2 without the second checked state repetition.

Independently generated forward sums and the coprime split

\[
\gcd(P,a(b-2^S))=\gcd(P,a)\,\gcd(d,b-2^S)
\]

reproduce the full raw gcds at k=0,...,8:
`[3,1,1,1,1,1,1,347,1]`. Here `gcd(a,b-2^S)=1` since a is a power of 3,
and powers of two cancel from the second gcd because b-2^S is odd. The
full raw and reduced coordinate hashes, signs and bit lengths are checked
against the pinned artifacts. k=9 was not computed. The all-k argument
does not extrapolate a gcd pattern from these nine samples.

## 8. Independent computational certificate proof

[referee_checks.py](phase13/referee_checks.py) imports only Python's standard
library. It neither imports a project implementation nor calls an optimizer.
For a supplied basis f=(u,v), g=(r,s), it verifies membership in the exact
cylinder and `|us-vr|=2^N`. The index argument proves that this is the
**whole** lattice, rather than just a sublattice containing the witness.
Every vector `(p,q)=alpha*f+beta*g` with `|p|<=B`, `1<=q<=B` satisfies

\[
|\alpha|\le\left\lfloor\frac{B(|r|+|s|)}{2^N}\right\rfloor,\quad
|\beta|\le\left\lfloor\frac{B(|u|+|v|)}{2^N}\right\rfloor.\tag{16}
\]

We enumerate the shorter complete **signed** coefficient interval. For each
coefficient we intersect the other coefficient's exact integer intervals
from the numerator bound and the **positive** denominator bound, and solve
the odd-q congruence. This is exhaustive, including zero coordinates and
negative basis entries. Absence of a vector at B=H-1 and a primitive actual
witness at H proves the exact minimum. It does not assume a reduction
invariant or a unique-if-exists reconstruction region. It also does not
trust or need the producer's floor-sum or positive-beta exclusion transcript.
The latter transcripts are additionally exercised by the implementation's
full validation suite, a separate check with a different trust route.

Backward rational branches independently reconstruct the cylinder from the
literal word; actual signed numerator iteration checks every reported bit
of every witness. A second reduced-Fraction implementation of T tests sign
normalization, odd scaling and nontrivial odd denominators. All 511 residues
through 8 bits compare complete coefficient coverage to a centered-residue
brute search. At N=11,12,13 a complete independent denominator search gives
respectively `(-3,1), (509,513), (509,513)` and heights 3,513,513.

The main full run verified all **1,691 baseline records in ten families**,
all **24 overnight records**, and all **16 intermediate transitions**.
It also reconstructed shadows through k=8 with the forward/split-gcd route.
For the large records the shorter coefficient cap in (16) is 0 or 1, so
the completeness check is particularly small even though the integers are
large. Every transition failure was found by actual numerator iteration,
including its exact failing numerator and endpoint heights, rather than
accepted from a replay-summary Boolean.

| precision | independently checked exact-height bit length |
|---|---:|
| 87091=L_5 | 35217 |
| 87092=L_5+1 | 51875 |
| 522547=L_6 | 211281 |
| 522548=L_6+1 | 311267 |

These integers are bit lengths, not numerical values of H. The witnesses at
L_5 and L_6 also match the independently constructed reduced shadows. No
large-N optimizer was rerun; the exact certificates were re-proved using
(16), which suffices for mathematical minimality.

Six small corrupted witness/cylinder/basis cases and one corrupted large
basis are rejected. The checker also independently falsifies nondecreasing
maximal plateau widths: width 3 at 87096 is followed by width 1 at 87099.
The width-one plateaux at 87099 and 87102 have different selected-basis
updates `[[2,0],[-1,1]]` and `[[2,0],[1,1]]`. These are statements about
the stored algorithm-selected bases, not invariants of all lattice bases.
The full width chain is `2,2,3,1,2,1,1,5,3,1,3,2,2,1,1,2`.
They supply exact hostile controls, not a replacement transition law.

### Provenance defect in the supplementary handoff

The actual height file has 24 records, 8,027,076 bytes, SHA-256
`08bcbb623aee8fd0bf8d6e6bcf919feed9e0cf171e2dafcb5ce89afbfc6c74a3`.
The two transition segments have 11 and 5 records. The current inventory
and transition replay refer to those final artifacts.

Both `overnight-summary.md` **and** `overnight/checkpoint-audit.json` describe
the preceding **23/15** checkpoint. The latter still claims height hash
`49b40df1...`, second-segment size 175,401 instead of 219,248, and an older
smoke hash. Its recorded entry head is `bcfc2a7...`, not the final head.
It cannot serve as the final-head preservation audit. This second stale
artifact was not identified in the issue's warning about the summary.

The final stored `smoke.log` itself contains 24 height checks, 16 transition
checks and exit 0, at 464.54 seconds and peak RSS 102,832 KiB. The old
audit's 457.37-second/23/15 smoke is a different run. The journal's final
smoke/preservation continuation is also not a completed final audit. The
referee leaves these files untouched and records the inconsistency here.
**FAIL if the summary/audit are interpreted as final-head provenance;
no failure of the independently checked mathematical certificates.** Before
any integration of the overnight material, regenerate or explicitly label
both historical snapshots and reconcile the final journal status.

Python integer arithmetic, the interpreter and hardware remain part of the
computational trust boundary. Hashes bind bytes and aid provenance; they
do not prove the formulas or minimality. None of these finite samples
establishes a limiting exponent, gcd growth or completeness of a dense
large-N profile. The main asymptotic proof did not use the samples.

## 9. Exact Lean statement and axiom audit

All newly exported declarations were read, including their proof bodies,
then checked against the independently derived mathematics above. The
machine-readable [inventory](phase13/referee/lean-statements.json) records
the **exact source header**, fully qualified name, source line, source hash
and actual foundation list for each one. The compiler fixture
[Declarations.lean](phase13/referee/Declarations.lean) checks all 60 names
with implicit arguments exposed. A separate
[Signatures.lean](phase13/referee/Signatures.lean) restates the substantive
interfaces and contains actual negative-p, q=5, negative-q and height
controls. It contains only anonymous examples, adding no public library API.

Here is the per-declaration interpretation. In the tables **R** means the
exact namespace `CollatzLab.RationalHeight`, **F** means
`CollatzLab.FrontierHeight`. All displayed free parameters are universally
quantified, and implicit hypotheses remain required. `v` is an arbitrary
Boolean word; `Prefix(q,p,v,n)` uses the **q,p** order. Each row is **PASS
for the stated proposition**, with limitations explicitly retained.

| R declaration | Proposition/definition and required hypotheses | Semantic assessment |
|---|---|---|
| `Prefix` | For all j<n, `seedParity q p j=bit(v j)` | Finite predicate; does not itself assert q odd or positive. |
| `InLattice` | `2^n` divides `p-A*q` | No parity, primitive or positivity restriction in the lattice itself. |
| `height` | `max p.natAbs q.natAbs` | Correct symmetric signed norm; equals issue norm for q>0. |
| `odd_cancel` | Odd integer d and `2^n | d*x` imply `2^n | x` | Includes negative d; excludes even cancellation. |
| `parity_cross_iff` | Odd q,s: `p%2=r%2` iff `2 | ps-rq` | Actual first parity, both signs. |
| `cross_step` | Odd q,s and equal first parity: some odd c satisfies `2*D_next=c*D` | c is 1 or 3; exact integer identity. |
| `cross_step_dvd` | Same hypotheses: divisibility of D by `2^(n+1)` iff next D by `2^n` | Correct one-bit loss and odd cancellation. |
| `prefix_cross_iff` | All n,p,q,r,s; odd q,s: equal n parities iff `2^n | ps-rq` | Genuine finite isometry; no positive denominator assumption. |
| `cylinder_iff` | A actually realizes v for n bits with denominator 1; q odd | `Prefix q p v n` iff `InLattice A n p q`. |
| `lattice_representation` | All A,n,p,q: membership iff `p=2^n*k+A*q` for some integer k | Full lattice, unrestricted q. |
| `lattice_determinant` | `2^n*1-0*A=2^n` | Exact basis determinant identity, not a general abstract lattice theorem. |
| `divide_odd` | Odd d and `(dp,dq)` in the cylinder imply `(p,q)` in it | Preserves all n bits of congruence. |
| `residue_exists` | Every v,n has A in `[0,2^n)` with `Prefix 1 A v n` | Explicitly nonvacuous even for n=0. |
| `residue_unique` | Two such centered nonnegative residue representatives are equal | Requires both range and actual-prefix premises. |
| `residue` | Classical choice from `residue_exists` | Specification, not an executable reconstruction algorithm. |
| `residue_spec` | Range and actual-prefix properties of that choice | Justifies use in the bridge. |
| `parity_lattice_iff` | Every v,n,p,q with q odd: Prefix iff congruence to `residue v n` | Correct q,p order and finite quantifiers. |
| `minimum_exists` | Least natural height over pairs with q>0 odd and Prefix | No gcd restriction; next theorem proves it automatic at minima. |
| `H` | Classical choice of that least height | Defines the intended finite minimum, not a heuristic score. |
| `H_spec` | An admissible pair attains H, and H bounds below every admissible pair | Attainment and minimality both present. |
| `H_mono` | n<=m implies H(v,n)<=H(v,m) | Nested finite prefixes; all v. |
| `H_positive` | `1<=H(v,n)` | Positive denominator prevents zero height. |
| `H_zero` | H(v,0)=1 | Empty prefix has the correct boundary value. |
| `H_centered_bound` | H(v,n+1)<=2^n | Correct N>=1 formulation of the universal signed upper bound. |
| `minimizer_primitive` | q>0 odd, Prefix, and height=H imply `p.gcd q=1` | Bridges unrestricted pair minimum to issue's reduced minimum. |
| `height_bounds` | `absInt p` and `absInt q` are at most height | Both signs; not an assertion p>=0. |
| `cross_height_bound` | All four signed integers: `absInt(ps-rq)<=2hh'` | No unjustified cancellation or sign restriction. |
| `same_prefix_height_separation` | Odd q,s, both Prefix, and `ps!=rq` imply `2^n<=2hh'` | Nonzero cross product is an explicit, substantive premise. |
| `bounded_height_unique` | Odd q,s; shared Prefix; both heights<=B; `2B^2<2^n` | Concludes equal rational value `ps=rq`, not equal unreduced pairs. |
| `shadow_crossing` | Odd q; matches n bits; fails exactly the next bit | `2^n<=2*height(p,q)*H(v,n+1)`; no inferred infinite realization. |
| `bounded_iff_rational` | Eventual bound `exists B,K, forall N>=K` iff some pair realizes all v | RealizesWord includes positive odd q; no periodicity conjecture. |

| F declaration | Proposition/definition and required hypotheses | Semantic assessment |
|---|---|---|
| `inflate` | Literal mu-image at parent n/6 and column n%6 | Both image words and zero-based columns verified. |
| `baseShadow` | w(n) for n<3, true afterwards | Exactly `100` followed by constant ones. |
| `shadow` | kth iterate of inflation of baseShadow | A word, not an assumed rational approximation. |
| `matchLength` | Starts 11; successor `6L+1` | Exact prefix length, not failing-prefix length. |
| `fixed_inflate` | Inflate(w)=w at every n | Uses one-start frontierSix. |
| `matchLength_formula` | For every k, `5L_k+1=56*6^k` | Integer equality; division form needs the elementary rearrangement. |
| `inflate_first_failure` | Arbitrary v matches before m and differs at m | Exact new mismatch `6m+1`, including the shared first column. |
| `shadow_first_failure` | Every k: agreement before L and disagreement at L | Both halves, no finite-k cutoff. |
| `inflate_period_after` | Period s after u for arbitrary v | Period 6s after 6u after inflation; no minimality claim. |
| `shadow_period_after` | All k,n>=3*6^k: shadow(n+6^k)=shadow(n) | Gives a preperiod and a period, including k=0. |
| `shadow_tail_initial` | j<6^k: shadow(3*6^k+j)=w(j) | A single period agrees with V; does not say its entire tail equals w. |
| `periodic_seed` | Arbitrary s>=1 periodic v, with `2^s<3^weight(v,s)` | Whole-itinerary seed `(-offset,3^weight-2^s)`; gap enforces positive q. |
| `prepend_seed` | A positive-odd-denominator rational realizes the whole shifted tail v(u+j) | Exact pair `(2^u*p-offset(v,u)*q,3^weight(v,u)*q)` realizes all v. |
| `local_pressure` | All blocks n and 0<=t<6 | `2^t<=4*3^weight` for the literal partial image. |
| `prefix_pressure` | Every n>=0 | Global w-prefix inequality (8), not just substitution powers. |
| `offset_of_pressure` | Any v satisfying the pressure premise at every n | `offset(v,n)<=2n*3^weight(v,n)` for every n. |
| `power_gap` | Every k | Strict `2^(6^k)<3^weight(w,6^k)`; k=0 included. |
| `shadowNum` | Signed integer P in (6) using prefix offsets | Explicit negative numerator, not reduced by definition. |
| `shadowDen` | Integer Q in (6) using prefix weights | Explicit raw denominator; positivity/oddness proved by realization. |
| `shadow_realized` | Every k: RealizesWord(P,Q,shadow) | Includes Q>0 odd and equality at every index. |
| `shadow_prefix` | Every k: Prefix(Q,P,w,L_k) | Correctly reverses q,p for finite predicate. |
| `shadow_failure` | Every k: actual seedParity(Q,P,L_k) differs from w(L_k) | Does not rely only on a word-level mismatch. |
| `shadow_weight_sum` | Integer equality `7*(r_U+r_V)=20*6^k-6*(-1)^k` | Integer sign oscillation, no natural-number truncated subtraction. |
| `shadow_height_bound` | Every k: raw height(P,Q)<=14*6^k*3^(r_U+r_V) | Retains the explicit raw pair; reduced pair is no larger. |
| `H_shadow_upper` | Every k: H(w,L_k)<=same T | Actual admissible witness; no assumed lattice short-vector existence. |
| `H_shadow_crossing` | Every k: `2^L<=2*T*H(w,L+1)` in Int | Correct strict failure index and exact power of two. |
| `H_after_shadow` | All k,N with L_k<N | Same inequality with H(w,N); monotonicity used in the right direction. |
| `H_eleven` | H(w,11)=3 | Kernel proof with actual negative-p witness and lower bound. |
| `H_twelve` | H(w,12)=513 | Kernel proof with q=513 odd; exact lower bound, not a test output imported as an axiom. |

The audit has **31 R declarations + 29 F declarations = 60**, and exactly
**653** records with the **593 baseline names preserved in order**.
All full audit records were rechecked both by the repository parser and
the reviewer-owned [audit_statements.py](phase13/referee/audit_statements.py).
The only permitted foundations are `propext`, `Classical.choice`, `Quot.sound`.
Among the 60 new declarations, nine depend on no axioms, 27 use propext and
Quot.sound, and 24 additionally use Classical.choice. There is no sorryAx,
unproved custom assumption or imported external irrationality axiom.
All 85 trusted Lean source files were scanned for the prohibited escapes.
The new library modules contain no redefinition of numStep/numIter/seedParity
or RealizesWord. `Word.lean` and `FrontierSix.lean` are unchanged from base.

Compilation establishes the exact formal propositions above. It does not
turn the real-logarithm proof, strict all-k minimum induction, modular-cycle
induction, finite counting refinement or external literature into Lean
theorems. We did not add a ceremonial real-limit formalization or enlarge
the trusted axiom list. The separate source/body audit and independent
proof establish the semantic connection being claimed.

## 10. Finite numerator distinctness and the alternative weaker bound

The author's secondary drift route is valid with its **finite** distinctness
premise; infinite word aperiodicity alone is insufficient for a finite seed.
For example -3 matches the first 11 symbols of this aperiodic w, but its
states at times 3 and 4 already both equal -1.

We independently verify the marker argument. For every t, the positions
`36t+1,36t+2` are both zero, since their parent at 6t is a forced one.
Every interval of 37 consecutive positions contains such a pair. If a match
at shift m not divisible by 6 had length at least 37, one of these two zeros
would be sent to a forced-one column: for residues 1 through 5 use respectively
the second, first, first, second, first zero. Contradiction. When 6 divides m,
the identity column 5 passes at least floor(length/6) consecutive matched
parent symbols to shift m/6. Strong induction on m now proves that every
match at positive shift m has length **less than 37m**.

If a rational seed matches N>=38J symbols and states at 0<=i<j<=J were
equal, determinism would give equal factors at shift m=j-i of length
N-j>=37J>=37m. This contradicts the word bound. Thus these J+1 states
are distinct, with every sign and denominator kept fixed.

De Jesús's finite excursion estimate, attributed to the original below,
gives `max_(i<=J)|p_i|<=H*(1+J/2)*2^Omega_J`. Take J=4S, N=152S,
S=6^k. All length-S factors in these positions occur inside the matched
prefix. If the states fit in `[-2^(S-1),2^(S-1))`, their distinctness and
the finite parity equivalence make S-factor complexity at least 4S+1,
contradicting the known global upper bound P_w(S)<=4S. Therefore

\[
\log_2 H_{152S}\ge S-1-\log_2(1+2S)-\Omega_{4S}.
\]

The exact prefix-discrepancy bound implies
`Omega_(4S)=4gS+O(log S)`, with `g=(5/7)log2(3)-1>0`.
Indeed `r_n=(5/7)n+O(log S)` uniformly for n<=4S; subtracting two such
drifts proves the upper estimate, and the entire interval gives the lower
estimate. Hence this route yields only `(1-4g)/912` as a uniform liminf
lower bound after the factor-six scale interpolation. Its numerator is
positive, e.g. `3^4<2^7` implies g<1/4. This is weaker than (13).
It is a written application of a known confinement/counting mechanism,
with a correct extra finite distinct-state argument, not a new infinite-orbit
criterion and not a separate Lean theorem.

The conditional two-shadow refinement also survives scrutiny. Suppose
`log h_k/L_k -> c_*`, which is not proved by raw gcd samples. On
`L_(k-1)<N<=L_k`, a minimum either equals y_k, in which case its normalized
height is at least c_*-o(1), or is distinct. The latter case has both
`log H_N >= ((1-c_*)/6-o(1))*L_k` from y_(k-1), and
`log H_N >= N-(c_*+o(1))*L_k` from y_k. If x=N/L_k, minimize
`max(a/x,1-c_*/x)`, with `a=(1-c_*)/6`. The crossing x=a+c_* lies in
(1/6,1), and yields `B>=(1-c_*)/(1+5c_*)`. This remains **CONDITIONAL on
the stated shadow-height limit**, not an unconditional improvement. Gcd
control alone would still not determine the exact global B.
