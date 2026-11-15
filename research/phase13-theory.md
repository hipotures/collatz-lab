# Phase 13: exact heights and quantitative research

Issue [#28](https://github.com/hipotures/collatz-lab/issues/28).
The derivation in Sections 1–3 was written before implementing the new Lean
proofs or either reconstruction algorithm. Status labels distinguish written
proofs, kernel verification and finite evidence. Provenance is in
[the source matrix](phase13-prior-art.md).

## 1. Independent finite parity derivation

Write `T(p/q)=p'/q`, where q is odd of either sign. If p is even,
`2p'=p`; otherwise `2p'=3p+q`. For a prescribed prefix v of length N, let
`r_N` count its ones and define `c_0=0`,

```
c_(n+1) = 3*c_n + 2^n  if v_n=1,
          c_n            if v_n=0.
```

Actual iteration gives `2^N p_N=3^r_N p+c_N q`. Each inverse branch is
`y -> 2y` or `y -> (2y-1)/3`. Reversing N branches from zero gives
`-c_N/3^r_N`. Therefore the cylinder residue is

```
A_N = -c_N * (3^r_N)^(-1) mod 2^N,   0<=A_N<2^N.
```

Here the inverse is modulo a power of two, and always exists. This establishes
existence but the converse deserves proof: if two odd-denominator seeds have
the same first parity, their next cross product is the initial cross product
divided by 2, multiplied by 1 or 3. Conversely divisibility of the initial
cross product by 2 forces equal first parities, and divisibility by `2^(n+1)`
transfers to divisibility by `2^n` after the first step. Induction gives

```
(forall j<N, seedParity(q,p,j)=seedParity(s,r,j))
    iff 2^N divides p*s-r*q                         (q,s odd).
```

Set `(r,s)=(A_N,1)`. This is the exact cylinder/lattice bridge, including
negative p and signed odd denominators. It uses the actual accelerated map;
`seedParity(q,p,j)` and `RealizesWord(p,q,v)` have different argument order.
Replacing `(p,q)` by `(-p,-q)` preserves all parities by the same cross-product
identity; q can therefore be normalized positive. Finite realizability says
nothing about an infinite rational realization.

## 2. Minimum and elementary safeguards (written proofs)

Let `M=2^N`. The congruence lattice is exactly
`{k*(M,0)+q*(A_N,1): k,q in Z}`, of determinant M. For N=0 the modulus
is 1 and `H_0=1`. For N>=1 choose q=1 and the centered residue p in
`[-M/2,M/2]`, including the positive endpoint when A_N=M/2. Hence
`1<=H_N<=2^(N-1)`; a nonempty set of natural heights has a least member.

If an admissible pair has common factor d>0, then d is odd because q is
odd. From `M|d*(p'-A_N q')` and `gcd(d,M)=1` cancel d. Division gives
another admissible pair and cannot increase height. A minimizing pair must
be primitive; the p=0 case reduces to `(0,1)`. Dividing an even denominator
by 2 does **not** preserve precision: `A=M/2` has the lattice vector `(0,2)`
but `(0,1)` is outside the cylinder. All odd q have centered numerator
magnitude M/2, so its exact height is M/2. This disproves a uniform
`O(sqrt(M))` existence bound over all residues, not just a particular constant.

Nested parity cylinders give monotonicity. If distinct rational values of
heights at most B lie in a cylinder, their nonzero integer cross product is
divisible by M and has magnitude at most `2 B^2`. Thus `M<=2 B^2`.
This is known bounded reconstruction uniqueness, not existence.

If one infinite rational seed exists, its height bounds every H_N. Conversely
if H_N is eventually bounded by B, nested finite sets of admissible pairs
inside `[-B,B] x [1,B]` have nonempty intersection. Explicitly, each pair that
fails the infinite word has a first failing index; taking the maximum of
these finitely many indices contradicts nonemptiness of a later cylinder.
One pair therefore realizes the whole word. No Periodicity Conjecture is
used, and the word itself need not be periodic for this equivalence.

## 3. Analytic questions after the source gate

Put `x=Phi(w)` irrational, and define the height-based 2-adic exponent

```
mu_2(x) = limsup_(H(p/q)->infinity) v_2(x-p/q) / log2 H(p/q)
```

over reduced fractions with positive odd denominator. Then
`liminf_N log2 H_N/N = 1/mu_2(x)`, with `1/infinity=0`.
For one inequality, a fraction of precision t has `H_t<=H(p/q)`.
For the other, an exact minimizer at N has precision at least N. Irrationality
ensures all these precisions are finite and minimizing heights tend to infinity.
These two inequalities also handle subsequences and plateaus; they do not
assert a limit of the height profile.

Klapper (2007), applied to the **binary expansion of x**, gives the full
accumulation interval `[B,1-B]`. In particular `mu_2>=2`, and existence of
a profile limit would force `B=1/2`, `mu_2=2`. Candidate-specific lower
bounds for B require a finite irrationality measure or other quantitative
structure. Aperiodicity of the parity word alone is insufficient to invoke
this digit theorem; irrationality of x must first be established by the known
Phase 12 reduction. We do not import any external irrationality assertion as
a Lean axiom.

The two planned analytic routes are (A) finite drift/confinement and actual
distinct-state bounds, and (B) exact inverse-branch products under the literal
unequal-weight substitution. Status and obstructions will be updated after
certified experiments. No numerical exponent is assumed.

## 4. Exact algorithms and independently checkable minimality

The optimized route replicates the published odd-denominator adaptive method.
Its basis has one even-coordinate vector f and one odd-denominator vector g.
The reference route instead counts a rectangle and binary searches its size.
Neither algorithm imports the other.

For `B>=0`, put `t=(B+1)//2` and define
`S(t,m,a,b)=sum_(i=0)^(t-1) floor((a*i+b)/m)`. The number of pairs in the
height-B box with positive odd q is exactly

```
C(B) = S(t,M,2*A,A+B) - S(t,M,2*A,A-B-1).
```

Indeed q=2i+1 and the number of integers k with `-B<=A*q-M*k<=B`
is the difference of those two floors. This counts all admissible vectors,
including nonprimitive ones, so zero is a valid no-smaller-height certificate.
It never relies on reconstruction uniqueness or an unconstrained shortest
vector.

For signed a,b, write `a=q_a*m+r_a`, `b=q_b*m+r_b`, with remainders in
`[0,m)`. Their contributions are `q_a*t*(t-1)/2+q_b*t`. For normalized
a,b, put `y=a*t+b`, `u=y//m`, `v=y mod m`. If y<m the residual sum is zero;
otherwise

```
S(t,m,a,b) = S(u,a,m,v).
```

To prove this identity, count integer points `(i,j)` with `0<=i<t` and
`1<=j`, `m*j<=a*i+b`. For `1<=j<=u` the number of i is
`t-ceil((m*j-b)/a)=floor((m*(u-j)+v)/a)`. Summing proves the formula;
the possible last zero contribution is harmless. The modulus strictly
decreases. Signed normalization and this identity telescope to an exact sum.

A certificate records the quotient pairs in this finite Euclidean chain for
each floor sum at B=H-1. The independent verifier reconstructs all states,
checks remainder inequalities, the final stopping condition and both totals.
Together with an actual odd primitive witness at height H and its numerator
iteration, equality of the two totals proves exact minimality. The verifier
imports neither reconstruction implementation and reconstructs A by **reverse
rational inverse branches**, whereas the producer uses forward affine offsets.
This computational certificate proof is written mathematics/Python exact
arithmetic, not a claim that the whole solver is Lean verified.

## 5. Route B: an infinite family of substituted rational shadows

**Kernel-verified shadow construction and finite integer inequalities,
independently replicated at five literal levels.** The logarithmic deductions
in Section 6 remain written mathematics. This is an
explicit specialization of the known inverse-parity/periodic-shadow method,
not a new approximation technique. The exact numerical specialization was
not found in the sources checked; mathematical priority is unverified.

Let mu be the literal Phase 12 substitution, `S_k=6^k`, `e_k=(-1)^k`, and

```
U_k = mu^k(100),    V_k = mu^k(1),    z_k = U_k V_k V_k ...,
L_k = (56*S_k-1)/5.
```

The base shadow `100111...` is the actual itinerary of -3/1. It agrees with w
at indices 0..10 and disagrees at 11. The two mu images agree exactly in
their first position before differing in the second. Thus, if two words first
disagree at index m, their images first disagree at `6m+1`. Induction proves
that z_k and w agree at exactly their first L_k positions, since
`L_0=11`, `L_(k+1)=6*L_k+1`. The predicted first failing prefix lengths are
therefore **12,68,404,2420,14516,...**. This is an exact word argument, not a
fit to the height data. The preperiod and period lengths of z_k are 3S_k,S_k;
they are not asserted to be minimal.

For a finite word X let `a_X=3^r_X`, `c_X=offset(X)`, `m_X=2^|X|`. Put
`a=a_U`, `b=a_V`, `c=c_U`, `d=c_V`. The periodic tail seed is `-d/(b-2^S)`;
reversing U gives the rational seed

```
P_k = -(2^(3*S)*d + c*(b-2^S)),
Q_k = a*(b-2^S),     y_k=P_k/Q_k.
```

The denominator is positive odd. For k=0 this is checked directly. For k>=1
each six-bit image has at least four ones, so `b>=81^(S/6)>64^(S/6)=2^S`.
The inverse branches prove that y_k realizes the **entire** periodic shadow
z_k. The normalized reduced seed has the same itinerary and no larger height.

Here is a fully elementary bound on its real height, avoiding any transfer
of a real limit to Q_2. Every aligned prefix n=6t+s of w has at least
`4t+tau_s` ones, where `tau=(0,1,1,1,2,3)` for s=0..5. The six checks
`2^s<=4*3^tau_s` and `64<=81` give

```
2^n <= 4*3^r_n  for every n>=0.
```

Induct in the offset recurrence to obtain `c_n<=2*n*3^r_n`. At a zero the
left side is unchanged. At a one, `3*c_n+2^n <=(6n+4)*3^r_n`, which is at
most `2*(n+1)*3^(r_n+1)`. Both U_k and V_k are actual prefixes of w. Hence
`c<=6S*a`, `d<=2S*b`, `2^(3S)<=4a`, and `0<b-2^S<b`. Consequently

```
height(y_k) <= max(|P_k|,Q_k) <= 14*S_k*3^R_k =: T_k,
R_k = r_(U_k)+r_(V_k) = (20*S_k-6*e_k)/7.
```

The last count follows from the exact incidence identity already proved in
Phase 12: `7*r_U=15S-8e`, `7*r_V=5S+2e`. This uses unequal image weights
faithfully. The proof supplies actual rational witnesses, not an assumed
short vector. In particular

```
H_(L_k) <= T_k,
2^L_k <= 2*T_k*H_(L_k+1).
```

For the second inequality, any rational seed matching w for L_k+1 bits is
different from y_k, since y_k fails at index L_k. Their cross product is a
nonzero multiple of `2^L_k`. Keep the two heights in the cross-product bound;
do not eliminate them as in the Phase 12 seed-free no-go.

## 6. Route A: exponent transfer, lower bounds and nonconvergence

**Written deductions from Section 5 and standard determinant approximation.**
Set

```
c = (25/98)*log2(3) = 0.40432716855... < 1/2.
```

The explicit T_k satisfies `log2(T_k)/L_k -> c`. The preceding inequalities
therefore prove for the actual Phase 12 word:

```
liminf log2(H_N)/N <= c,
limsup log2(H_N)/N >= 1-c.
```

**Thus the normalized height profile does not converge.** In particular, the
tempting limit 1/2 is false for this word. This conclusion follows directly
from two exact subsequences; it does not assume Klapper's theorem or infer
anything from the 16,384-bit experiment. It does not determine either extremum.

There is also a weak but nontrivial bound at **all** sufficiently large N.
Choose the unique k with `L_k<N<=L_(k+1)`. The shadow y_k is different from
every seed matching N bits, so

```
H_N >= 2^L_k / (28*S_k*3^R_k),  for L_k<N<=6*L_k+1.
```

This explicit finite inequality implies

```
(1-c)/6 <= B=liminf log2(H_N)/N <= c.
```

The lower endpoint is approximately 0.09927880524. Combined with the **external
known** Klapper result, the limsup is 1-B, lying between `1-c` and
`1-(1-c)/6`. In the height-exponent convention of Section 3,

```
1/c <= mu_2(Phi(w)) <= 6/(1-c).
```

The upper bound here is an explicit, weak shadow-based approximation measure,
with a computable finite threshold in the displayed inequality; its exact
value is not asserted optimal. It is a known-method deduction, not a new
general irrationality-measure theorem. The separate code checks exact integer
inequalities and first failures; no logarithm is used to certify a height.

**A second route within A: finite drift/confinement.** The known De Jesús
growth estimate retains H and bounds the first J numerators by
`H*(1+J/2)*2^Omega_J`. To use the global `P(6^k)<=4*6^k` bound for finite
shadows, infinite aperiodicity does not suffice: the first J states must be
proved distinct while N is still finite. A marker/descent argument gives a
useful sufficient condition. Any equal factors at shift m>0 have matching
length `<37*m`: a match of length >=37 contains a forced-zero marker pair
at `36t+1,36t+2`; nonzero shift residues modulo 6 send one to a forced one.
For m divisible by 6, identity column 5 passes at least floor(length/6)
matched parents to the smaller shift m/6. Strong induction proves the bound.
Hence a seed matching N>=38J symbols has distinct states at times 0..J.

Taking J=4S and N=152S, finite confinement plus the known complexity bound
forces roughly `log2 H_N >= (1-4g)*S-O(log S)`, where
`g=(5/7)*log2(3)-1`. The coefficient is positive. Between these sparse scales
this would yield only `(1-4g)/912` as a liminf lower bound, much weaker than
the explicit-shadow lower bound above. This route was investigated and its
finite distinctness gap addressed, but it is **not** the headline or a new
counting mechanism. No assertion about infinite rational orbit distinctness
is silently applied to a finite approximant.

## 7. Lattice dynamics and rigorous limitations

The finite inverse sum gives `A_(n+1)=A_n+epsilon_n*2^n`, with epsilon in
{0,1}; testing the next actual parity selects the lift. For a word concatenation
UV, its rational inverse map is `F_U(F_V(y))`. At level one the exact matrices
are

```
B_1 = [[64,-179],[0,81]],    B_0 = [[64,-211],[0,243]].
```

At successive levels,
`B_1' = B_1 B_0 B_0 B_1 B_1 B_1`, `B_0'=B_1^5 B_0`. These are exact
noncommutative product recurrences, not a scalar Mahler equation. The
upper-right entry of `B_1 B_0-B_0 B_1` is -28454. Replacing both lower-right
entries by 81 already gives the wrong 12-bit residue on source prefix 10;
the precise two residues are in `analytics.json`. A first draft guessed an
offset from an external table with different bit conventions; independent
iteration rejected it. The correct offset 179 is now kernel/independently
checked, and the incorrect value is not used in any theorem.

Remaining obstructions are substantive. A recurrence for exact inverse maps
does not by itself control odd gcd cancellations or other competing rational
approximants. Section 8 upgrades shadow minimality to an all-level written
theorem and disproves the tempting raw-coprimality conjecture. It still does
not show that no other subsequence has a smaller exponent.
Generic whole-lattice short vectors can have even denominators. Neither
automaticity of w nor classical digit-complexity theorems for w determine the
complexity of the different digit sequence of Phi(w). Known Mahler measures
cannot simply be transferred across this unequal-weight substitution.

The strongest unresolved question is now the **exact value of B**, plausibly
the shadow bound c but unproved. The existence of a limit is no longer an
open conjecture under the written proof above. No claim of transcendence,
novelty or an optimal measure is made here.

## 8. Exact subsequence minima and a modular cancellation obstruction

**Written mathematical deductions with exact finite arithmetic certificates;
the asymptotic and modular-cycle conclusions are not separate Lean theorems.**

The reduced fractions y_k in Section 5 attain H_(L_k) for **every k**.
This requires more than observing five matching minima. From the count formula
`R_(k+1)<=6*R_k+6`, put `D_k=14*S_k`. Since D_k>=14,

```
T_(k+1) <= 4374*D_k*(3^R_k)^6 <= D_k^6*(3^R_k)^6 = T_k^6,
```

where `4374=6*3^6<14^5`. The exact finite base check gives
`2*T_2^2<2^L_2` (S_2=36, R_2=102, L_2=403). If that strict inequality
holds at k, then

```
2*T_(k+1)^2 <= 2*T_k^12 <= (2*T_k^2)^6
               < 2^(6*L_k) < 2^(6*L_k+1) = 2^L_(k+1).
```

Induction proves it for k>=2. Any smaller rational in the same L_k cylinder
would have a nonzero cross product of magnitude at most `2*T_k^2<2^L_k`,
which is impossible. Equal rational values have the same primitive positive
denominator representation. The two early reduced shadows also satisfy
`2*height(y_k)^2<2^L_k`, checked exactly at k=0,1. Therefore

```
H_(L_k) = max(|P_k|,Q_k) / gcd(|P_k|,Q_k)  for every k>=0.
```

This is an explicit infinite subsequence formula with a remaining integer gcd,
not an assertion that its normalized logarithm has limit c. Its general
uniqueness mechanism is classical rational reconstruction, already audited.

The first seven positive levels disprove the simplest way to drop the gcd:
for k=1..6 it is 1, but **gcd(|P_7|,Q_7)=347**. Here S_7=279936 and
L_7=3135283. `verify_modular.py` computes the full integer matrices through
level 7, replicates the literal Fraction construction at levels 0..4, and
records exact gcds plus coordinate hashes in `modular.json`. This is a
bounded computation, not a large-N engine scan.

There is a stronger all-level divisibility consequence. Modulo any odd m
coprime to 3, the inverse image maps are affine maps on Z/mZ with initial

```
f_0(x)=2*x,   f_1(x)=(2*x-1)/3.
```

Their substitution update is exactly the noncommutative product of Section 7.
The following finite equality certificates are reproduced independently:

| Modulus m | Initial repeated level a | Period t, with state(a+t)=state(a) | Level b inside the cycle with f_1=identity |
|---|---|---|---|
| 347 | 1 | 86 | 7 |
| 347^2=120409 | 62 | 14878 | 5425 |

Each state is the pair of affine coefficient pairs for f_0,f_1; all exact
coefficients at the three relevant points are in `modular.json`. A deterministic
recurrence and one repeated state prove state periodicity from a, by induction;
no extrapolation from a plot is involved. Thus f_1 is the identity modulo m
at every level b+t*j, j>=0. Its inverse matrix has `c_V=0` and `3^r_V=2^S`
modulo m. Consequently both raw shadow coordinates P_k,Q_k are divisible by m.
In particular **347 divides both at every k=7+86j**, and **347^2 divides both
at every k=5425+14878j**.

This is an explicit certified obstruction to raw coprimality, using a known
finite-state congruence mechanism. No priority claim is made for the particular
cycles. Constant-size common factors, even at infinitely many levels, do not
prove cancellation exponential in S_k or change an exponent. The possibility
`log2 gcd(|P_k|,Q_k)=o(S_k)` remains unresolved, as does control of all other
prefix lengths. No corresponding claim about unrestricted Collatz orbits is
implied by these shadow calculations.

There is a useful **conditional** refinement of the lower bound. Suppose
`log2(height(y_k))/L_k -> c`; the unresolved subexponential-gcd condition
would imply this, since the raw denominator already has exponent c. Put
`a=(1-c)/6`. For `L_(k-1)<N<=L_k`, a minimum r either equals y_k, giving
`log2(H_N)/N>=c-o(1)`, or differs from y_k. In the latter case the two
determinant comparisons with y_(k-1) and y_k give

```
log2 H_N >= max((a-o(1))*L_k, N-(c+o(1))*L_k).
```

Writing x=N/L_k, the minimum of `max(a/x,1-c/x)` occurs at x=a+c.
Consequently the conditional conclusion is
`B>=(1-c)/(1+5c)=0.19713587687...`, still below c. This known two-approximant
principle shows precisely why controlling the gcd alone would not determine
the global B: intermediate best approximants also need control. This is a
written conditional theorem, not an unconditional improvement or Lean result.

## 9. Exact verification boundary

`RationalHeight.lean` and `FrontierHeight.lean` export 60 new audited declarations.
The exact CI manifest has 653 entries, preserving the 593 baseline names.
Separate `phase13/Signatures.lean` examples state the key interfaces afresh.

| Claim | Evidence |
|---|---|
| Signed finite parity iff cross-product / residue congruence | **Lean kernel**, actual numStep/numIter/seedParity semantics |
| Minimum exists, every minimizer is primitive, monotonicity, centered bound | **Lean kernel** |
| Bounded heights iff an infinite rational realization; height separation | **Lean kernel**, no Periodicity Conjecture premise |
| All-level actual rational shadows, exact first mismatch, pressure and weights | **Lean kernel** |
| H_(L_k)<=T_k and 2^L_k<=2*T_k*H_N whenever N>L_k | **Lean kernel** |
| H_11=3, H_12=513 | **Lean kernel**, plus independent exhaustive Python iteration |
| Exponent interval, nonconvergence, exact reduced-shadow minima for all k | **Written deductions** from the displayed finite theorems, not formal real-limit theorems |
| Modular cycle identities and full gcd computations through k=7 | **Exact independent Python certificates**, with written infinite-cycle deduction |
| B=c, asymptotic gcd size, no better intermediate approximants | **Open / conjectural**, no convergence claim |

The mathematical result is an attributed quantitative specialization
and repository formalization. It is not advertised as a newly discovered
irrationality or transcendence theorem.
