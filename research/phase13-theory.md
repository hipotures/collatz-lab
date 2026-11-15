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
