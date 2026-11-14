# Morphisms outside criterion (C): Phase 7 research

2026-11-14 UTC. **Primary target resolved in Lean:** no rational number with
positive odd denominator realizes either target, `1 -> 10, 0 -> 01` or
`1 -> 101, 0 -> 011`, any shifted tail, or an eventual shifted tail. The primary
target has two independent infinite proofs: contraction and Mahler forms.
Generic Theorem 8.1 is also kernel-checked.
No claim about Collatz or the general Periodicity Conjecture follows.

## Status and reproducible evidence

| Result | Status |
|---|---|
| Correct `10/01` fixed point and non-eventual-periodicity | Lean-kernel-verified |
| Uniformly contracting equal-weight blocks force any rational realization to have an eventually periodic itinerary | Lean-kernel-verified |
| `10/01` rational exclusion, all shifts and eventual shifted matches | Lean-kernel-verified |
| Both target Mahler equations and rational seed identities below | proven-by-algebra; finite integer identities are generic Lean theorems |
| 48 exact Padé rows, degrees 1–24; 8 modular checkpoints; signed small rational falsification | verified-for-finite-domain |
| `101/011` degree-2 periodic control and infinite contradiction | Lean-kernel-verified |
| Generic periodic-control certificate with freely chosen period | Lean-kernel-verified |
| Generic Theorem 8.1 under exactly H1–H3 and (C) | Lean-kernel-verified; see `lean-equal-weight-formalization.md` |

```text
python3 research/mahler-uncovered/verify_uncovered.py --check
cargo test --locked --test mahler_uncovered
lake build
lake env lean research/lean-audit/FamilyAudit.lean
```

The Python producer solves rational linear systems, normalizes primitive
pairs and evaluates the exact ledger. Rust independently reconstructs the
words from digit recurrences, checks all 48 residuals through coefficient
511, primitive content, leading coefficients, valuations and ledgers. It also
checks the seed identities against actual Collatz iteration at 32,64,128,256
bits and the selected pairs' exact form valuations at three tower levels.
The JSON explicitly labels everything finite; kernel proofs are in Lean files.

## 1. Primary target: the elementary invariant

Write `v` for the complement of the usual Thue–Morse word, starting at 1.
Literal substitution gives

```text
v(2n)=v(n),  v(2n+1)=1-v(n),  v(0)=1.
mu(1)=10, mu(0)=01;  L=2, r=1, A=4, B=3, c0=2, c1=1.
F(z)=z/(1-z^2)+(1-z)F(z^2).
F_2(4/3)=3*x(v)-6, or x(v)=2+F_2(4/3)/3.
```

The last identity follows from
`B*((B-A)*x+c0)=(B-A)*(c0-c1)*F_2(A/B)`. These are 2-adic evaluations;
the real power series at `4/3` does not converge and is never used.
`t=1,s=0,e=1,N=2`: (C) fails because `2^4<4^5`. The first prefix `10`
already crosses the coefficient threshold, so this word is not a survivor.

**Complete infinite proof of rational exclusion.** Suppose `p/q` realizes
`v`, with `q>0` odd and any integer `p`. Let `y_n=numIter q p (2n)`.
Both selected Collatz branches are exact integer divisions, and composing
them gives

```text
4*y_(n+1)=3*y_n+(2-v(n))*q.
```

Set `K=|p|+2q`. Inductively `|y_n|<=K`, because the forcing lies between
`q` and `2q` and `3K+2q<=4K`. All `y_n` are ordinary integers with the same
denominator `q`; hence two distinct block boundaries have equal numerators.
Determinism of `numStep` makes all subsequent states equal at that lag, so
the full parity word is eventually periodic. This uses discreteness of the
fixed-denominator lattice, not a conjecture about rational orbits.

For completeness, here is an independent aperiodicity proof. Suppose `d>=1`
is an eventual period from `M`. If `d` is even, applying the period equation
at even indices gives the strictly smaller eventual period `d/2`; descend
by strong induction. If `d=2h+1` is odd, applying it at `2n` and `2n+1` gives

```text
1-v(n+h)=v(n),  v(n+h+1)=1-v(n)   (n sufficiently large).
```

Thus consecutive symbols `v(n+h),v(n+h+1)` are equal. Take
`n=2M+h`; these indices are `2(M+h),2(M+h)+1`, whose symbols are
complementary. This is impossible for a binary symbol. Therefore no eventual
period exists, contradicting the rational recurrence above.

Every step is accepted by the kernel in `Subcritical.lean` and `ThueMorse.lean`.
There is no nonzero Mahler form or valuation assumption in this proof: bounded
integer states supply the contradiction. Separately proved binary recurrences
and the existing rational inverse branches yield all tails. The exact exports:

```lean
CollatzLab.no_rational_seed_realizes_thueMorse (p q : Int) :
  ¬ CollatzLab.RealizesWord p q
    (CollatzLab.Morphism.parityWord CollatzLab.Morphism.thueMorse)

CollatzLab.no_rational_seed_realizes_shifted_thueMorse :
  ∀ (t : Nat) (p q : Int),
    ¬ CollatzLab.RealizesWord p q
      (CollatzLab.shiftWord
        (CollatzLab.Morphism.parityWord CollatzLab.Morphism.thueMorse) t)
```

`no_eventually_shifted_thueMorse_itinerary` excludes agreement after arbitrary
finite orbit and word offsets `s,t`. Numerators may be negative, zero or
unreduced. `thueMorse_positive_prefix` independently checks the 32-symbol
integer witness 1895344877, which reaches 18996277; finite realizability and
infinite rational exclusion remain distinct.

## 2. General subcritical result (additional direction D)

The proof was generalized before specializing it. The exact generic export,
in `CollatzLab.Morphism`, is:

```lean
no_rational_seed_subcritical {L : Nat} (hL : 2 ≤ L) (M : Images L)
  (h1 : image M true 0 = true)
  (hw : weight (image M false) L = weight (image M true) L)
  (hBA : B M < A L)
  (haper : ¬ CollatzLab.EventuallyPeriodic (parityWord M)) (p q : Int) :
  ¬ CollatzLab.RealizesWord p q (parityWord M)
```

Aperiodicity is an explicit proved hypothesis in the Thue–Morse instance.
It has not been silently inferred for all distinct equal-weight images.
For general blocks, the forcing has magnitude at most `(c0+c1)*q`.
The elementary lemma `contracting_recurrence_bounded` handles every integer
`0<=B<A`, so no logarithms or limiting odd-step density are needed.
`bounded_blocks_periodic` needs boundedness only at block boundaries. This
criterion covers a different parameter region from the family proof.

## 3. Exact Padé search and independent falsification

Coefficients are listed in ascending powers. `M` is reduced maximum degree;
`c` is the first nonzero residual coefficient. The generic sufficient ledger
for such a pair is `2^(L*(L-1)*N) > m^((L-1)*M+L+e)`; coefficients contribute
a fixed norm, and the tower contributes `(2L)^k`, which must still be proved
negligible in an infinite argument.

| target | search degree | p0 | p1 | M | N | c | v2(c) | exact ledger |
|---|---|---|---|---|---|---|---|---|
| `10/01` | 1–2 | `[1]` | `[-1]` | 0 | 3 | -1 | 0 | `2^6=4^3`, fails strict gap |
| `10/01` | 3 | `[1,0,-1]` | `[-1,0,1,1]` | 3 | 7 | 1 | 0 | `2^14>4^6` |
| `10/01` | 4 | `[1,-2,-1,2,1]` | `[-1,2,1,-1,-3]` | 4 | 9 | -5 | 0 | `2^18>4^7` |
| `101/011` | 1 | `[1]` | `[-1]` | 0 | 2 | -1 | 0 | `2^12<9^4` |
| `101/011` | 2 | `[1]` | `[-1,0,1]` | 2 | 5 | -1 | 0 | `2^30>9^8` |
| `101/011` | 3 | `[1,0,0,-1]` | `[-1,0,1,1]` | 3 | 7 | 2 | 1 | `2^42>9^10` |

All remaining rows through search degree 24 are in `mahler-uncovered/evidence.json`,
including primitive norms and common shifts removed. There is no justified
reason to extend to degrees 25–48: low-degree pairs already close both ledgers.
Non-unit leading coefficients require the additional condition
`v2(c)<L^(k+1)` at the levels used; the two selected pairs have unit coefficients
and avoid that issue altogether.

The signed falsification domain is `-512<=p<=512`, odd `1<=q<=31`, comparing
64 actual Collatz parities: 16,400 pairs per target, zero complete matches.
This is only a bounded adversarial check. Finite modular seeds **do** match
at each specified precision, and establish non-vacuity; no rational conclusion
is drawn from the absence of small matches.

Failed approaches now explained precisely: criterion (C)'s periodic control is
too low-order here; a degree-0 truncation has no strict gap in the primary
case; aperiodicity alone has no general rational exclusion consequence;
real/complex automatic-digit theorems concern a different object. Repeating
or enlarging these failed searches is unnecessary.

## 4. Secondary target: complete algebraic and kernel certificate

For `1->101, 0->011`,

```text
w(3n)=w(n), w(3n+1)=1-w(n), w(3n+2)=1;
L=3, r=2, A=8, B=9, c0=10, c1=7, t=1, s=0, e=1.
F(z)=(z+z^2)/(1-z^3)+(1-z)F(z^3),
F_2(8/9)=3*x(w)+30.
```

The primary argument fails because the affine multiplier is `9/8>1`.
The improved pair is `R(z)=1+(z^2-1)F(z)=-z^5+O(z^6)`.
The following gives a complete infinite proof in ordinary integer towers,
using the same finite-congruence interpretation as the family proof.

Suppose `p/q` realizes this word. Put `a_k=8^(3^k)`, `b_k=9^(3^k)`,
`D_0=3q`, `u_0=9(p+10q)`. The finite base identity proved in
`MorphismPrefix.base_identity` supplies every initial congruence for these
values. Define

```text
Delta_k=(b_k^3-a_k^3)*u_k-D_k*b_k*(a_k*b_k+a_k^2),
u_(k+1)=b_k*Delta_k,
D_(k+1)=D_k*(b_k-a_k)*(b_k^3-a_k^3),
E_k=D_k*b_k^2+(a_k^2-b_k^2)*u_k, H_k=|u_k|+D_k.
```

These are integer recurrences with no division. All `D_k` are positive odd
integers. The finite Mahler identity transports all-prefix congruences:
multiply the old length-`3n` congruence by `b*(b^3-a^3)`; its difference
from the new one is `a^(3n)` times an integer, with a factor `b^2` on the
new congruence. Bezout coprimality of `a,b` cancels `b^2`, preserving the
entire modulus `(a^3)^n`.

The six-symbol prefix is `101011`. Its homogeneous sum satisfies

```text
b^5*b^2+(a^2-b^2)*pre(a,b,6)=a^5*(-b^2+a*b+a^2).
```

The congruence at length 6 therefore gives
`b^5*E=a^5*(D*(-b^2+a*b+a^2)+a*(a^2-b^2)*r)` for an integer `r`.
The expression in parentheses is odd. Cancel `b^5` by coprimality to see
that `E` is an odd multiple of `a^5`: nonzero at **every** level, with
`v2(E_k)=15*3^k` and `|E_k|>=2^(15*3^k)`.

Since `0<a<b`, `Q0h=ab+a^2<2b^2`, so
`|u_(k+1)|<=b_k^4*(|u_k|+2D_k)` and `D_(k+1)<=b_k^4*D_k`.
Thus `H_(k+1)<=3*b_k^4*H_k` and

```text
H_k<=3^k*9^(2*(3^k-1))*H_0,
|E_k|<=b_k^2*H_k<=3^k*H_0*9^(4*3^k-2).
```

The strict integer comparison `2^15>4*9^4` then forces
`4^(3^k)<=3^k*H_0` at every `k`. But `3^k>=2k` and `16^k>=6^k`, so
`2^k<=H_0` for every `k`, impossible at `k=H_0` since `k<2^k`.
This proves rational exclusion on paper; tails follow from inverse branches.
The kernel now checks the entire argument through the generic periodic-control
interface in `PeriodicCertificate.lean`. `Secondary.lean` proves the exact
finite control conditions and exports `no_rational_seed_realizes_secondary`,
`no_rational_seed_realizes_shifted_secondary`, and
`no_eventually_shifted_secondary_itinerary`. The same old signed tower and
the general height bound are reused; no infinite certificate assumption is
added to the public theorem for this concrete word.

## 4.1 Stronger criterion and a second primary proof (D2)

`PeriodicControl` contains a positive period `P`, a length-`P` binary block
and an order `N`. Its kernel-checkable predicate `Valid M C` requires
`1<=P<=N`, agreement of the actual fixed point with that periodic block at
every index below `N`, and an odd difference at `N`. The improved sufficient
condition is exactly

```text
2^(L*(L-1)*N) > max(A,B)^(P*(L-1)+L+e).
```

`no_rational_seed_with_periodic_control` proves exclusion for arbitrary
equal-weight images under H1–H3, this finite validity predicate and the gap.
`no_rational_seed_with_shifted_periodic_control` excludes all tails.
The form has degree `P`, is an odd multiple of `a_k^N`, and satisfies the
height ledger with `P*(L-1)+L+e` instead of `L^2+e`. The proof retains
`(2L)^k` and uses the general strict-gap contradiction. This is a verified
parametric certificate interface; certificates contain finite data rather
than an assumed irrationality proposition.

For `101/011`, `alternatingControl` is block `10`, `P=2,N=5`. It gives exactly
the degree-2 pair found independently and already recorded upstream.
For `10/01`, `thueMorseControl` is block `100101`, `P=6,N=10`. It gives
`p0=1+z^3+z^5`, `p1=-1+z^6`, leading coefficient -1 and
`2^20>4^9`. The export `no_rational_seed_realizes_thueMorse_mahler` therefore
proves the primary exclusion **without** using its aperiodicity or contraction
theorem. Both routes are audited. Searching degree beyond 24 is unnecessary.

## 5. Literature and attribution audit

No novelty is claimed. Primary sources checked on 2026-11-14:

- Monks–Yazinski, *The autoconjugacy of the 3x+1 function*, manuscript dated
  2002-07-10, [author-hosted PDF](https://monks.scranton.edu/files/pubs/AutoConjV13.pdf),
  Lemmas 3.1–3.2 and Corollary 3.3(a), pp. 6–7: fixed-denominator rational
  orbits are discrete, and a bounded orbit is eventually cyclic. This is the
  classical foundation of the primary argument, not a new rational-orbit
  principle. Theorem 2.7(b) also gives a density restriction on divergent
  rational orbits; our proof uses the explicit block contraction instead.
- López–Stoll, [arXiv:2101.12747v1](https://arxiv.org/abs/2101.12747v1),
  submitted 2021-01-29: the general rational Periodicity Conjecture is open.
  The abstract states additional density hypotheses. None are imported as
  an unconditional automatic-word irrationality theorem here.
- `msharpe248/collatz`, main still
  [`ec8174b567d5cab4960024782210b5f5db02bd3a`](https://github.com/msharpe248/collatz/tree/ec8174b567d5cab4960024782210b5f5db02bd3a),
  commit dated 2026-09-06. Its
  [`analysis/RUNG1_ATTACK.md`](https://github.com/msharpe248/collatz/blob/ec8174b567d5cab4960024782210b5f5db02bd3a/analysis/RUNG1_ATTACK.md)
  concerns the supercritical `110/011` word at `8/9`. Its
  [`analysis/mahler_candidates.json`](https://github.com/msharpe248/collatz/blob/ec8174b567d5cab4960024782210b5f5db02bd3a/analysis/mahler_candidates.json)
  **already contains exactly our secondary degree-2 pair** with order 5,
  coefficient -1 and comparison `2^30>9^8`, labelled finite with no infinite
  certificate supplied there. Our independent search reproduces that known
  candidate; it is not an original discovery. No conclusion about other
  files or unpublished work is inferred from this inspection.

Next priorities: systematically test small periodic controls on the existing
finite catalogue, then investigate generic aperiodicity before removing that
explicit hypothesis from the subcritical theorem. General coverage of all
admissible morphisms remains open.

## 6. Complete small catalogue (D3)

The control search is now complete on the old admissible domain `2<=L<=5`,
with periods tested in increasing order from 1 through 24 and first-disagreement
search restricted to 512 symbols. Every one of the 144 morphisms has a valid
certificate; the largest chosen period is 15. The four cases requiring period
beyond 12 all have `mu(1)=10011`, with `mu(0)` equal to `01101`, `10101`,
`10110` or `11010`; period 15 closes each ledger. No Padé degree above 24 was
searched.

| L | admissible images | old (C) holds | new certificates | maximum chosen period | maximum chosen order |
|---|---|---|---|---|---|
| 2 | 1 | 0 | 1 | 6 | 10 |
| 3 | 6 | 2 | 6 | 5 | 8 |
| 4 | 27 | 11 | 27 | 12 | 18 |
| 5 | 110 | 52 | 110 | 15 | 23 |

`verify_uncovered.py` writes both the JSON and
`CollatzLab/SmallCertificates.lean` deterministically. This module stores
finite integer masks, with index-zero symbols in the low bit. The kernel
checks all rows' image lengths/bounds, H1, equal weights, explicit disagreement,
finite control validity and strict gap. `catalogue_valid` and
`listed_no_rational_seed` therefore prove rational exclusion for **each listed
word**, at arbitrary seed height and every positive odd denominator.

The fourth Rust test independently enumerates every finite image pair by bit
counts, compares the complete set of 144 keys, reconstructs words by digit
recursion and checks every control and ledger. Thus completeness of the
finite enumeration is independently verified; the Lean catalogue theorem's
domain is its explicit list, rather than a separate Lean enumeration theorem
over all finite functions. The generic Theorem 8.1 and certificate interface
remain universally quantified and do not depend on this list.

Compared with (C)'s 65 successes, this adds 79 rigorously certified words.
It does not establish a bound of 15 or 24 for other lengths or guarantee the
existence of any particular approximant outside the finite catalogue.
CI now audits 140 declarations and runs 94 Rust tests, plus exact reproduction
of both generated artifacts.
