# Phase 11: beyond uniform contraction

Issue: <https://github.com/hipotures/collatz-lab/issues/19>.
No originality claim is made. All infinite claims below identify their proof status.

## Gate A: exact supercritical aperiodic example

`NonContracting110111.lean` defines precisely `mu(1)=110`, `mu(0)=111`.
The fixed point starts at 1, has both symbols (indices 0 and 2), and satisfies
`w(3n)=w(3n+1)=1`, `w(3n+2)=1-w(n)`, including index zero.
`NonContractingChecks.literal_semantics` independently kernel-evaluates four
literal list-substitution levels and compares them with the indexed word.

**Kernel theorem:** this word is not eventually periodic. For a positive
period p beyond any starting index s, set d=floor(p/3). If p mod 3=0, compare
last columns and cancel the complement to obtain the smaller positive period d.
If p mod 3=1, compare the forced column at `3*(3s+2d)+1` with its p-shift,
whose index is `3*(3*(s+d))+2`. Its parent has forced value 1, so the shifted
value is 0, a contradiction. For residue 2, start at `3*(3s+2d)` instead.
Strong induction excludes all periods. No rationality premise is used.

**Kernel theorem:** every three consecutive bits contain at least two ones.
Consequently every length-3h window, at every starting index, contains at least
2h ones. For h>0 and R>=2h, `3^R >= 9^h > 8^h = 2^(3h)`. Thus no complete-image
grouping satisfies the Phase 10 gap. More strongly, suppose length-k chunks
starting at any shift t all have at most R ones. Summing three chunks gives
`3R>=2k`. Cubing a purported `3^R<2^k` would contradict `9^k>8^k`.
`nonContracting_no_uniform_chunks` therefore excludes **all** positive fixed
chunk lengths, at **all** shifts. This is a limitation of that criterion.

**Kernel frequency estimate:** for every n<3^k,
`|4*W(n)-3n|<=2k`, represented as two integer inequalities. The exact recurrence
is `W(3n+r)+W(n)=3n+r` for r=0,1,2; discrepancy changes to its negative plus r.
Choosing k just above log_3(n) gives `W(n)/n -> 3/4`. This last real-limit
interpretation is an elementary deduction from the kernel estimate, not a
formal real-analysis theorem. It covers all prefixes, not only powers.
The exact aligned power count, reusing Phase 10 `balance_power`, is
`4W_k(b)=3*3^k+(-1)^k*(4b-3)` for each occurring parent bit.

These facts alone do not imply rational-seed exclusion.

## Research in progress

The word begins with 11. Hence substitution should give square prefixes of
length 2*3^k. A separate integer proof is being developed to test whether their
congruence precision exceeds the height of periodic approximants. Until that
proof and its semantic regressions are complete, no exclusion is claimed.

## Gate C: a successful mechanism independent of contraction

**Kernel theorem, `RepeatedPrefix.lean`:** if a Boolean word v is not eventually
periodic and has arbitrarily long square prefixes UU, no rational seed realizes
v. Both conditions are essential. There is no frequency premise.

Here is an independent integer reconstruction. Let m=|U|>0, r the one-count,
c the affine offset, A=2^m, B=3^r, and let x_j be numerator states with fixed
positive odd denominator q. Actual realization of the two identical blocks gives

```
A*x_m = B*p + c*q,
A*x_(2m) = B*x_m + c*q.
```

Subtracting shows `A | B*(x_m-p)`. Since A and B are coprime, `A | x_m-p`.
Thus the integer `E=(A-B)*p-c*q=A*(p-x_m)` is divisible by `A^2=4^m`.
If E=0, `x_m=p`, so determinism makes the full itinerary periodic. Independent
non-eventual-periodicity implies E!=0, hence `4^m<=|E|`.

For every length-m Boolean word, `0<=c<=3^m-2^m` and `r<=m`. Both A and B are
in `[0,3^m]`, so `|A-B|<=3^m`. Therefore `|E|<=(|p|+q)*3^m`. The exact strict
base gap 4>3 contradicts arbitrarily large m. The formal proof uses the existing
integer Bernoulli bound to choose `m>=3*(|p|+q+1)`, not real limits or logarithms.
This does not bound the actual orbit states, which can grow very rapidly.

`word_power_congr` proves equal parent letters have identical iterated images
at every level. A prolongable fixed word beginning with 11 therefore has square
prefixes of length `2*L^k`. The new general theorem
`no_rational_seed_morphism_initial_double` assumes exactly this initial double
and independent non-eventual-periodicity; it assumes neither equal image weights
nor a contracting chunk. It applies to the explicit 110/111 word.
`NonContractingExclusion.lean` excludes every rational realization, every finite
shift, and eventual agreement after arbitrary finite prefixes. The raw eventual
itinerary theorem covers **either sign** of odd denominator using the existing
normalization theorem. Negative numerators and unreduced fractions are included.

The theorem strengthens the repository's available sufficient criteria: this
concrete example provably satisfies no fixed-length uniform contraction premise.
It does not prove exclusion for all supercritical words or all automatic words.
It proves rational exclusion, not transcendence. Its originality is **unverified**;
the periodic-approximation and integer-height principle is classical.

### Independent adversarial checks

- Python computes affine maps independently for all 254 binary blocks of
  lengths 1..7 and their squares. Positive, negative and signed-denominator
  finite witnesses satisfy the exact modulus and height bound.
- Literal substitution, independently of both Lean indexing and the balance
  formula, gives square prefixes at levels 0..7.
- Actual positive, negative and unreduced 81-bit rational prefixes are checked
  by Lean reduction and Python numerator iteration. They establish non-vacuous
  finite semantics; none is an infinite rational realization.
- `101/010` remains realized by 1/1. Its fixed point starts 10, so the initial
  double premise fails. The all-one word at -1/1 has unbounded square prefixes
  and density one but is periodic, so the aperiodicity premise fails.
  Deleting either safeguard would make the theorem false.

## Gate B: exact classification of the contraction method

**Kernel theorem, `SpectralThreshold.uniform_contraction_iff_subcritical`:**
let L>=2, mu be any binary length-L substitution prolongable on 1, r0/r1 its
image weights, and D=L-r1+r0>0. There exist a finite shift t, positive chunk
length k and cap R satisfying the Phase 10 uniform bound and `3^R<2^k`
**if and only if** `3^r0<2^D`. The reverse implication supplies a power-block
certificate; the forward implication rules out every chunk size and shift in
the supercritical case. No aperiodicity premise is needed for this classification.
Rational exclusion still needs a separate aperiodicity theorem.

This classifies certificates for the actual selected fixed point, not every
word in its substitution subshift and not arbitrary nonuniform substitutions.
The underlying balance identity is reused from Phase 10, not claimed as new.

### Exact identities and degeneracies

The incidence characteristic polynomial is `(X-L)(X-(r1-r0))`, kernel checked
by polynomial expansion. `power_image_count` exports

```
D*W_k(b) = r0*L^k + Delta^k*(D*b-r0).
```

It applies to each occurring parent at every position. It does not assert that
both parents occur. The signed negative-eigenvalue case is included. A uniform
bound for the absolute discrepancy is `(D+r0)*|Delta|^k`.

`frequencyDen_nonnegative` proves D>=0. When D=0, r0=0 and r1=L; the selected
fixed point is the constant-one word (`frequencyDen_zero_word`). Dividing by D
is invalid there. When D>0, prolongability forces r1>=1, so `|Delta|<L` follows
without primitivity. The otherwise exceptional Delta=-L case would require
r1=0 and cannot be prolongable on 1. Constant-one examples with r1=L and r0>0
have D=r0, frequency one and no contraction. Nonprimitive examples with r0=0,
r1<L have limiting frequency zero and are covered by the subcritical theorem;
they can be eventually constant and need not be rational exclusions. Identical
images, absent letters, Delta=0 and period-one fixed points are all permitted.

The exact discrepancy and Phase 10 boundary estimate imply the ordinary
frequency rho=r0/D, uniformly in finite-window starting position. This analytic
interpretation is a deduction from integer estimates, not a Lean real-limit
statement. The classification itself uses no limits. Critical equality would
require `3^r0=2^D`, impossible since the former is odd and the latter even for
D>=1 (`rational_threshold_ne`). Equivalently rational rho cannot equal
log(2)/log(3); that equivalence uses elementary real logarithms only in exposition.

### Effective subcritical witness

Choose integers s,d>=1 with `d*r0<D*s` and `3^s<2^d`. Such a separating slope
is constructed entirely in integers: from `3^r0<2^D`, take
`t=3*3^r0+1`, `s=r0*t+1`, `d=D*t`. Integer Bernoulli amplification gives
`4*(3^r0)^t <= (2^D)^t`, so `3^s<2^d` and `d*r0<D*s`.

Set `B=max(1,|Delta|)`, `C=d*(D+r0)+D*d`, `k=B*C+1`, `S=L^k`,
`R=floor(s*S/d)`. Since 1<=B<L, the same amplification proves
`(C+1)*B^k<=S`. The spectral transient and the integer floor error are
therefore both dominated by the positive margin:

```
d*D*W_k(b) <= D*s*S - D*d <= D*d*R.
```

Thus every aligned S-block has weight at most R, and raising a purported
failure of `3^R<2^S` to the positive d-th power contradicts `3^s<2^d`.
These constructions, including existence and rounding, are kernel checked.
The witness is deliberately large; no minimal k is claimed. A faster finite
search can return a smaller certificate but failure below a cutoff proves nothing.

### Why no supercritical grouping can help

`uniform_chunks_frequency_necessary` proves the stronger necessary inequality
`r0*k<=D*R` for every uniform cap on shifted length-k chunks. Sum the cap at
length `k*L^e`, retain the initial-prefix boundary term, and compare with the
exact balance formula. If `D*R<r0*k`, its positive integer gap times L^e would
be bounded by a constant times `B^e`, where B<L. An explicit Bernoulli witness
e gives a contradiction. Raising the proposed contraction gap to D and the
supercritical inequality to k then gives inconsistent integer powers.

This establishes that subcritical substitutions are eventually covered by
power-block contraction, whereas supercritical ones are outside that method.
The 110/111 exclusion is therefore an application of a genuinely different
repository criterion, rather than a search for a longer contracting chunk.

## Sharper return bound and further research routes

The repeated-prefix mechanism also proves the following **kernel-checked**
finite inequality. If the first ell bits recur at position m>0 in a nonperiodic
rational itinerary, and r=W(m), then

```
2^(m+ell) | E_m,
2^(ell+r) <= (abs(p)+q)*3^r.
```

The sharper bound uses the exact universal offset cap
`offset(v,m)<=2^(m-r)*3^r-2^m`, attained by putting all ones last. It requires no
frequency hypothesis. This identifies a quantitative partial-repetition route
beyond full squares; a finite return alone is not an infinite exclusion theorem.

| Route | Precise obligation / smallest test | Evidence and outcome | Status / genuine scope |
|---|---|---|---|
| Variable affine cocycle | Actual maps `8*y'=9*y+5q` and `8*y'=27*y+19q`; seek bounded states or a common center | Exact recurrence kernel proved. Their homogeneous integer matrices have off-diagonal products 287 and 211, so do not commute. A common center would be both -5 and -1, kernel proved impossible. Both multipliers expand. | Bounded-state pigeonhole route fails; it excludes no seed. The successful route bounds a cycle-closing form instead of states. |
| Finite rational congruences | Find a contradiction for unbounded repeated prefixes with fixed p/q, not merely a failed finite seed search | For every tested finite word the affine congruence has a residue solution because 3^r is odd. Signed witnesses exist through 81 bits. Adding repetition yields modulus `2^(m+ell)` and a height contradiction. | Successful general kernel criterion, non-vacuously applied to 110/111 and all shifts/tails. Strictly extends available contraction criteria. |
| Spectral discrepancy | Determine whether longer fixed chunks can contract in the supercritical case | Exact iff theorem above; no fixed chunk can work. Quantified transient proves every subcritical case does eventually work. | Kernel classification of this method, not a universal irrationality theorem. Rational constant-one and 101/010 controls prevent deleting aperiodicity. |
| Vector / Mahler transport | Relate the **actual seed**, not just an ordinary automatic generating series, to a functional equation with valid arithmetic heights | A useful two-step prefix-height profile is kernel proved below. Finite coefficient and seed-sum checks support the stated exploratory relation. No analytic specialization theorem is proved here. | A separate possible proof, not a dependency of the exclusion. Transcendence remains open in this development. |

### A concrete Mahler route with its remaining obligations

For nu=mu^2, `nu(0)=110110110`, `nu(1)=110110111`. For j<9 the common
prefix-height vector is `(0,1,2,2,3,4,4,5,6)`. The new kernel theorem
`nonContracting_nine_prefix_height` proves, for every n,j<9,

```
W(9n+j)=6n+W(n)+2*floor(j/3)+(j mod 3).
```

Consider the exploratory formal series `H(x,y)=sum_n x^n*y^W(n)` and
`F(x,y)=sum_n w(n)*x^n*y^W(n)`. The candidate identities are

```
H(x,y)=P(x,y)*H(x^9*y^6,y),
P=(1+x*y+x^2*y^2)*(1+x^3*y^2+x^6*y^4),
(1-x)*H(x,y)-1=x*(y-1)*F(x,y).
```

The exact profile supplies a coefficientwise derivation, checked independently
on finite coefficients by `verify_spectral_boundary.py`; these infinite formal
series identities are **not exported as Lean theorems**. Finite affine sums
confirm that the actual Collatz seed is `-F(2,1/3)/3` in Q_2, and the proposed
specialization would give `seed=-(H(2,1/3)+1)/4`. To reduce the transformation
to z->z^9, put `x=3^(3/4)*z`; the candidate evaluation point becomes
`z=2/3^(3/4)`, an algebraic 2-adic point of positive valuation. A choice of the
fourth root requires working in a suitable finite extension.

Remaining obligations: formalize the series/specialization identities, prove
non-rationality or transcendence of the normalized H over the relevant field,
check functional-equation nonvanishing at the orbit, and supply an appropriate
p-adic specialization/height argument. The real and 2-adic sums are never
identified here. Generic automatic generating functions alone do not provide
any of those missing steps. This route excludes no additional seed at present.

## Primary-source scope and originality

Consulted 2026-11-14; this is a focused comparison, not a repeat of Phase 9.
No external theorem is an assumption of any new Lean result.

- **Monks–Yazinski**, *The autoconjugacy of the 3x+1 function*, Discrete Math.
  275 (2004), 219–236, [author PDF](https://monks.scranton.edu/files/pubs/AutoConjV13.pdf),
  Theorem 2.7(b), printed p. 6, proof in Section 4.1: statement and proof read.
  It supplies a lower density bound for noncyclic rational orbits; it does not
  exclude the supercritical example. The new exclusion uses repetition instead.
- **López–Stoll**, arXiv:2101.12747v1 (2021), [Section 6](https://arxiv.org/html/2101.12747v1#S6),
  Theorem 1 and equations (15)–(16): relevant statement and transfer step read.
  The final inference from the real value to the 2-adic value is unsupported
  for a hypothetical escaping rational orbit. This agrees with the earlier
  repository audit; no theorem here relies on that claim.
- **Molchanov**, Vestnik Moskov. Univ. Ser. I Mat. Mekh. (1983), no. 2, 31–37,
  [original scan](https://www.mathnet.ru/eng/vmumm3467): theorem text on pp. 31–32
  inspected in the original scan's extracted text; the proof was not checked
  line by line in this phase. It concerns p-adic Mahler values under substantive
  function, transformation and point hypotheses. It motivates the separate H
  route; no direct application to H has been established here. Phase 9's
  equal-weight comparison is preserved without modification.
- **lyapunov_weaver**, *Automatic parity and primitive substitutions in rational
  Collatz dynamics*, [rStation version 2, 22 Oct 2026](https://rstation.ai/problems/collatz/papers/16/v2):
  statements and scope discussion read; full analytic proof not independently
  checked. It claims restrictions for positive rational automatic/primitive
  itineraries through analytic comparison of completions. The webpage's review
  is platform review, not evidence of journal publication. This phase uses an
  elementary argument for both numerator signs and makes no general automatic
  word or priority claim.

The repeat/periodic-approximation height principle is established mathematics.
The contribution claimed here is a checked criterion and an application outside
the repository's previous contraction scope. Whether either theorem statement
or application is new in the wider literature remains **unverified**. No claim
of publication, peer review, or general Periodicity Conjecture progress follows.
