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
