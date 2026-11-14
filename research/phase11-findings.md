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
