# Phase 13 overnight computation — owner handoff

The third intermediate witness transition after `L_5` is certified:
**`H_87099 > H_87098 = H_87097 = H_87096 > H_87095 = H_87094`**.
The actual 87096 witness first fails at zero-based index 87098. Its plateau
has three prefixes, after two consecutive two-prefix plateaux. All these
heights have 51,875 bits. The third selected-basis update is exactly
`f'=8*f, g'=4*f+g`. The finite widths **2, 2, 3** reject constant two-prefix
plateaux on this chain; they do not determine a general width law, asymptotic
exponent or cancellation bound.

Only the new minimum at 87099 was computed. All ten previous height records,
both earlier transition records and raw-shadow level 8 remain intact.
See [issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the local plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
Remote issue/PR state was neither queried nor changed.

## New independent minimum and transition

The [bounded scan](overnight/witness_transition.py) uses literal substitution
and actual rational numerator iteration. The
[separate checker](overnight/verify_transitions.py) reconstructs the word by
indexed substitution, then locates the same failure using reverse integer
branches and an exact 2-adic discrepancy valuation. It independently verifies
both endpoint minima: primitive positive odd denominators, actual numerator
parities and compact no-smaller-height certificates.

The new positive height difference has 35,222 bits, and exact integer
comparison gives `1 < H_87099/H_87096 < 2`. A witness change alone would not
establish a strict increase; both exact minima are checked. The failing
numerator is positive with 63,384 bits; its hash agrees between the two routes.

[transitions.jsonl](overnight/transitions.jsonl) contains three compact records,
131,315 bytes, SHA-256
`e83434b2e508be7859bb5af54e87c54c36ff22f3b2c949f705ac6bec5307781e`.
The preceding 87,545 bytes are unchanged. The
[replay manifest](overnight/transition-verification.json) binds its results
to the height and transition files. The completed
[checkpoint](overnight/transition-checkpoint.json) records the latest request.

The [new computation](overnight/transition-87096-compute.log) passed in 7.93s,
peak 108,244 KiB. The [independent replay of all three links](overnight/transition-87096-replay.log)
passed in 10.13s, peak 66,908 KiB. Both had bounded timeouts and a 1 GiB child
address-space cap. Previous command logs are unchanged.

## Finite plateau and basis falsification

The exact consecutive maximal plateaux are `87092..87093`, `87094..87095`
and `87096..87098`. Witness persistence and monotonicity give constant minima
through each interval; independent certificates establish strict height
changes on both sides. Thus the third width is three, while the first two
are two. This is a finite counterexample to constant two-prefix widths on
this chain, without a general replacement law.

The updated [probe](overnight/probe_basis_pattern.py) adds derived chain
metadata to [its compact report](overnight/basis-pattern-probe.json).
Source hashes, replay fields, contiguous intervals, basis determinants,
lattice membership and denominator parity are checked. Cramer's coordinates
are checked by direct vector multiplication. The third update is `[[8,0],[4,1]]`,
after two updates `[[4,0],[2,1]]`. No optimizer or new minimum is computed
by this probe; its chain data depend on the separately replayed certificates.

The [probe command](overnight/basis-chain-probe.log) passed in 1.85s, peak
67,160 KiB, under a 30-second signal budget, 35-second outer timeout and
1 GiB child address-space cap. The [new controls](overnight/basis-chain-controls.log)
passed in 3.47s, peak 42,164 KiB: 31 small independently certified chain links
include two equal-height witness changes; unknown left boundaries stay
unclassified; four malformed chains are rejected. Existing controls also
passed: 5404 signed Fraction/valuation cases, 68 small transition certificates,
eighteen corruptions and three publication/resumption cases.

The earlier extrapolation result remains unchanged: repeating
`f'=4*f, g'=2*f+g` every two bits through 90000 gives a candidate that fails
actual parity at index 87097. Both forward and reverse calculations agree.
That candidate differs from the actual 87096 witness, whose failure is at
87098. The old extrapolation supplied no minimum or plateau-width conclusion.
The original [probe log](overnight/basis-pattern-final.log) is preserved;
source hashes and the additional chain fields are refreshed in the report.

## Previously completed evidence

| Prefix length N | Bit length of exact minimum H_N |
|---|---:|
| 80000 | 35217 |
| 87090 | 35217 |
| 87091 | 35217 |
| 87092 | 51875 |
| 87094 | 51875 |
| 87096 | 51875 |
| 87099 (this iteration) | 51875 |
| 90000 | 51875 |
| 522546 | 211281 |
| 522547 | 211281 |
| 522548 | 311267 |

Full hexadecimal witnesses and minimum certificates are in
[heights.jsonl](overnight/heights.jsonl). Its eleven records total 6,390,436
bytes, below the fixed 8 MiB cap, SHA-256
`6850209b82258f5fa86f933369141fa8390dd8f05b3da9723ed9a819ecde0865`.
All preceding 6,264,543 bytes are identical to the entry checkpoint; the only
new line is the independently certified minimum at 87099 (125,893 bytes).
The [inventory](overnight/height-inventory.json) records exact comparisons and
inherited shadow hashes. Equal height bit lengths alone never imply a plateau.

The earlier shadow-boundary findings remain: `80000..87091` is a certified
plateau matching the k=5 shadow; the next jump lies in `[2^16657,2^16658)`.
At 522546 and 522547, exact heights and witnesses agree with the k=6 shadow;
the jump at 522548 lies in `[2^99985,2^99986)`. The known all-level shadow
minima are inherited written mathematics, not new theorems from these samples.

Raw-shadow levels 0..8 remain complete with gcds `[3,1,1,1,1,1,1,347,1]`.
At level 8, `S=1679616`, `L=18811699`, the raw numerator has 7,606,082 bits
and denominator 7,606,080 bits, with gcd 1. The return from 347 to 1 rejects
nondecreasing raw gcd; it establishes no asymptotic cancellation bound.
The nine-line [evidence](overnight/raw-shadows.jsonl), its
[independent replay](overnight/raw-shadow-verification.json), checkpoint and
original command logs remain unchanged. No raw-shadow producer was repeated.
Level 9 has not been attempted.

## Validation and evidence limits

The full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in
410.70s, peak 99,568 KiB, under a 750-second timeout and 1 GiB child
address-space cap. It checked all eleven height certificates, all three
independent transitions, nine-level raw-shadow replay, baseline/basis controls
and the new finite chain checks. The
[scope/preservation audit](overnight/checkpoint-audit.json) records unchanged
Git state, authorized paths, append-only evidence, preserved older logs and
source hashes. No calculation remains running. No Lean, Rust or remote CI
result is claimed.

The new sample is exact computation plus an independent finite parity and
minimality certificate. The basis updates are exact integer data; maximal
plateau interpretation uses the inherited written monotonicity argument.
Python exact arithmetic and the written parity/basis identities are the trust
boundary. No new Lean-kernel theorem was added. Exact `B`, asymptotic gcd
cancellation and further intermediate minima remain open. No asymptotic or
originality claim follows from these finite samples.

## Next obligation and checkout

Locate the first actual parity mismatch of the stored `N=87099` witness
through 90000, then independently certify that prefix's minimum only if
absent. Exact arithmetic gives `H_87099 < H_90000`, with different primitive
witnesses. The next failure is unresolved. Neither the old predicted failure
at 87097 nor the actual 87096 witness's failure at 87098 determines it.
The journal gives the concrete command and fixed evidence caps. Useful bounded
work remains, so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`05700214437a42e570128968356724bb7856622d`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver
owns the next validated checkpoint. All edits stay within the three authorized
paths; original Phase 13 engines, PR #29, main, CI and papers are unchanged.
