# Phase 13 overnight computation — owner handoff

The fifth intermediate witness transition after `L_5` is certified:
**`H_87102 > H_87101 = H_87100 > H_87099`**.
The actual 87100 witness first fails at zero-based index 87101. Its maximal
plateau has two prefixes, giving consecutive widths **2, 2, 3, 1, 2**.
The new selected-basis update is exactly `f'=4*f, g'=2*f+g`, returning to
the update seen in the first two links after two other updates. The earlier
width-decrease and constant-update counterexamples remain valid.
These finite observations determine no general width or basis law,
asymptotic exponent or cancellation bound.

Only the new minimum at 87102 was computed. All twelve previous height
records, four earlier transition records, previous command logs and raw-shadow
level 8 are preserved. See [issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the local plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
Remote issue/PR state was neither queried nor changed.

## New independent minimum and transition

The [bounded scan](overnight/witness_transition.py) uses literal substitution
and actual rational numerator iteration. The
[separate checker](overnight/verify_transitions.py) reconstructs the word by
indexed substitution, then finds the same failure using reverse integer
branches and an exact 2-adic discrepancy valuation. It independently verifies
both endpoint minima: primitive positive odd denominators, actual numerator
parities and compact no-smaller-height certificates.

The new height has 51,875 bits, its positive difference from `H_87100` has
35,224 bits, and exact comparison gives `1 < H_87102/H_87100 < 2`.
A witness change alone would not establish a strict increase; both minima
are certified. The positive failing numerator has 63,386 bits and SHA-256
`fed6d60a0e128b73e3ff84b27de20741f8974edfde71bff283f3b7286c77edaf`.
Both routes agree on this hash.

[transitions.jsonl](overnight/transitions.jsonl) contains five compact records,
218,847 bytes, SHA-256
`7d1f72c3f80c7ce2a7c78b391e7322381a55457e2f50c5b47dff503c1a43c990`.
The preceding 175,082 bytes are unchanged. The
[replay manifest](overnight/transition-verification.json) binds its results
to the height and transition files. The completed
[checkpoint](overnight/transition-checkpoint.json) records the latest request.

The [new computation](overnight/transition-87100-compute.log) passed in 7.94s,
peak 109,356 KiB. The [independent replay of all five links](overnight/transition-87100-replay.log)
passed in 16.81s, peak 67,268 KiB. Both had bounded timeouts and a 1 GiB child
address-space cap. Previous command logs are unchanged.

## Finite plateau and basis falsification

The exact consecutive maximal plateaux are `87092..87093`, `87094..87095`,
`87096..87098`, the singleton `87099..87099`, and `87100..87101`. Witness
persistence and monotonicity give each constant interval; independently
certified strict height changes on both sides establish maximality. The earlier
widths 3 and 1 still reject nondecreasing widths; the latest width is 2.

The refreshed [probe](overnight/probe_basis_pattern.py) records four adjacent
maximal plateau comparisons and this explicit decrease in
[its compact report](overnight/basis-pattern-probe.json). Both intervals must
have certified strict boundaries before a comparison is counted. Cramer's
coordinates, direct vector multiplication and signed determinants give
`[[4,0],[2,1]]` for the newest selected-basis update, following
`[[4,0],[2,1]]`, `[[4,0],[2,1]]`, `[[8,0],[4,1]]`, `[[2,0],[-1,1]]`.

The [probe command](overnight/basis-87100-chain.log) passed in 1.90s, peak
67,840 KiB. Its implementation was unchanged. The preserved
[controls](overnight/width-decrease-controls.log) passed at the prior checkpoint in
3.49s, peak 42,368 KiB: reported small-chain decreases agree with directly
enumerated complete constant-height runs. Equal-height witness changes
and unknown left boundaries cannot establish maximality. The existing
5404 Fraction/valuation cases, 68 small transition certificates, eighteen
corruptions, three resumption controls and four malformed chains also passed.
Smoke already invokes both extended checks.

The earlier failed extrapolation is preserved: repeating `f'=4*f, g'=2*f+g`
every two bits through 90000 produces a candidate that first fails actual
parity at index 87097. That candidate differs from the actual source witnesses;
it certifies no minimum or plateau. No optimizer is called by the probe.
The old result fields and command logs remain unchanged.

## Previously completed evidence

| Prefix length N | Bit length of exact minimum H_N |
|---|---:|
| 80000 | 35217 |
| 87090 | 35217 |
| 87091 | 35217 |
| 87092 | 51875 |
| 87094 | 51875 |
| 87096 | 51875 |
| 87099 | 51875 |
| 87100 | 51875 |
| 87102 (this iteration) | 51875 |
| 90000 | 51875 |
| 522546 | 211281 |
| 522547 | 211281 |
| 522548 | 311267 |

Full hexadecimal witnesses and minimum certificates are in
[heights.jsonl](overnight/heights.jsonl). Its thirteen records total 6,642,220
bytes, below the fixed 8 MiB cap, SHA-256
`2d4421cc83faf6c618a465583b45abad3b1eb26e29b678206a4d9afda9faad14`.
All preceding 6,516,327 bytes are identical to the entry checkpoint; the only
new line is the independently certified minimum at 87102 (125,893 bytes).
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
418.56s, peak 100,104 KiB, under a 750-second timeout and 1 GiB child
address-space cap. It checked all thirteen height certificates, all five
independent transitions, nine-level raw-shadow replay and baseline/basis/
transition controls, including the width-decrease tests. The
[scope/preservation audit](overnight/checkpoint-audit.json) records unchanged
Git state, authorized paths, append-only evidence, all 28 preserved older
command logs, unchanged producer/checker/smoke sources and source hashes.
No calculation remains running.

The new sample is exact computation plus an independent finite parity and
minimality certificate. The basis updates and width-decrease test are derived
exact integer data; maximal-plateau interpretation uses the inherited written
monotonicity argument. Python exact arithmetic and the written parity/basis
identities are the trust boundary. No new Lean-kernel theorem was added.
Exact `B`, asymptotic gcd cancellation and further intermediate minima remain
open. No asymptotic or originality claim follows from these finite samples.
No Lean, Rust or remote CI result is claimed.

## Next obligation and checkout

Locate the first actual parity mismatch of the stored `N=87102` witness
through 90000, then independently certify that prefix's minimum only if
absent. Exact arithmetic gives `H_87102 < H_90000`, with different primitive
witnesses. The next failure is unresolved. Earlier failures and plateau widths
do not determine it. The journal gives the concrete command and fixed evidence
caps. Useful bounded work remains, so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`95fb0b67b3ca79382bc45db76d8263d1b1ea8323`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver
owns the next validated checkpoint. All edits stay within the three authorized
paths; original Phase 13 engines, PR #29, main, CI and papers are unchanged.
