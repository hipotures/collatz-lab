# Phase 13 overnight computation — owner handoff

The seventh intermediate witness transition after `L_5` is certified:
**`H_87104 > H_87103 > H_87102`**. The actual 87103 witness first fails at
zero-based index 87103. Its minimum is therefore a singleton maximal plateau.
The consecutive certified widths are **2, 2, 3, 1, 2, 1, 1**. The new height
has 51,875 bits; its positive increase has 35,225 bits, with exact comparison
`1 < H_87104/H_87103 < 2`. It remains strictly below `H_90000`.
These finite data establish no general plateau law or asymptotic behavior.

Only the missing minimum at 87104 was computed. All fourteen previous height
records, six previous transitions, raw-shadow artifacts and older command logs
are preserved. See [issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the local plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
Remote issue/PR state was neither queried nor changed.

## Exact computation and independent certificate

The [bounded producer](overnight/witness_transition.py) uses literal
substitution and actual numerator iteration. The [separate
checker](overnight/verify_transitions.py) reconstructs the word by indexed
substitution and finds the same first failure by reverse integer branches and
exact 2-adic discrepancy valuation. Both endpoint minima have independently
checked primitive positive odd-denominator witnesses, every actual numerator
parity and compact no-smaller-height certificates. The positive failing
numerator has 63,385 bits and SHA-256
`99fe23823dcf0aa8cdf4a0cb547dc84578c6ac609132e475d28cea8feaae4b09`.
Both routes agree on this hash.

The [computation log](overnight/transition-87103-compute.log) records a pass,
exit 0, in 7.79s, peak 110,572 KiB. The [independent seven-link
replay](overnight/transition-87103-replay.log) passed, exit 0, in 23.25s,
peak 68,236 KiB. The commands used respective 185- and 180-second outer
timeouts, the producer's 180-second signal budget, and a 1 GiB child
address-space cap. Exact commands are in the journal.

[heights.jsonl](overnight/heights.jsonl) now has fifteen records, 6,894,006
bytes, SHA-256
`81a21156f7cf355ae01cefa2d9cc73ca8275ccda3a0d01fce45db461b96fa07a`.
The new line has 125,892 bytes; all 6,768,114 previous bytes are unchanged.
[transitions.jsonl](overnight/transitions.jsonl) has seven records, 306,375
bytes, SHA-256
`d76b54b836637868a2b68bd0e738b2f5d0186e70449691dc6f8b1f63d1c06b66`.
The new line has 43,763 bytes; all 262,612 previous bytes are unchanged.
Both fixed caps, 8 MiB and 512 KiB, remain in force. The
[replay manifest](overnight/transition-verification.json),
[inventory](overnight/height-inventory.json) and completed
[checkpoint](overnight/transition-checkpoint.json) bind the new references.

## Derived finite plateau and basis data

The seventh selected-basis update is `[[2,0],[-1,1]]`, namely
`f'=2*f, g'=g-f`. It returns to the update at the earlier singleton 87099.
The adjacent singletons 87102 and 87103 have different updates. This extends
the existing counterexample to equal widths determining selected-basis updates.
These coordinates describe the stored algorithm-selected bases.

The [refreshed probe](overnight/basis-87103-chain.log) passed in 1.93s, peak
68,604 KiB, under its 35-second outer timeout and 30-second signal budget.
Its [report](overnight/basis-pattern-probe.json) checks six adjacent maximal
plateau pairs, retaining the decreases 3 to 1 and 2 to 1. Six equal-width
pairs now include two unequal-update pairs. Each eligible plateau has
independently certified strict height boundaries on both sides; persistence
and monotonicity establish the constant interval. A witness change alone
does not establish a height increase.

All earlier extrapolation result fields and six chain links are unchanged.
Repeating `f'=4*f, g'=2*f+g` every two bits through 90000 still fails actual
parity at index 87097 by both forward and reverse routes. The probe calls
no optimizer. No producer, checker, probe, control or smoke source was
changed this iteration; existing semantic, corruption, resumption and chain
controls are included in smoke.

## Preserved earlier results

| Prefix length N | Bit length of exact minimum H_N |
|---|---:|
| 80000, 87090, 87091 | 35217 |
| 87092, 87094, 87096, 87099 | 51875 |
| 87100, 87102, 87103, 87104, 90000 | 51875 |
| 522546, 522547 | 211281 |
| 522548 | 311267 |

Equal bit lengths alone imply no plateau. The earlier `80000..87091` plateau
matches the k=5 shadow; the jump at 87092 lies in `[2^16657,2^16658)`.
The two k=6 boundary heights agree with its reduced shadow; the jump at
522548 lies in `[2^99985,2^99986)`. The all-level shadow-minimum argument
is inherited written mathematics, not a new theorem from these samples.

Raw-shadow levels 0..8 remain complete with gcds `[3,1,1,1,1,1,1,347,1]`.
At level 8, `S=1679616`, `L=18811699`, the raw numerator has 7,606,082 bits
and denominator 7,606,080 bits, with gcd 1. The return from 347 to 1 rejects
nondecreasing raw gcd; it establishes no asymptotic cancellation bound.
The [raw evidence](overnight/raw-shadows.jsonl), independent manifest,
checkpoint and original logs are unchanged. Level 9 remains unattempted.

## Validation, evidence levels and continuation

The full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in
423.34s, peak 100,528 KiB, under a 750-second timeout and 1 GiB child cap.
It checked all fifteen heights, seven independent transitions, nine raw-shadow
levels, baseline/basis controls, corruption/resumption cases and the preserved
finite falsifications. Shell syntax, Python compilation and `git diff --check`
also passed. The [checkpoint audit](overnight/checkpoint-audit.json) records
scope, source references, hashes, append-only preservation, all 36 unchanged
older command logs and unchanged Git state. Historical journal sections and
every Python/shell source are preserved. No calculation remains running.

The new minimum and first failure are exact computation plus an independent
finite actual-parity/minimality certificate. Basis changes are derived exact
integer metadata. The plateau interpretation uses inherited written parity
and monotonicity arguments. Python exact arithmetic and the written
cylinder/basis identities are the trust boundary. No new written all-level
proof or Lean theorem was added. Exact `B`, asymptotic gcd cancellation and
remaining intermediate minima are open. No originality or asymptotic claim
follows from seven intervals; no Lean, Rust or remote CI result is claimed.

Next: locate the first actual parity mismatch of the stored `N=87104` witness
through 90000 and independently certify only a missing target minimum.
Exact arithmetic gives `H_87104 < H_90000`, with different primitive witnesses;
the next failure remains unresolved. The journal gives the bounded commands.
Useful bounded work remains, so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`8f9414e1f3cfb286e4e6de2e5bca01f7c290a3a2`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the next validated checkpoint. All edits stay within the three authorized
paths; original Phase 13 engines, PR #29, main, CI and papers are unchanged.
