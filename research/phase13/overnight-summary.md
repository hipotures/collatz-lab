# Phase 13 overnight computation — owner handoff

The ninth intermediate witness transition after `L_5` is certified:
**`H_87104 < H_87109 = H_87110 = H_87111 < H_87112 < H_90000`**.
The actual 87109 witness first fails at zero-based index 87111. Its minimum
has a maximal plateau of width **3**, following the width-5 plateau.
The consecutive certified widths are **2, 2, 3, 1, 2, 1, 1, 5, 3**.
The new height has 51,875 bits; its positive increase has 35,235 bits, with
exact comparison `1 < H_87112/H_87109 < 2`. These finite data establish no
general plateau law or asymptotic behavior.

Only the missing minimum at 87112 was computed. All sixteen previous height
records, eight previous transitions, raw-shadow artifacts and preceding
command logs are preserved. See [issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the local plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
Remote issue/PR state was neither queried nor changed.

## Exact computation and independent finite certificate

The [bounded producer](overnight/witness_transition.py) uses literal
substitution and actual numerator iteration. The [separate
checker](overnight/verify_transitions.py) reconstructs the word by indexed
substitution and finds the same first failure by reverse integer branches
and exact 2-adic discrepancy valuation. Both endpoint minima have checked
primitive positive odd-denominator witnesses, every actual numerator parity
and compact no-smaller-height certificates. The new certificate excludes
all smaller odd-denominator vectors using one exhaustive coefficient row.
The positive failing numerator has 63,384 bits and SHA-256
`80b4f02234fba60be3ea1f1fb9d8c365a8bbd5f21fcb84a80d8141e69895a0a6`.
Both routes agree on this hash.

The [computation log](overnight/transition-87109-compute.log) records a pass,
exit 0, in 7.79s, peak 111,948 KiB. The [independent nine-link
replay](overnight/transition-87109-replay.log) passed, exit 0, in 29.78s,
peak 68,864 KiB. The commands used respective 185- and 180-second outer
timeouts, the producer's 180-second signal budget, and a 1 GiB child
address-space cap. Exact commands are in the journal.

[heights.jsonl](overnight/heights.jsonl) has seventeen records, 7,145,796 bytes,
SHA-256 `6e0bd541aaeb7e9063056970cb8ad105c1141f77c69b6a371f566af29df0aab3`.
The new line adds 125,895 bytes; all 7,019,901 previous bytes are unchanged.
[transitions.jsonl](overnight/transitions.jsonl) has nine records, 393,892 bytes,
SHA-256 `01f435ecebc8da625b500675b92c87b63910ab3605afd16ca74a3582a1a9633b`.
The new line adds 43,757 bytes; all 350,135 previous bytes are unchanged.
The fixed caps remain 8 MiB and 512 KiB, with 1,242,812 and 130,396 bytes
of headroom. The [replay manifest](overnight/transition-verification.json),
[inventory](overnight/height-inventory.json) and completed
[checkpoint](overnight/transition-checkpoint.json) bind the new references.

## Derived finite plateau and basis data

The ninth selected-basis update is `[[8,0],[4,1]]`, namely
`f'=8*f, g'=4*f+g`, returning to the update at the earlier width-3 plateau.
These coordinates describe the stored algorithm-selected bases.
The [refreshed probe](overnight/basis-87109-chain.log) passed in 1.94s,
peak 69,264 KiB, under a 35-second timeout and its 30-second signal budget.
Its [report](overnight/basis-pattern-probe.json) checks eight adjacent maximal
plateau pairs. The new decrease from width 5 to width 3 adds a third finite
counterexample to nondecreasing widths. Seven equal-width pairs retain the
two unequal-update counterexamples. A maximal plateau requires independently
certified strict height changes on both sides; persistence and monotonicity
establish the constant interval. A witness change alone is insufficient.

All earlier extrapolation fields and eight chain links are preserved.
Repeating `f'=4*f, g'=2*f+g` every two bits through 90000 still fails actual
parity at index 87097 by both routes. No optimizer is called by the probe.
No Python/shell source changed; smoke already calls all relevant independent
checks and semantic, corruption, resumption and chain controls.

## Preserved earlier results and proof boundary

Both `L_5` and `L_6` boundary triplets and the earlier sparse samples remain
certified. The `80000..87091` plateau matches the k=5 shadow. Heights at
522546 and 522547 have 211,281 bits; the height at 522548 has 311,267 bits.
The all-level shadow-minimum argument is inherited written mathematics,
not a new theorem from these samples.

Raw-shadow levels 0..8 remain complete with gcds `[3,1,1,1,1,1,1,347,1]`.
At level 8, `S=1679616`, `L=18811699`, the raw numerator has 7,606,082 bits
and denominator 7,606,080 bits, with gcd 1. The return from 347 to 1 rejects
nondecreasing raw gcd; it establishes no asymptotic cancellation bound.
Raw-shadow evidence, manifest, checkpoint and original logs are unchanged.
Level 9 remains unattempted.

The new minimum and first failure are exact computation plus an independent
finite actual-parity/minimality certificate. Basis changes are derived exact
integer metadata. The plateau interpretation uses inherited written parity
and monotonicity arguments. Python exact arithmetic and the written
cylinder/basis identities are the trust boundary. No new written all-level
proof or Lean theorem was added. Exact `B`, asymptotic gcd cancellation and
remaining intermediate minima are open; no originality claim is made.

## Validation and continuation

The full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in
428.08s, peak 100,708 KiB, under a 750-second timeout and 1 GiB child cap.
It checked all seventeen heights, nine independent transitions, nine raw-shadow
levels, baseline arithmetic/parity, quick extended/basis regressions and all
existing corruption/resumption/falsification controls. Shell syntax, overnight
Python compilation and `git diff --check` passed. The
[checkpoint audit](overnight/checkpoint-audit.json) checks scope, references,
hashes, append-only preservation, preceding logs, sources and unchanged Git
refs. The prior checkpoint left its final smoke unrecorded; this run checks
both that eighth transition and the new ninth one. No older unrecorded pass
is claimed. No calculation remains running; no Lean, Rust or remote CI
result is claimed.

Next: locate the first actual parity mismatch of the stored `N=87112` witness
through 90000 and independently certify only a missing target minimum.
Exact arithmetic gives `H_87112 < H_90000`, with different primitive witnesses;
the next failure remains unresolved. Keep the evidence caps and check remaining
headroom. The journal gives bounded commands. Useful bounded work remains,
so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`096fcff4dda6facb604b57c3edfd8c82267ff743`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the next checkpoint. All edits stay within the three authorized paths;
original Phase 13 engines, PR #29, main, CI and papers are unchanged.
