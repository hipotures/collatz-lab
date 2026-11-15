# Phase 13 overnight computation — owner handoff

The tenth intermediate witness transition after `L_5` is certified:
**`H_87109 < H_87112 < H_87113 < H_90000`**. The actual 87112 witness first
fails at zero-based index 87112, so 87112 is a maximal singleton plateau,
following the width-3 plateau at `87109..87111`. The consecutive certified
widths are **2, 2, 3, 1, 2, 1, 1, 5, 3, 1**. The new height has 51,875 bits;
its positive increase has 35,236 bits, with exact comparison
`1 < H_87113/H_87112 < 2`. These finite data establish no general plateau
law or asymptotic behavior.

Only the missing minimum at 87113 was computed. All seventeen previous height
records, nine previous transitions, raw-shadow artifacts and preceding
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
and compact no-smaller-height certificates. The new certificate excludes all
smaller odd-denominator vectors using one exhaustive coefficient row.
Both routes agree on the positive 63,384-bit failing numerator, magnitude
SHA-256 `90c1bfc3ba1803217f45765c4c82fdc7e916343b4c551d2f347853d45c32b58d`.

The [computation log](overnight/transition-87112-compute.log) records a pass,
exit 0, in 7.55s, peak 112,572 KiB. The [independent ten-link
replay](overnight/transition-87112-replay.log) passed, exit 0, in 32.57s,
peak 69,196 KiB. Commands used respective 185- and 180-second outer timeouts,
the producer's 180-second signal budget, and a 1 GiB child address-space cap.
Exact commands are in the journal.

[heights.jsonl](overnight/heights.jsonl) has eighteen records, 7,271,692 bytes,
SHA-256 `c0f45c58a69a54d0aea8f66bfcb52cf0f40b49c956b1a5d977c26a54211f755b`.
The new line adds 125,896 bytes; all 7,145,796 previous bytes are unchanged.
[transitions.jsonl](overnight/transitions.jsonl) has ten records, 437,647 bytes,
SHA-256 `6884af2c1af24d7e6a4097fe931cabf1655c5dc4de6fff3392bf356fd9403485`.
The new line adds 43,755 bytes; all 393,892 previous bytes are unchanged.
The [replay manifest](overnight/transition-verification.json),
[inventory](overnight/height-inventory.json) and completed
[checkpoint](overnight/transition-checkpoint.json) bind the new references.

## Derived finite plateau and basis data

The tenth selected-basis update is `[[2,0],[1,1]]`, namely
`f'=2*f, g'=f+g`, returning to the update at the earlier singleton at 87102.
These coordinates describe the stored algorithm-selected bases.
The [refreshed probe](overnight/basis-87112-chain.log) passed in 1.95s,
peak 69,516 KiB, under a 35-second timeout and its 30-second signal budget.
Its [report](overnight/basis-pattern-probe.json) checks nine adjacent maximal
plateau pairs. The new decrease from width 3 to width 1 adds a fourth finite
counterexample to nondecreasing widths. Ten equal-width pairs contain four
unequal-update pairs; the new pairs are `(87099,87112)` and `(87103,87112)`.
A maximal plateau requires certified strict height changes on both sides;
a witness change alone is insufficient.

All previous extrapolation fields and nine chain links are preserved.
Repeating `f'=4*f, g'=2*f+g` every two bits through 90000 still fails actual
parity at index 87097 by both routes. No optimizer is called by the probe.
No Python/shell source changed; smoke already calls all relevant independent
checks and semantic, corruption, resumption and chain controls.

## Preserved results and proof boundary

Both `L_5` and `L_6` boundary triplets and earlier sparse samples remain
certified. The `80000..87091` plateau matches the k=5 shadow. Heights at
522546 and 522547 have 211,281 bits; the height at 522548 has 311,267 bits.
The all-level shadow-minimum argument is inherited written mathematics.

Raw-shadow levels 0..8 remain complete with gcds `[3,1,1,1,1,1,1,347,1]`.
At level 8, `S=1679616`, `L=18811699`, the raw numerator has 7,606,082 bits
and denominator 7,606,080 bits, with gcd 1. The return from 347 to 1 rejects
nondecreasing raw gcd; it establishes no asymptotic cancellation bound.
Raw-shadow evidence and original logs are unchanged. Level 9 is unattempted.

The new minimum and first failure are exact computation plus an independent
finite actual-parity/minimality certificate. Basis changes are derived exact
integer metadata. Plateau interpretation uses inherited written parity and
monotonicity arguments. Python exact arithmetic and the written cylinder/basis
identities are the trust boundary. No new all-level written proof or Lean
theorem was added. Exact `B`, asymptotic gcd cancellation and remaining
intermediate minima are open; no originality claim is made.

## Validation and continuation

The full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in
431.57s, peak 102,164 KiB, under a 750-second timeout and 1 GiB child cap.
It checked all eighteen heights, ten independent transitions, nine raw-shadow
levels, baseline arithmetic/parity, quick extended/basis regressions and all
existing corruption/resumption/falsification controls. Shell syntax, overnight
Python compilation and `git diff --check` passed. The
[checkpoint audit](overnight/checkpoint-audit.json) records scope, references,
hashes, append-only preservation, all 45 previous command logs, sources and
unchanged Git refs. No calculation remains running; no Lean, Rust or remote
CI result is claimed.

Next: locate the first actual parity mismatch of the stored `N=87113` witness
through 90000 and independently certify only a missing target minimum.
Exact arithmetic gives `H_87113 < H_90000`, with different primitive witnesses;
the next failure remains unresolved. Keep the fixed 8 MiB height and 512 KiB
transition caps. Remaining headroom is 1,116,916 and 86,641 bytes; at observed
record sizes only one more transition fits the current segment. Check projected
sizes before the next request and implement a separate bounded segment before
later transitions. The journal gives concrete bounded commands. Useful bounded
work remains, so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`d2862296f93ae2808289e834a9c45517cd77bc73`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the next checkpoint. All edits stay within the three authorized paths;
original Phase 13 engines, PR #29, main, CI and papers are unchanged.
