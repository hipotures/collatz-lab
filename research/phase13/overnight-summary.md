# Phase 13 overnight computation — owner handoff

The eleventh intermediate witness transition after `L_5` is certified:
**`H_87112 < H_87113 = H_87114 = H_87115 < H_87116 < H_90000`**.
The actual 87113 witness first fails at zero-based index 87115, giving the
maximal width-3 plateau `87113..87115`. The consecutive certified widths are
**2, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3**. The new height has 51,875 bits; its
positive increase has 35,239 bits, with exact comparison
`1 < H_87116/H_87113 < 2`. These finite data establish no general plateau
law or asymptotic behavior.

Only the missing minimum at 87116 was computed. All eighteen previous height
records, ten previous transitions, raw-shadow artifacts and preceding command
logs are preserved. See [issue #30](https://github.com/hipotures/collatz-lab/issues/30),
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
Both routes agree on the positive 63,386-bit failing numerator, magnitude
SHA-256 `96bea349e80e184c8a641f8eebc16c4e492ac4cf08e925ae83c1c10ab9b0fd44`.

The [preflight](overnight/transition-87113-preflight.json) checked current
records, references and file capacity before computation. The
[computation log](overnight/transition-87113-compute.log) records a pass,
exit 0, in 7.68s, peak 113,428 KiB. The [independent eleven-link
replay](overnight/transition-87113-replay.log) passed, exit 0, in 35.78s,
peak 69,388 KiB. Commands used respective 185- and 180-second outer timeouts,
the producer's 180-second signal budget, and a 1 GiB child address-space cap.
Exact commands are in the journal.

[heights.jsonl](overnight/heights.jsonl) has nineteen records, 7,397,588 bytes,
SHA-256 `4d250b23e27b8cd5b916a5cc8464fa9de3ddc7e9f0019866743cf6d1a4bf4102`.
The new line adds 125,896 bytes; all 7,271,692 previous bytes are unchanged.
[transitions.jsonl](overnight/transitions.jsonl) has eleven records, 481,400 bytes,
SHA-256 `24ef2b65c32e804663b20833a7bb330e85a305674fd8f5ae725e7c4fb91a38a7`.
The new line adds 43,753 bytes; all 437,647 previous bytes are unchanged.
The [replay manifest](overnight/transition-verification.json),
[inventory](overnight/height-inventory.json) and completed
[checkpoint](overnight/transition-checkpoint.json) bind the new references.

## Derived finite plateau and basis data

The eleventh selected-basis update is `[[8,0],[4,1]]`, namely
`f'=8*f, g'=4*f+g`, matching the other two stored width-3 transitions.
These coordinates describe the stored algorithm-selected bases.
The [refreshed probe](overnight/basis-87113-chain.log) passed in 1.99s,
peak 70,016 KiB, under a 35-second timeout and its 30-second signal budget.
Its [report](overnight/basis-pattern-probe.json) checks ten adjacent maximal
plateau pairs, retaining four decreases, and twelve equal-width pairs,
retaining four unequal-update pairs. The new comparisons add no falsification.
A maximal plateau requires certified strict height changes on both sides;
a witness change alone is insufficient.

All preceding extrapolation fields and ten chain links are preserved.
Repeating `f'=4*f, g'=2*f+g` every two bits through 90000 still fails actual
parity at index 87097 by both routes. No optimizer is called by the probe.
No Python/shell source changed; smoke already calls the independent checks
and semantic, corruption, resumption and chain controls.

## Preserved results and proof boundary

Both `L_5` and `L_6` boundary triplets and earlier sparse samples remain
certified. The `80000..87091` plateau matches the k=5 shadow. Heights at
522546 and 522547 have 211,281 bits; the height at 522548 has 311,267 bits.
The all-level shadow-minimum argument is inherited written mathematics.

Raw-shadow levels 0..8 remain complete with gcds `[3,1,1,1,1,1,1,347,1]`.
At level 8, `S=1679616`, `L=18811699`, the raw numerator has 7,606,082 bits
and denominator 7,606,080 bits, with gcd 1. This finite result establishes no
asymptotic cancellation bound. Raw-shadow evidence and original logs are
unchanged. Level 9 remains unattempted.

The new minimum and first failure are exact computation plus an independent
finite actual-parity/minimality certificate. Basis changes are derived exact
integer metadata. Plateau interpretation uses inherited written parity and
monotonicity arguments. Python exact arithmetic and the written cylinder/basis
identities are the trust boundary. No new all-level written proof or Lean
theorem was added. Exact `B`, asymptotic gcd cancellation and remaining
intermediate minima are open; no originality claim is made.

## Validation and continuation

The full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in
435.96s, peak 101,660 KiB, under a 750-second timeout and 1 GiB child cap.
It checked all nineteen heights, eleven independent transitions, nine
raw-shadow levels, baseline arithmetic/parity, quick extended/basis
regressions and existing corruption/resumption/falsification controls.
Shell syntax, overnight Python compilation and `git diff --check` passed.
The [checkpoint audit](overnight/checkpoint-audit.json) records scope,
references, hashes, append-only preservation, all 48 previous command logs,
sources and unchanged Git refs. No calculation remains running; no Lean,
Rust or remote CI result is claimed.

Next: implement and independently test a second bounded transition segment,
its cross-segment references, capacity checks and interrupted-publication
controls. The existing 8 MiB height and 512 KiB transition caps stay fixed.
Remaining headroom is 991,020 and 42,888 bytes; another transition of the latest
size would exceed the transition cap. Preserve historical evidence byte for
byte and update the independent replay, derived probe and smoke for segments.
Then locate the first actual parity mismatch of the stored `N=87116` witness
through 90000 and independently certify only a missing target minimum.
Exact arithmetic gives `H_87116 < H_90000`, with different primitive witnesses;
its next failure remains unresolved. Do not run the current single-segment
producer with the new source before adding segment support. Useful bounded
work remains, so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`1b2161ccc62cf4d7a183ae676f71a1a083b2e8d5`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the next checkpoint. All edits stay within the three authorized paths;
original Phase 13 engines, PR #29, main, CI and papers are unchanged.
