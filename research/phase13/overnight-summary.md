# Phase 13 overnight computation — owner handoff

The twelfth intermediate witness transition after `L_5` is certified:
**`H_87115 < H_87116 = H_87117 < H_87118 < H_90000`**.
The actual 87116 witness first fails at zero-based index 87117, so
87116..87117 is a maximal width-2 plateau. Only the missing minimum at 87118
was computed. Its height has 51,875 bits; the positive increase has 35,241
bits and `1 < H_87118/H_87116 < 2`, by exact integer comparisons.
These finite data establish no asymptotic behavior.

## Exact computation and independent finite certificate

The [bounded producer](overnight/witness_transition.py) uses literal
substitution and actual numerator iteration. The [independent
checker](overnight/verify_transitions.py) uses indexed substitution, reverse
integer branches and exact 2-adic discrepancy valuation. Both routes agree
on failure index 87117 and the positive 63,384-bit failing numerator, SHA-256
`a44351a81ff4ef83f98b83747acbe985ee431bfce004573ef5007b0d2552f326`.
Both endpoint minima have primitive positive odd-denominator witnesses,
checked actual parities and no-smaller-height certificates; the new exclusion
uses one exhaustive odd coefficient row.

The [computation](overnight/transition-87116-compute.log) passed, exit 0,
in 7.59s, peak 114,796 KiB. The [separate twelve-link
replay](overnight/transition-87116-replay.log) passed, exit 0, in 38.94s,
peak 70,056 KiB. Commands had respective 185- and 180-second outer timeouts,
the producer's 180-second signal budget and a 1 GiB child address-space cap.
The [preflight](overnight/transition-87116-preflight.json), [completed
checkpoint](overnight/transition-checkpoint.json), [inventory](overnight/height-inventory.json)
and [replay manifest](overnight/transition-verification.json) bind the evidence.

## Tested second transition segment

The eleven historical transitions in [transitions.jsonl](overnight/transitions.jsonl)
are sealed and unchanged at 481,400 bytes. The new
[second segment](overnight/transitions-0002.jsonl) holds one 43,853-byte line,
SHA-256 `49fd0fd72a893a544a4e08bc8e01c152f55ba1754dd9d44ee05c2798dcf54235`.
Each segment keeps its fixed 512 KiB cap. The new record binds the exact
preceding line's hash across the boundary. Independent replay and the probe
bind both segment partitions and height-line hashes; their separate readers
reject duplicates, disconnected links and incorrect predecessor references.

Both proposed output sizes are checked exactly before a new height is
published. A durable located checkpoint covers the separate atomic writes.
Resumption after height publication reuses the target without another scan
or optimizer call. Resumption after transition publication independently
rechecks the link and completes the checkpoint without duplicating it.
The [new controls](overnight/segment-controls.log) passed 36 malformed-reader
rejections and nine publication/resumption/cap checks in tiny exact fixtures.
[Legacy controls](overnight/segment-legacy-controls.log) and the
[eleven-link replay before research](overnight/segment-legacy-replay.log) passed.
The [storage notes](overnight/README.md#two-segment-continuation) explain the format.

[heights.jsonl](overnight/heights.jsonl) now has twenty records, 7,523,485 bytes,
SHA-256 `e6c9f50df7c16938f443c9e7a0ffb375b0e6904e91b321daa53d64af4dceddd6`.
All 7,397,588 historical bytes are preserved. The fixed 8 MiB cap leaves
865,123 bytes; segment 2 leaves 480,435 bytes. Historical raw-shadow artifacts
and prior command logs are unchanged.

## Derived metadata and proof boundary

The twelve certified maximal plateau widths are
**2,2,3,1,2,1,1,5,3,1,3,2**. The latest selected-basis update is
`[[4,0],[2,1]]`. The [refreshed probe](overnight/basis-87116-chain.log)
passed in 1.97s, peak 70,492 KiB: eleven adjacent pairs give five width
decreases, including the new 3 to 2, and fifteen equal-width pairs retain
four unequal updates. Earlier extrapolation fields and all eleven old chain
intervals are preserved. These are coordinates of the stored selected bases.

The new minimum and failure are exact computation plus independent finite
certificates. Plateau interpretation uses inherited written parity and
monotonicity arguments; no new all-level written or Lean theorem was added.
Python exact arithmetic and the written cylinder/basis identities remain the
trust boundary. Earlier `L_5` and `L_6` triplets and raw-shadow levels 0..8
remain complete. Gcds stay `[3,1,1,1,1,1,1,347,1]`; level 9 is unattempted.
Exact `B`, asymptotic gcd cancellation and remaining intermediate minima
are open. No originality claim is made.

## Validation and continuation

Full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in 443.77s,
peak 101,740 KiB, under a 750-second outer timeout and 1 GiB child cap.
It checked all twenty heights, twelve transitions, nine raw-shadow levels,
new segment/cap/recovery controls and existing regressions. Shell syntax,
overnight Python compilation and `git diff --check` passed. The final
[checkpoint audit](overnight/checkpoint-audit.json) records scope, references,
hashes, all 51 preserved prior command logs and unchanged Git refs.
No computation remains running. No Lean, Rust or remote CI result is claimed.

Next: check current local evidence and capacity, then locate the first actual
failure of the stored `N=87118` witness through 90000 and independently
certify only a missing failing prefix. Its next failure remains unresolved;
exact arithmetic gives `H_87118 < H_90000`. The tested second segment is ready
for that request. Preserve the sealed first segment and both fixed caps.
Useful bounded work remains, so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry HEAD/cached origin ref:
`dbefca3041ead2a7fb98624cf579170ba5a4fe1e`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the checkpoint. All edits stay within the three authorized paths; original
Phase 13 engines, PR #29, main, CI, papers and other worktrees are untouched.
Remote [issue #30](https://github.com/hipotures/collatz-lab/issues/30) and
[PR #29](https://github.com/hipotures/collatz-lab/pull/29) state was neither
queried nor changed. See the [journal](overnight-progress.md) for exact
commands and the next obligation.
