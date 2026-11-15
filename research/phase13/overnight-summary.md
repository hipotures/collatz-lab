# Phase 13 overnight computation — owner handoff

The fourteenth intermediate witness transition after `L_5` is certified:
**`H_87118 = H_87119 < H_87120 < H_87121 < H_90000`**.
The actual 87120 witness first fails at zero-based index 87120, so its maximal
plateau is the singleton 87120. Only the missing minimum at 87121 was computed.
The new height has 51,875 bits; the positive increase has 35,243 bits, with
`1 < H_87121/H_87120 < 2` by exact comparisons. These are finite results.

## Exact computation and independent finite certificate

The [producer](overnight/witness_transition.py) used literal substitution and
actual numerator iteration. The [independent checker](overnight/verify_transitions.py)
used indexed substitution, reverse branches and exact discrepancy valuation.
They agree on failure index 87120 and the positive 63,386-bit failing numerator,
SHA-256 `a475e4f17a713773a0ad9791fb436b0c39f416d741ca489378103f4792fa9a7b`.
Both endpoint minima have independently checked primitive positive odd-denominator
witnesses, actual parity prefixes and no-smaller-height certificates. The new
exclusion has coefficient bound 1 and one exhaustive odd row.

The [producer log](overnight/transition-87120-compute.log) passed, exit 0, in
7.77s, peak 116,608 KiB. The [fourteen-link replay](overnight/transition-87120-replay.log)
passed in 45.52s, peak 70,692 KiB. Outer timeouts were 185 and 180 seconds;
the producer also had a 180-second signal budget. Both used a 1 GiB child
address-space cap. The [preflight](overnight/transition-87120-preflight.json),
[completed checkpoint](overnight/transition-checkpoint.json),
[inventory](overnight/height-inventory.json) and
[replay manifest](overnight/transition-verification.json) bind the evidence.

## Preserved evidence and capacity

The eleven records in [transitions.jsonl](overnight/transitions.jsonl) stay
sealed at 481,400 bytes. [Segment 2](overnight/transitions-0002.jsonl) now has
three records and 131,553 bytes, preserving all 87,704 previous bytes.
Its SHA-256 is `1e8fe5fb090b78f52159564ec3878b826aad707b09210543b5e778602dc0bf9d`.
The new link binds the exact preceding transition and both height-record lines.
Its fixed 512 KiB cap leaves **392,735 bytes**. No third segment is supported.

[heights.jsonl](overnight/heights.jsonl) has twenty-two records, 7,775,280 bytes,
SHA-256 `eae238301bbda84072afaeb016f8070ad388a349c21d3a2d535d30d033ab6f63`.
All 7,649,382 previous bytes are preserved. The fixed 8 MiB cap leaves
**613,328 bytes**. Both exact proposed file sizes were checked before the new
height was published. No producer, checker or smoke implementation changed.

## Derived metadata and proof boundary

Fourteen certified maximal widths are **2,2,3,1,2,1,1,5,3,1,3,2,2,1**.
The selected-basis update is `[[2,0],[-1,1]]`. The
[probe](overnight/basis-87120-chain.log) passed in 2.00s, peak 71,116 KiB.
Thirteen adjacent maximal pairs include six decreases, adding 2 to 1 from
87118 to 87120. Twenty-three equal-width pairs include six unequal updates,
adding (87102,87120) and (87112,87120). The earlier extrapolation rejection
and all thirteen prior basis intervals are preserved. No replacement law follows.

The new minimum and failure are exact computation plus independent finite
certificates. Plateau interpretation uses inherited written parity and
monotonicity arguments. No new all-level written proof or Lean theorem was
added; Python exact arithmetic and the written identities remain the trust
boundary. The `L_5` and `L_6` triplets and raw-shadow levels 0..8 remain
complete, with gcds `[3,1,1,1,1,1,1,347,1]`. Level 9 is unattempted.
Exact `B`, asymptotic gcd cancellation and remaining intermediate minima are
open. Fourteen intervals establish no asymptotic behavior or originality claim.

## Validation and continuation

The full [overnight smoke test](overnight/smoke.log) **passed, exit 0**, in
**453.96s**, peak **102,376 KiB**, with a 750-second timeout and 1 GiB child
cap. It checked all twenty-two heights, fourteen transitions, nine raw-shadow
levels and existing semantic/corruption/resumption regressions. Shell syntax,
overnight Python compilation and `git diff --check` passed. The
[final audit](overnight/checkpoint-audit.json) checks scope, unchanged Git refs,
exact references and hashes, all earlier certificates, 60 historical command
logs and all source implementations. No computation remains running.
No Lean, Rust or remote CI check was run or claimed.

Next: reread current files and capacity, then locate the first actual failure
of the stored **`N=87121`** witness through 90000 and certify only its first
missing failing prefix. Its next failure is unresolved; its exact height is
below `H_90000`. Preserve both caps and the sealed first segment. Useful
bounded work remains; no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry HEAD/cached origin ref:
`68b38cf31ba28c4c8a8a1d6611473204fd08c05f`. No commit, push, remote access,
issue/PR edit, integration or publication occurred. The host driver owns
checkpoints. All edits stay within the authorized paths. Original Phase 13
engines, PR #29, main, CI, papers and other worktrees are untouched.
Remote [issue #30](https://github.com/hipotures/collatz-lab/issues/30) and
[PR #29](https://github.com/hipotures/collatz-lab/pull/29) state was neither
queried nor changed. The [journal](overnight-progress.md) records exact commands,
the initial unsupported read-only Git inspection and the next obligation.
