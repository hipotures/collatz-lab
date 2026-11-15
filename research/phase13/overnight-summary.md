# Phase 13 overnight computation — owner handoff

The thirteenth intermediate witness transition after `L_5` is certified:
**`H_87117 < H_87118 = H_87119 < H_87120 < H_90000`**.
The actual 87118 witness first fails at zero-based index 87119, giving a
maximal width-2 plateau at 87118..87119. Only the missing minimum at 87120
was computed. Its height has 51,875 bits; the positive increase has 35,243
bits, and `1 < H_87120/H_87118 < 2` by exact integer comparisons.
These finite data establish no asymptotic behavior.

## Exact computation and independent finite certificate

The [bounded producer](overnight/witness_transition.py) used literal
substitution and actual numerator iteration. The [separate
checker](overnight/verify_transitions.py) used indexed substitution, reverse
integer branches and exact 2-adic discrepancy valuation. Both routes agree
on failure index 87119 and the positive 63,385-bit failing numerator, SHA-256
`6de1f02a08b253980074d9e9d88ff06da5c628a62073f0427e5675d43dcdcc2d`.
Both endpoint minima have primitive positive odd-denominator witnesses,
checked actual parities and no-smaller-height certificates. The new exclusion
uses one exhaustive odd coefficient row.

The [computation](overnight/transition-87118-compute.log) passed, exit 0,
in 7.76s, peak 115,892 KiB. The [separate thirteen-link
replay](overnight/transition-87118-replay.log) passed, exit 0, in 42.54s,
peak 70,356 KiB. Their outer timeouts were 185 and 180 seconds; the producer
also had a 180-second signal budget. Both used a 1 GiB child address-space
cap. The [preflight](overnight/transition-87118-preflight.json), [completed
checkpoint](overnight/transition-checkpoint.json), [inventory](overnight/height-inventory.json)
and [replay manifest](overnight/transition-verification.json) bind the evidence.

## Preserved evidence and capacity

The eleven historical records in [transitions.jsonl](overnight/transitions.jsonl)
remain sealed at 481,400 bytes. The [second segment](overnight/transitions-0002.jsonl)
now holds two records, 87,704 bytes, preserving its first 43,853 bytes.
Its SHA-256 is `29e10c602a20ba4e28ece0e48c02c8bba25988d8fb5d8e9f670e62a1f11e1460`.
The new link binds its exact predecessor and both exact height-record lines.
Each segment retains its 512 KiB cap; segment 2 leaves 436,584 bytes.

[heights.jsonl](overnight/heights.jsonl) has twenty-one records, 7,649,382 bytes,
SHA-256 `f164d02c9912d83252083aa40f8ccb67f75ab511714c01710b93478782031301`.
All 7,523,485 previous bytes are preserved. The fixed 8 MiB cap leaves
739,226 bytes. Both proposed output sizes are checked before a new height
is published. No producer, checker or smoke implementation needed modification.

## Derived metadata and proof boundary

The thirteen certified maximal plateau widths are
**2,2,3,1,2,1,1,5,3,1,3,2,2**. The latest selected-basis update is
`[[4,0],[2,1]]`. The [probe](overnight/basis-87118-chain.log) passed in 1.99s,
peak 70,836 KiB: twelve adjacent maximal pairs retain five decreases, and
nineteen equal-width pairs retain four unequal updates. No new falsification
follows from the latest link. Earlier extrapolation fields and twelve old
chain intervals are preserved; these are coordinates of stored selected bases.

The new minimum and failure are exact computation plus independent finite
certificates. Plateau interpretation uses inherited written parity and
monotonicity arguments. No new all-level written or Lean theorem was added.
Python exact arithmetic and the written cylinder/basis identities remain the
trust boundary. Earlier `L_5` and `L_6` triplets and raw-shadow levels 0..8
remain complete. Gcds stay `[3,1,1,1,1,1,1,347,1]`; level 9 is unattempted.
Exact `B`, asymptotic gcd cancellation and remaining intermediate minima
are open. No originality claim is made.

## Validation and continuation

Full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in 449.94s,
peak 101,944 KiB, under a 750-second timeout and 1 GiB child cap. It checked
all twenty-one heights, thirteen transitions, nine raw-shadow levels and
existing regressions. Shell syntax, overnight Python compilation and
`git diff --check` passed. The [final audit](overnight/checkpoint-audit.json)
records scope, references, hashes, twelve preserved prior replay results and
basis intervals, 57 unchanged historical command logs, unchanged source
implementations and Git refs. No computation remains running.
No Lean, Rust or remote CI result is claimed.

Next: check current local evidence and capacity, then locate the first actual
failure of the stored `N=87120` witness through 90000 and independently
certify only its first missing failing prefix. Its next failure is unresolved;
exact arithmetic gives `H_87120 < H_90000`. Preserve the sealed first segment
and both fixed caps. Useful bounded work remains; no `COMPLETE` is justified.

Branch: `codex/phase13-overnight`; entry HEAD/cached origin ref:
`fcb95d6754967d4ae783a619b53a40ce0e405335`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the checkpoint. All edits stay within the three authorized paths; original
Phase 13 engines, PR #29, main, CI, papers and other worktrees are untouched.
Remote [issue #30](https://github.com/hipotures/collatz-lab/issues/30) and
[PR #29](https://github.com/hipotures/collatz-lab/pull/29) state was neither
queried nor changed. See the [journal](overnight-progress.md) for exact
commands and the next obligation.
