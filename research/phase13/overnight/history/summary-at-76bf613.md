# Phase 13 overnight computation — owner handoff

The fifteenth intermediate witness transition after `L_5` is certified:
**`H_87120 < H_87121 < H_87122 < H_90000`**. The actual 87121 witness first
fails at zero-based index 87121, making 87121 another maximal singleton
plateau. Only the missing minimum at 87122 was computed. Its height has
51,875 bits; the positive increase has 35,243 bits, with exact comparison
`1 < H_87122/H_87121 < 2`. These are finite results.

## Exact computation and independent finite certificate

The [producer](overnight/witness_transition.py) used literal substitution and
actual numerator iteration. The [independent checker](overnight/verify_transitions.py)
used indexed substitution, reverse branches and exact discrepancy valuation.
They agree on failure index 87121 and the positive 63,386-bit failing numerator,
SHA-256 `8695e637548448cef5fb72cb4990878965a4bf3bdebb208e095f0276fb500f38`.
Both endpoint minima have checked primitive positive odd-denominator witnesses,
every actual parity and no-smaller-height certificates. The new exclusion has
coefficient bound 1 and one exhaustive odd row.

The [producer log](overnight/transition-87121-compute.log) passed, exit 0, in
7.70s, peak 117,416 KiB. The [fifteen-link replay](overnight/transition-87121-replay.log)
passed in 48.62s, peak 71,120 KiB. Producer signal/outer budgets were 180/185
seconds; replay had a 180-second outer timeout. Both used a 1 GiB child cap.
The [preflight](overnight/transition-87121-preflight.json),
[completed checkpoint](overnight/transition-checkpoint.json),
[inventory](overnight/height-inventory.json) and
[replay manifest](overnight/transition-verification.json) bind the evidence.

## Preserved evidence and capacity

The eleven-record [base segment](overnight/transitions.jsonl) remains sealed
at 481,400 bytes. [Segment 2](overnight/transitions-0002.jsonl) has four records
and 175,401 bytes, preserving all 131,553 preceding bytes. Its SHA-256 is
`419f2b217ee31ada351742cf6a1b2c4d2f04f5cafda79ba31b362d66c8bc8be5`.
The fixed 512 KiB cap leaves **348,887 bytes**; no third segment is supported.

[heights.jsonl](overnight/heights.jsonl) has twenty-three records and 7,901,178
bytes, SHA-256 `49b40df14814fa054a292c1d196324c3d301d3f1d2d3801557d8b2990fd9c026`.
All 7,775,280 previous bytes are preserved; one 125,898-byte line was appended.
The unchanged 8 MiB cap leaves **487,430 bytes**. Both exact proposed output
sizes were checked before publishing the new minimum. No Python/shell
implementation changed.

## Derived metadata and proof boundary

Fifteen maximal widths are **2,2,3,1,2,1,1,5,3,1,3,2,2,1,1**. The new
selected-basis update is `[[2,0],[1,1]]`. The
[probe](overnight/basis-87121-chain.log) passed in 2.05s, peak 71,524 KiB.
Fourteen adjacent pairs retain six decreases; twenty-eight equal-width pairs
include nine unequal updates. The earlier falsifications and fourteen prior
intervals remain intact. No replacement law follows.

The new minimum/failure are exact computation plus independent finite
certificates. Basis changes are derived integer metadata. Plateau maximality
uses inherited written parity and monotonicity arguments. No new all-level
written proof or Lean theorem was added. Python exact arithmetic and the
written identities remain the trust boundary. `L_5` and `L_6` triplets and
raw-shadow levels 0..8 remain complete; gcds stay `[3,1,1,1,1,1,1,347,1]`.
Level 9 is unattempted. Exact `B`, asymptotic cancellation and remaining
intermediate minima remain open. No asymptotic or originality claim is made.

## Validation and continuation

The full [overnight smoke test](overnight/smoke.log) **passed, exit 0**, in
**457.37s**, peak **102,176 KiB**, under a 750-second outer timeout and 1 GiB
child cap. It checked all twenty-three heights, fifteen transitions, nine
raw-shadow levels and existing arithmetic, parity, corruption, resumption,
segment and basis controls. Shell syntax, overnight Python compilation and
`git diff --check` passed. The [final audit](overnight/checkpoint-audit.json)
records scope, unchanged refs and sources, exact references/hashes, all prior
certificates and 63 historical command logs. No computation remains running.
No Lean, Rust or remote CI check was run or claimed.

Next reread local files and capacity, then locate the first actual failure of
the stored **`N=87122`** witness through 90000 and certify only its first
missing failing prefix. Its next failure is unresolved; its height is below
`H_90000`. Preserve both caps and the sealed base segment. Useful bounded
work remains; no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry HEAD/cached origin ref:
`bcfc2a7d9f57b8001b3041453ada7dc6ff08ae10`. No commit, push, remote access,
issue/PR edit, integration or publication occurred. The host driver owns
checkpoints. All edits stay within the authorized paths. Original Phase 13
engines, PR #29, main, CI, papers and other worktrees are untouched.
Remote [issue #30](https://github.com/hipotures/collatz-lab/issues/30) and
[PR #29](https://github.com/hipotures/collatz-lab/pull/29) state was neither
queried nor changed. The [journal](overnight-progress.md) records exact commands,
verified outcomes and the next obligation.
