# Phase 13 overnight computation — final owner handoff

The frozen evidence contains **24 exact rational-height minima, 16 certified
witness transitions, and nine raw-shadow levels k=0..8**. The sixteenth
transition is from **N=87122**, whose witness first fails at zero-based index
**87123**, to the certified minimum at **N=87124**:
`H_87121 < H_87122 = H_87123 < H_87124 < H_90000`.
The 87122..87123 plateau has width two. Both endpoint heights have 51,875
bits; the positive increase has 35,247 bits and `1 < H_87124/H_87122 < 2`.
These are finite results preserved from the original run, not new research.

## Sources and corrected provenance

The source is the immutable [overnight head 76bf613](https://github.com/hipotures/collatz-lab/commit/76bf6136c334c1db9e52e399fcc33fd4c20b9c24).
The integration base is [main 0190d57](https://github.com/hipotures/collatz-lab/commit/0190d57f43164ce2ec6016b3d3314c94ff98e06b),
which includes implementation PR #29 and independent referee PR #32.
[Issue #33](https://github.com/hipotures/collatz-lab/issues/33) repairs the
23-minima/15-transitions handoff identified in the
[independent report](../phase13-independent-referee-report.md), sections 8, 12, 13.
The old [summary](overnight/history/summary-at-76bf613.md) and
[audit](overnight/history/checkpoint-audit-at-76bf613.json) are preserved
byte-for-byte as historical snapshots; their entry HEAD, hashes and timing
attest the older checkpoint, not the final source head. See the
[history label](overnight/history/README.md).

The new [final audit](overnight/checkpoint-audit.json) binds the unchanged
source bytes, main's protected files, fresh command outputs and actual input
hashes. Its validation entry HEAD is a parent checkpoint plus an explicit
working-tree input manifest; it does not pretend to contain its own future
commit SHA. The PR head identifies the committed handoff.

## Unchanged evidence and capacity

| Artifact | Records | Bytes | SHA-256 |
|---|---:|---:|---|
| [heights.jsonl](overnight/heights.jsonl) | 24 | 8,027,076 | `08bcbb623aee8fd0bf8d6e6bcf919feed9e0cf171e2dafcb5ce89afbfc6c74a3` |
| [raw-shadows.jsonl](overnight/raw-shadows.jsonl) | 9 | 6,288 | `72088c34e8e8ac6666da741466fd8c244168350de12c124be38b086d849acad7` |
| [transitions-0002.jsonl](overnight/transitions-0002.jsonl) | 5 | 219,248 | `786cf600dc93222ab38fa1ef70cac3cb810840b188f6396f70b981ee0892e23e` |
| [transitions.jsonl](overnight/transitions.jsonl) | 11 | 481,400 | `24ef2b65c32e804663b20833a7bb330e85a305674fd8f5ae725e7c4fb91a38a7` |

Heights retain the 8 MiB cap, with 361,532 bytes free. The sealed first
transition segment retains all 11 records. Segment 2 retains five records;
its 512 KiB cap has 305,040 bytes free. No record was appended, recomputed or
rewritten, and no third segment was created. The final transition's positive
63,384-bit failing numerator has magnitude SHA-256
`4d36741dd00f16fa4a60d6f5c237bb03626c26401313dd2094ccea8ae8018324`.
The [completed checkpoint](overnight/transition-checkpoint.json),
[16-link replay](overnight/transition-verification.json),
[inventory](overnight/height-inventory.json) and
[final original replay log](overnight/transition-87122-replay.log) remain unchanged.

## Historical and current validation

The unchanged original [smoke.log](overnight/smoke.log) passed **24/16/9**,
exit 0, **464.54 seconds**, peak **102,832 KiB**, under the recorded
750-second outer timeout and 1 GiB child address-space cap. These are
historical observations, not the timing of the fresh integration checks.

| Current checked command | Exit | Wall seconds | Peak RSS KiB |
|---|---:|---:|---:|
| [combined-matrix](overnight/integration/combined-matrix.log) | 0 | 269.91 | 292976 |
| [combined-interfaces](overnight/integration/combined-interfaces.log) | 0 | 9.52 | 292848 |
| [overnight-smoke](overnight/integration/overnight-smoke.log) | 0 | 467.32 | 102696 |
| [pinned-referee](overnight/integration/pinned-referee.log) | 0 | 585.64 | 6288872 |

The current smoke uses a 750-second outer timeout and 1 GiB address-space cap.
The full current-main matrix checks Lean, the exact **653**-declaration axiom
allowlist, research interfaces, Rust formatting/lints/**94 tests**, all current
Python checkers and static manuscript/Lean-name consistency. Independent
interface/axiom parsing checks the actual combined tree. The unchanged
referee reproduction fetches its exact two pinned refs, checks all **1,691**
baseline minima, all **24** overnight minima, **16** transitions and raw gcds
through k=8, and byte-compares both committed reviewer result files.
All logs, timestamps, exit codes, caps and input fingerprints are in the
[validation ledger](overnight/integration/validation.json). CI status is
reported separately in the integration journal/PR, never inferred from a local run.

## Evidence boundary and owner decision

Primitive positive odd-denominator witnesses, actual signed numerator parities,
complete lattice exclusions and independent failure checks certify the finite
minima/transitions. Plateau maximality uses inherited written parity and
monotonicity arguments. The producer and original independent certification
scripts are unchanged. The merged mathematical referee report is unchanged;
the existing Lean statements and proofs are unchanged. No new Lean theorem,
mathematical priority, asymptotic law or publication readiness is claimed.
The general methods retain the source attribution in that report.

Widths remain `2,2,3,1,2,1,1,5,3,1,3,2,2,1,1,2`; earlier finite
counterexamples to nondecreasing widths and width-determined basis updates
remain intact. Raw gcds remain `[3,1,1,1,1,1,1,347,1]`. Exact B, asymptotic
gcd cancellation, remaining intermediate minima and the next failure of the
N=87124 witness are unresolved. Level 9 was not attempted.

The repair is ready for owner review after successful PR CI on the actual
integration head. No further computation is required for issue #33. Do not
resume the historical next-experiment instructions. No PR was merged, no issue
was closed, and the original branches were not moved. See the
[current journal](overnight-progress.md) and [finalization instructions](overnight/README.md#final-state-provenance).
