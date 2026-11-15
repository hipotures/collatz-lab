# Phase 13 overnight research journal — issue #30

## Resume here

- Branch: `codex/phase13-overnight`. Local HEAD and cached origin ref at
  entry: `43a0f7c841851325fdd165611116224068fc54da`. PR #29 source:
  `65b087dc62e4950e1c504fe34865acaacb9188c9`. The host driver owns all
  commit/push operations. No Git mutation or remote access is authorized here.
- Entry was clean. Read the current plan, journal, theory Sections 5–9,
  original experiment/verifier modules, and overnight modules. The five
  existing samples were already certified and have not been recomputed.
- **Completed this iteration:** implemented `odd-box-basis-interval-v1` in
  the overnight producer and independent checker. The proof checks basis
  membership, determinant, denominator parity, an exhaustive coefficient
  bound, and tight integer interval endpoints. It rejects enumeration above
  4095; automatic mode falls back to the preserved floor-sum method.
- Compact-certificate validation **passed**: 27,540 directly enumerated
  boxes (18,792 empty, 8,748 nonempty), signed and zero coordinates, 13
  malformed cases rejected, explicit cap rejection and verified fallback.
  Alternative compact certificates passed for all 1,691 historical minima
  and all eight stored overnight minima. Evidence:
  `overnight/basis-validation.json`, `overnight/basis-validation.log`,
  `overnight/basis-final.log` (final eight-record source).
- Full extended regression **passed** after the certificate change: 511
  brute-force residues, all 1,691 historical minima/floor-sum certificates,
  four independent prefix/residue controls, seven corruptions rejected,
  `H_11=3`, `H_12=513`. Evidence: `overnight/compact-regression.log`.
- **New exact samples completed:** `N=522546,522547,522548` near `L_6`
  have minimum-height bit lengths `211281,211281,311267`. Each has a primitive
  positive odd denominator, actual parity witness, and independent exclusion
  of all smaller-height vectors. The first two witnesses and heights are
  identical, matching the inherited k=6 shadow coordinate hashes. The exact
  ratio satisfies `2^99985 <= H_522548/H_522547 < 2^99986`. These three
  samples must not be recomputed. Evidence: `overnight/l6-triplet.log` and
  the append-only `overnight/heights.jsonl`.
- Existing certified `N=80000,87090,87091,87092,90000` have exact-height
  bit lengths `35217,35217,35217,51875,51875`. Their original 4,052,103
  bytes remain an unchanged prefix, SHA-256
  `982adbab2ee61192a6666649e16c2167c141370fb67e726462cedfe725db9eaf`.
  The first three have the same primitive witness, so monotonicity gives a
  finite plateau `80000..87091`. The boundary height ratio lies in
  `[2^16657,2^16658)`. By `90000` the height and witness change again despite
  the unchanged height bit length. These earlier findings are preserved.
- The eight-record file is 6,012,761 bytes (below 8 MiB), SHA-256
  `fb2cc65ea9500a2d84f69c5c9db483143455d5058548400701e596f1f297db94`.
  Refreshed `overnight/height-inventory.json` verifies exact comparisons and
  the inherited k=5 and k=6 shadow hashes. Existing floor-sum transcripts
  were preserved; each new basis certificate enumerates exactly one positive
  odd coefficient (`C=1`). **Final overnight smoke passed, exit 0**,
  including independent witness/parity/minimality verification of all eight
  records and the inventory check. Evidence: `overnight/smoke.log`;
  final scope/preservation audit: `overnight/checkpoint-audit.json`.
- **Next research obligation:** exact raw-shadow gcd at
  k=8 with separate noncommutative matrix construction and independent replay,
  comparing k=0..7 signs/gcds/hashes against the inherited evidence; then
  basis-transition falsification. No gcd level beyond 7 is complete here.
  No hard blocker has been reached; useful bounded work remains, so no
  `COMPLETE` marker is justified.

## Scope and evidence levels

Read local `AGENTS.md`, `overnight/PLAN.md`, this journal, theory Sections 4–9,
the original engines/experiments/verifiers, `modular.json`, and current CI.
The user forbids remote access, so issue #30's local plan and supplied prompt
were used; no claim is made to have checked its current remote state.
All edits are within the three authorized paths. Original Phase 13 code,
Lean/Rust sources, CI, papers, main, PR #29, and other worktrees are untouched.
No agents or detached processes were spawned.

- **Exact computation:** an adaptive odd-denominator candidate solver with
  exact integer discrepancies, bounded at 600,000 bits.
- **Independent finite certificate:** literal substitution, reverse rational
  branches, actual numerator parities, primitive positive odd denominator,
  lattice determinant, and no vector at `H-1`, by floor-sum count or basis
  exclusion. The checker imports no optimizer or other project code. Full
  integers, Euclidean quotients, and interval endpoints use canonical
  hexadecimal strings in the bounded JSONL file.
- **Written proof:** the floor-sum counting/telescoping argument is the
  existing theory Section 4. The all-level shadow minimum in Section 8 is
  inherited, not a theorem discovered by an overnight sample. No new Lean
  proposition or formal proof was added. The coefficient-bound and integer
  interval argument in `overnight/README.md` is written elementary mathematics
  with an implemented independent checker and finite adversarial tests;
  it is not a Lean proof.
- **Open:** exact `B`, subexponential raw-gcd cancellation, and competing
  intermediate approximants. Finite data do not prove asymptotic behavior.

## Earlier checkpoint validation and resource observations

- Initial `timeout 150s /usr/bin/time -v python3 -B
  research/phase13/overnight/test_extended.py` failed promptly because the
  historical decimal JSON exceeds Python's default 4,300-digit conversion
  limit. Preserved output: `overnight/regression.log`. The test now sets a
  finite 20,000-digit limit; new evidence uses hex and needs no raised limit.
- The same full regression then passed under a 1 GiB child address-space
  cap: wall time 145.68 seconds, peak resident memory 74,448 KiB, exit 0.
  This is a local performance observation, not a complexity guarantee.
- `overnight/l5-triplet.log` records the bounded triplet command. Each sample
  gets at most 180 seconds including independent verification; the invocation
  additionally has a 550-second timeout and 1 GiB child address-space cap.
  For `N=87090`, residue construction took 0.269s, candidate construction
  1.400s cumulative, transcript generation 32.642s cumulative, and total
  verified publication 64.961s. These times are observations only.
  All three records completed, exit 0: 241.28 seconds total wall time,
  peak resident memory 102,988 KiB. Individual sample times were 64.961s,
  65.622s, and 110.660s. The JSONL after the triplet is 2,460,738 bytes;
  SHA-256 `9680e3a53d264a0be107edb2a8399ecaf7519f87bb5c9284a7c7370feec5a1cf`.
  `python3 -B research/phase13/overnight/summarize.py --write` records exact
  witness equality, integer jump bounds, and the inherited k=5 coordinate
  hashes without recomputing any historical shadow experiment.
- `timeout 550s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/extended_height.py --samples 80000 90000
  --seconds-per-sample 180 --write`, under the same 1 GiB cap, passed after
  independently rechecking and skipping the existing triplet. Wall time
  298.64s, peak resident memory 115,332 KiB, exit 0. New sample times were
  60.107s and 118.533s. Output: `overnight/l5-sparse.log`.
- The final five-record JSONL is 4,052,103 bytes, SHA-256
  `982adbab2ee61192a6666649e16c2167c141370fb67e726462cedfe725db9eaf`.
  The first three lines remain exactly the certified triplet. Regenerated
  `height-inventory.json` records exact comparisons and canonical coordinate
  hashes, plus the coefficient-bound preflight. It is derived metadata, not
  a substitute for the independent certificate checker.
- The earlier smoke prevented imported baseline modules from writing bytecode
  and ran a quick extended regression (first/final record of every historical
  family, all 511 small residues, parity controls and corruptions), plus the
  independent checker on every overnight record. The executed invocation was
  `timeout 450s /usr/bin/time -v bash research/phase13/overnight/smoke.sh`,
  under a 1 GiB child address-space cap. The per-iteration `smoke.log` and
  `checkpoint-audit.json` now describe the latest checkpoint instead.
  It passed, exit 0: wall time 223.81s, peak resident memory 94,592 KiB.
  Actual output confirms 25,432 signed floor sums, 4,095 exhaustive residues,
  31,750 signed parity cylinders, 262,400 direct `H_12` exclusions, seven
  corrupt baseline certificates rejected; then 511 extended brute-force
  residues, 20 historical first/final records, four independent prefix/residue
  controls, seven extended corruptions rejected; finally all five overnight
  witness/parity/minimality checks and the exact inventory check. Shell syntax,
  overnight Python compilation and `git diff --check` also passed. No Lean,
  Rust or remote CI check was run or claimed this turn.
- The earlier checkpoint audit confirmed the original triplet was preserved,
  the five expected sample IDs were unique, the final source hash matched the
  inventory, all changed paths were authorized, HEAD was unchanged, and no
  `COMPLETE` marker existed. The whitespace check passed. No calculation
  was left running at that handoff.

## Current iteration validation and resource observations

All timed commands below ran with a 1 GiB child address-space cap (`ulimit -v
1048576`), without changing the host configuration.

- `timeout 120s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/test_basis.py --write` passed, exit 0: 0.58s wall
  time and 79,812 KiB peak resident memory. The preflight log records the
  five-record source hash. After appending the triplet and strengthening the
  malformed zero-coordinate test to start from a valid empty-box certificate,
  the same command passed again, exit 0: 1.93s wall time and 83,700 KiB peak
  resident memory. `basis-final.log` and `basis-validation.json` record all
  eight current samples and the final source hash.
- `timeout 240s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/test_extended.py` passed, exit 0: 50.20s wall
  time and 76,204 KiB peak resident memory. All 1,691 original floor-sum
  certificates were checked as well as the new candidate certificates.
- `timeout 750s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/extended_height.py --samples 522546 522547 522548
  --seconds-per-sample 180 --certificate basis --write` passed, exit 0:
  499.28s total wall time, 123,024 KiB peak resident memory. New sample
  times including independent checking were 90.710s, 90.771s, 105.667s.
  Candidate construction finished at 53.128s, 53.029s, 53.654s; compact
  transcript construction finished at 53.134s, 53.034s, 53.667s. The total
  includes independently checking and skipping the five existing records.
  Evidence: `overnight/l6-triplet.log`. No sample exhausted its cap.
- `python3 -B research/phase13/overnight/summarize.py --write` passed on all
  eight samples. A separate exact check against the local HEAD blob confirmed
  that all 4,052,103 previous evidence bytes are unchanged; all eight IDs are
  unique. The new records use coefficient bound 1 and one exhaustive positive
  odd coefficient row. The three new records add 1,960,658 bytes, giving
  6,012,761 bytes in total, safely within the fixed 8 MiB cap.
- `timeout 650s /usr/bin/time -v bash research/phase13/overnight/smoke.sh`
  passed, exit 0: 350.18s wall time, 98,492 KiB peak resident memory.
  Output in `overnight/smoke.log` confirms the baseline arithmetic/parity
  regressions, quick extended and basis tests, all eight independent
  primitive witnesses/actual parity prefixes/no-smaller-height certificates,
  and the exact inventory check. The changed Python sources also compiled
  using `compile(...)` without writing bytecode; shell syntax and
  `git diff --check` passed. No Lean, Rust, or remote CI result is claimed
  for this iteration. No calculation is left running at this handoff.

## Concrete continuation

Read the current files and Git state before resuming. Do not recompute a
sample already independently certified in `heights.jsonl`. The triplet,
inventory, and final smoke are complete. Implement a bounded exact matrix
recurrence through raw-shadow level k=8 in separate
modules under `overnight/`, without editing the inherited Phase 13 modules.

Use `B_0=[[2,0],[0,1]]`, `B_1=[[2,-1],[0,3]]`, with the noncommutative
updates `B_0'=B_1^5 B_0` and `B_1'=B_1 B_0 B_0 B_1 B_1 B_1` evaluated
simultaneously. Compare all inherited k=0..7 gcds and coordinate hashes,
check negative numerator/positive odd denominator directly, and extend only
to k=8 initially under a per-level time cap and a 1 GiB child memory cap.
Store exact gcd, raw/reduced bit lengths and deterministic coordinate hashes,
not full giant raw integer strings. A separate implementation must replay
and check the new record before it is called independently verified.

If k=8 exhausts a resource cap, preserve a resumable matrix checkpoint and
record precisely which construction or gcd check is unfinished. Do not
promote a candidate, a timeout, or a finite gcd list to an asymptotic claim.
The next research priority after this is basis-transition falsification;
additional sparse samples must respect the 8 MiB height-evidence cap.

The host driver's quota polling and deadline are unchanged. Driver logs are
outside this checkout; evidence and command logs are under `overnight/`.
