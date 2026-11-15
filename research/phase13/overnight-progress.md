# Phase 13 overnight research journal — issue #30

## Resume here

- Branch: `codex/phase13-overnight`. Entry local HEAD and cached origin ref:
  `6a65207193376deafdf1e4f9480efba648a4faca`. PR #29 source:
  `65b087dc62e4950e1c504fe34865acaacb9188c9`. Entry was clean. No Git
  mutation or remote access was performed; the host driver owns checkpoints.
- **Completed this iteration:** exact raw-shadow level `k=8` using signed
  noncommutative matrix products, followed by a separate positive-offset
  recurrence and split-denominator gcd replay. Both reconstructed and matched
  inherited levels `0..7`, including their gcds and coordinate hashes.
- **New exact finite result:** at `S_8=1679616`, `L_8=18811699`,
  `gcd(|P_8|,Q_8)=1`. The negative numerator and positive odd denominator
  have bit lengths `7606082,7606080`; reduced bit lengths are unchanged.
  The gcd list through level 8 is `[3,1,1,1,1,1,1,347,1]`. In particular,
  nondecreasing raw gcd is false already at `7 -> 8`. No asymptotic
  cancellation conclusion follows, and no new large-prefix parity/minimality
  sample at `L_8` is claimed.
- Evidence: `overnight/raw-shadows.jsonl` (9 records, 6,288 bytes, SHA-256
  `72088c34e8e8ac6666da741466fd8c244168350de12c124be38b086d849acad7`),
  `overnight/raw-shadow-verification.json`, and
  `overnight/raw-shadows-compute.log`, `overnight/raw-shadows-replay.log`.
  Both timed commands passed with exit 0 under a 1 GiB child memory cap.
  The matrix-ready emergency checkpoint has been replaced by compact
  completed status in `overnight/raw-shadow-checkpoint.json`.
- Small controls passed: 10 literal reverse-branch maps, 5 exact
  matrix/offset shadow comparisons, 37,800 signed split-gcd cases,
  20 rejected malformed records, and resumption before/after publication.
  Evidence: `overnight/raw-shadows-tests.log`. The new checker imports no
  producer or other project implementation.
- The eight existing certified height samples remain byte-for-byte
  unchanged: `N=80000,87090,87091,87092,90000,522546,522547,522548`.
  Their height bit lengths are `35217,35217,35217,51875,51875,211281,
  211281,311267`. File size is still 6,012,761 bytes; SHA-256
  `fb2cc65ea9500a2d84f69c5c9db483143455d5058548400701e596f1f297db94`.
  Earlier plateau and jump findings are preserved below and in the summary.
  Do not recompute these samples or the completed raw-shadow experiment.
- **Final overnight smoke passed, exit 0:** 389.32s wall time and
  98,896 KiB peak resident memory. It checked the baseline arithmetic/parity
  controls, quick extended/basis regressions, all eight independent height
  certificates, the exact inventory, and all nine raw-shadow replay records.
  Evidence: `overnight/smoke.log`; final scope/preservation/hashes:
  `overnight/checkpoint-audit.json`. No calculation remains running.
- **Next bounded research obligation:** basis-transition falsification
  inside `87092 < N <= 90000`. Using the stored primitive witness at 87092,
  find its first actual parity mismatch by 90000. This locates a concrete
  endpoint of witness persistence without a dense height scan. Independently
  certify a minimum at the first failing prefix if that prefix is not already
  stored; compare exact heights, allowing a change of witness at equal height.
  Preserve existing JSONL bytes and its 8 MiB cap. Details are in Concrete
  continuation below. Level `k=9` has not been attempted.
- Useful bounded work remains, so no `COMPLETE` marker is justified.

## Scope and evidence levels

Read local `AGENTS.md`, `overnight/PLAN.md`, this journal, theory Sections 4–9,
the original engines/experiments/verifiers, `modular.json`, and current CI.
The user forbids remote access, so issue #30's local plan and supplied prompt
were used; no claim is made to have checked its current remote state.
All edits are within the three authorized paths. Original Phase 13 code,
Lean/Rust sources, CI, papers, main, PR #29, and other worktrees are untouched.
No agents or detached processes were spawned.

- **Exact computation:** an adaptive odd-denominator candidate solver with
  exact integer discrepancies, bounded at 600,000 bits; and full signed
  noncommutative raw-shadow matrices through level 8.
- **Independent finite certificate:** literal substitution, reverse rational
  branches, actual numerator parities, primitive positive odd denominator,
  lattice determinant, and no vector at `H-1`, by floor-sum count or basis
  exclusion. The checker imports no optimizer or other project code. Full
  integers, Euclidean quotients, and interval endpoints use canonical
  hexadecimal strings in the bounded JSONL file. Separate raw-shadow replay
  uses expanded positive offsets and coprime denominator factors, comparing
  every stored coordinate hash, bit length, sign and gcd.
- **Written proof:** the floor-sum counting/telescoping argument is the
  existing theory Section 4. The all-level shadow minimum in Section 8 is
  inherited, not a theorem discovered by an overnight sample. No new Lean
  proposition or formal proof was added. The coefficient-bound and integer
  interval argument in `overnight/README.md` is written elementary mathematics
  with an implemented independent checker and finite adversarial tests;
  it is not a Lean proof. The expanded offset recurrences and split-gcd
  identity have the same written-arithmetic/Python trust boundary.
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

## Previous height-checkpoint validation and resource observations

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

## Raw-shadow checkpoint validation and resource observations

Commands used `ulimit -v 1048576` in their child shell. They did not change
host configuration. Each expensive level also had a 180-second signal budget.

- `timeout 60s /usr/bin/time -v python3 -B
  research/phase13/overnight/test_raw_shadows.py` passed, exit 0: 0.03s wall
  time, 20,480 KiB peak resident memory. It checked the ten literal maps,
  five exact matrix/offset shadow controls, 37,800 signed split-gcd inputs,
  twenty rejected corruptions and resumable matrix checkpoints. Evidence:
  `overnight/raw-shadows-tests.log`.
- `timeout 420s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/raw_shadows.py --through-level 8
  --seconds-per-level 180 --write` passed, exit 0: 54.27s total wall time,
  38,908 KiB peak resident memory. Level 8 took 52.620s including matrix
  construction, exact full-coordinate gcd and record publication. It matched
  every inherited level before publishing the new one. Evidence:
  `overnight/raw-shadows-compute.log`.
- `timeout 420s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_raw_shadows.py --write` passed, exit 0:
  41.79s total wall time, 37,588 KiB peak resident memory. Level 8 took
  40.496s. The separate checker expands positive offsets, reconstructs scalar
  denominators from letter counts, splits `Q=3^r_U*(b-2^S)` into coprime
  factors, and independently verifies all raw/reduced hashes and bit lengths.
  Ten literal inverse maps through level 4 also agree. Evidence:
  `overnight/raw-shadows-replay.log`, `overnight/raw-shadow-verification.json`.
- The checkpoint mechanism writes matrices before a level's gcd, accepts
  either an unfinished level or the preceding completed level on resume, and
  preserves all completed evidence lines. At the final level it writes compact
  completed status. The 64 KiB evidence cap and 8 MiB emergency checkpoint cap
  were respected. No timeout or mathematical blocker occurred this iteration.
- The strict finite inequality `2*height(y_8)^2 < 2^L_8` was checked in both
  arithmetic routes. This is a separation inequality for the reconstructed
  shadow coordinates, not a fresh independent check of 18,811,699 actual
  parity bits. The all-level match/minimum interpretation is the inherited
  written argument from theory Sections 5 and 8.

- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0: 389.32s wall time,
  98,896 KiB peak resident memory, under the same child memory cap. Output
  confirms 25,432 signed floor sums, 4,095 exhaustive residues, 31,750 signed
  parity cylinders, 262,400 direct `H_12` exclusions and seven rejected
  baseline corruptions; 511 extended brute-force residues, twenty historical
  first/final records, four independent prefix/residue controls and seven
  extended corruptions; 27,540 direct compact-box controls and thirteen
  malformed basis cases; all eight stored height certificates and the exact
  inventory; then the new raw-shadow tests and independent nine-level replay.
  Its final replay checked level 8 in 40.541s. Evidence: `overnight/smoke.log`.
- Overnight Python compilation without bytecode, shell syntax and
  `git diff --check` passed. Final local audit checks the entire eight-record
  height file against the entry HEAD blob, unchanged branch/HEAD/cached origin
  ref, authorized changed paths, and evidence/replay/checkpoint hashes.
  No Lean, Rust or remote CI check was run or claimed. No calculation remains
  running, and no commit, push, issue/PR mutation or external action occurred.

## Concrete continuation

Read the current plan, journal, modules, evidence and Git state before the
next step. The eight sparse height samples and raw-shadow level 8 are complete.
Do not rerun either producer to rediscover those results. Smoke may independently
recheck existing certificates; that is validation, not a new experiment.

The next useful step is a bounded transition experiment between the already
certified prefixes 87092 and 90000:

1. Read the primitive witness `(p,q)` and exact height at `N=87092` from
   `overnight/heights.jsonl`. Construct the literal fixed-word prefix through
   90000 independently of an optimizer. Iterate the actual rational numerator
   recurrence with the same positive odd denominator, recording the first
   mismatch index `t`. Do not infer the next transition from height bit lengths.
2. The existing witness and monotonicity certify persistence of the known
   minimum through prefix length `t`. A mismatch concerns this witness;
   it does not by itself prove that the next height strictly increases, since
   there could be another witness at the same height. Record this distinction.
3. If `t+1` is a new prefix length, compute its candidate and use the existing
   independent parity/basis-interval checker to certify its exact minimum.
   Compare the actual integers and witnesses. If `t+1=90000`, reuse that
   existing certificate. Keep each calculation signal/timeout bounded and
   memory capped, and preserve the height JSONL's existing bytes and 8 MiB cap.
4. Store only a small transition certificate and any genuinely new minimum;
   do not generate a dense profile. Add its independent verification to smoke.

This can falsify a fixed witness-persistence or plateau guess on a concrete
finite interval. It cannot decide `B=c`, asymptotic gcd size or the behavior
of other intervals. Level 9 is optional future research and has not been run;
this implementation deliberately caps its full-integer computation at level 8.
No hard blocker has been reached and no `COMPLETE` marker is warranted.

The host driver's quota polling and deadline are unchanged. Driver logs are
outside this checkout; evidence and command logs are under `overnight/`.
