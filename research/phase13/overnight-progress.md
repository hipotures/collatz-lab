# Phase 13 overnight research journal — issue #30

## Resume here

- Branch: `codex/phase13-overnight`. Entry local HEAD and cached origin ref:
  `291b5d2681cf0aab48c92764b65fc491e47c234b`. PR #29 source:
  `65b087dc62e4950e1c504fe34865acaacb9188c9`. Entry was clean. No Git
  mutation or remote access was performed; the host driver owns checkpoints.
- **Completed this iteration:** the first bounded witness transition after
  `L_5`. The stored primitive witness at `N=87092` matches exactly through
  prefix length **87093**, then fails at zero-based index **87093**. A new
  independent parity/minimality certificate gives **`H_87094 > H_87093 =
  H_87092`**. Both endpoint heights have 51,875 bits; their positive difference
  has 35,217 bits and `1 < H_87094/H_87092 < 2`. Equal bit lengths conceal
  this strict increase. No asymptotic conclusion follows.
- The forward actual-parity scan and independent reverse-branch discrepancy
  valuation agree. Compact basis/interval certificates independently exclude
  every smaller-height odd-denominator vector at both endpoints, so this is
  a strict minimum change, not merely a change of selected witness.
- Evidence: `overnight/transitions.jsonl` (one record, 43,773 bytes, SHA-256
  `385efdbd09c8c3f33392f2e40fda6bacd1d6d89c47f61ee2ec0928c1429cd63e`),
  `overnight/transition-verification.json`, `overnight/transition-compute.log`,
  `overnight/transition-replay.log`, and the completed
  `overnight/transition-checkpoint.json`. The complete computation took 7.92s
  and the independent replay 3.43s, both exit 0 under a 1 GiB child memory cap.
- Appended only the genuinely new `N=87094` certificate (125,891 bytes).
  All 6,012,761 bytes of the eight prior samples are unchanged. The nine-record
  file is now 6,138,652 bytes, SHA-256
  `00422d5cb5884ad1b0f015ff1b7969b8e31f1db2063bffa5ab4d2c6d477e9f80`,
  below the fixed 8 MiB cap. No historical sample was recomputed.
- Small controls passed: 5404 signed Fraction/valuation comparisons, including
  1364 no-failure cases; 68 small transition certificates, including two
  equal-height witness changes and 66 strict increases; eighteen rejected
  corruptions. Evidence: `overnight/transitions-tests.log`. A repeated completed
  request skipped calculation and preserved all evidence (`transition-skip.log`).
  Three additional temporary-fixture publication/resumption controls passed
  (`transition-resume-tests.log`); they forbid new scans and optimization.
- Earlier height triplets and the raw-shadow `k=8` result remain complete.
  The raw gcd list is `[3,1,1,1,1,1,1,347,1]`; its nine-line file and replay
  manifest remain byte-for-byte unchanged. Do not repeat either producer.
- **Final overnight smoke passed, exit 0:** 399.76s wall time, 99,100 KiB peak
  resident memory. It checked all nine height certificates, raw-shadow replay
  and the new transition semantic/corruption/resumption controls and replay.
  Evidence: `overnight/smoke.log`; scope/preservation/hashes:
  `overnight/checkpoint-audit.json`. No calculation remains running.
- **Next bounded research obligation:** scan the new `N=87094` witness through
  90000 and certify its first failing prefix only if absent. Its exact height
  and witness differ from those at 90000, so a larger transition remains
  unresolved. Do not infer its location from bit lengths. Preserve all prior
  height and transition evidence lines. Concrete command appears below.
  Level `k=9` has not been attempted.
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
  noncommutative raw-shadow matrices through level 8. The new bounded
  transition uses literal substitution and actual numerator iteration.
- **Independent finite certificate:** literal substitution, reverse rational
  branches, actual numerator parities, primitive positive odd denominator,
  lattice determinant, and no vector at `H-1`, by floor-sum count or basis
  exclusion. The checker imports no optimizer or other project code. Full
  integers, Euclidean quotients, and interval endpoints use canonical
  hexadecimal strings in the bounded JSONL file. Separate raw-shadow replay
  uses expanded positive offsets and coprime denominator factors, comparing
  every stored coordinate hash, bit length, sign and gcd. The new independent
  transition verifier imports only the independent height checker, reconstructs
  the word by indexed substitution, locates the failure by reverse-branch
  discrepancy valuation and verifies compact proofs of both endpoint minima.
- **Written proof:** the floor-sum counting/telescoping argument is the
  existing theory Section 4. The all-level shadow minimum in Section 8 is
  inherited, not a theorem discovered by an overnight sample. No new Lean
  proposition or formal proof was added. The coefficient-bound and integer
  interval argument in `overnight/README.md` is written elementary mathematics
  with an implemented independent checker and finite adversarial tests;
  it is not a Lean proof. The expanded offset recurrences and split-gcd
  identity have the same written-arithmetic/Python trust boundary. Witness
  persistence plus monotonicity gives the finite plateau at `87092..87093`;
  the cylinder-valuation derivation is written in the same README. No new
  universally quantified transition law or Lean theorem was introduced.
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

## Witness-transition validation and resource observations

All timed commands used a 1 GiB child address-space cap (`ulimit -v 1048576`).
The source was the clean entry checkpoint `291b5d2681cf0aab48c92764b65fc491e47c234b`.
The local issue plan and current files were reread before the new experiment;
remote access remained prohibited.

- `timeout 60s /usr/bin/time -v python3 -B
  research/phase13/overnight/test_transitions.py` passed, exit 0, 0.05s wall
  time and 20,784 KiB peak resident memory. The separate Fraction route checks
  signed rational states, no-failure cases and failure-at-zero indexing.
  Two equal-height witness changes prevent interpreting a failure alone as
  a height jump. The exact `H_11=3`, `H_12=513` control also passed.
- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87092 --through 90000
  --seconds 180 --write` passed, exit 0, 7.92s wall time and 106,720 KiB peak
  resident memory. The first failure was checkpointed at 1.572s; the genuinely
  new minimum at 87094 was independently checked and published by 4.480s.
  Full transition verification/publication finished at 7.882s. Source and
  target compact coefficient bounds are both 1, with one odd coefficient row.
  Evidence: `overnight/transition-compute.log`.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  3.43s wall time and 66,284 KiB peak resident memory. The exact reverse-branch
  discrepancy has 2-adic valuation 87093. The independently reconstructed
  failing numerator is positive, has 63,383 bits, and matches the scan's hash.
  No source or optimizer implementation is imported by this checker; its sole
  project import is the independent height-certificate verifier.
  Evidence: `overnight/transition-replay.log`, `transition-verification.json`.
- `python3 -B research/phase13/overnight/summarize.py --write` passed for all
  nine height records. The new exact height remains strictly below the stored
  `H_90000`, and the primitive witnesses differ. The first failure of this
  new witness has not been located.
- Repeating the completed producer request with `--seconds 10` under
  `timeout 15s` passed, exit 0, 0.07s wall time and 66,476 KiB peak resident
  memory. It skipped calculation. A separate exact comparison with the entry
  HEAD blob confirmed all eight original height records and all raw-shadow
  evidence bytes are unchanged; only one new height line was appended.
  The transition record hash was also unchanged. Evidence: `transition-skip.log`.
- The final expanded `test_transitions.py` passed under `timeout 60s`, exit 0,
  3.49s wall time and 41,616 KiB peak resident memory. In addition to all
  preceding semantic/corruption controls it exercised three publication paths
  in an automatically cleaned temporary fixture inside the authorized folder:
  resume from `located` with the target already published, byte-preserving
  completed reuse, and entry to the next request after a completed checkpoint.
  New scans, optimizer calls and height publication were forbidden in the
  fixture. The next request stopped before scanning the `87094` witness.
  Evidence: `overnight/transition-resume-tests.log`.
- A `located` checkpoint is published before expensive candidate work. On
  resume the producer reuses that location and any already-published target;
  the independent verifier rechecks the full claim before transition
  publication. After completion only the small completed checkpoint remains.
  No budget was exhausted and no mathematical blocker was encountered.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 399.76s wall time and
  99,100 KiB peak resident memory. It checked 25,432 signed floor sums,
  4,095 exhaustive residues, 31,750 signed parity cylinders, 262,400 direct
  `H_12` exclusions and seven malformed baseline certificates; 511 extended
  brute-force residues, twenty historical first/final records, four independent
  prefix/residue controls and seven extended corruptions; 27,540 direct compact
  boxes and thirteen malformed basis cases; all nine height/parity/minimality
  certificates and their inventory; raw-shadow controls and nine-level replay;
  and all new transition controls, three publication/resumption controls and
  independent first-failure/minimum replay. The raw level-8 replay took 40.458s.
  Evidence: `overnight/smoke.log`.
- All overnight Python modules compiled with `compile(...)` without bytecode;
  shell syntax and `git diff --check` passed. The final checkpoint audit checks
  unchanged branch/HEAD/cached ref, all eight prior height-record bytes, all
  raw-shadow data and manifests, the one new prefix, transition references and
  hashes, completed checkpoint, authorized changed paths and smoke exit status.
  No Lean, Rust or remote CI check was run or claimed. No calculation remains
  running. No Git mutation, issue/PR change, remote action or `COMPLETE` marker
  was made; the host driver owns commit/push.

## Concrete continuation

Read the current plan, journal, modules, evidence and Git state before the
next step. The nine sparse height samples, raw-shadow level 8 and first
post-`L_5` witness transition are complete. Do not repeat their producers.
Smoke may independently recheck certificates; that is validation.

The next useful step is one further bounded transition for the stored
`N=87094` witness, with search ending at 90000. It differs from the 90000
witness and has a strictly smaller height; locate its own first failure.
The completed old checkpoint may be replaced by this new request while
all existing transition and height lines remain append-only. Start with:

```bash
ulimit -v 1048576
timeout 185s /usr/bin/time -v python3 -B -u research/phase13/overnight/witness_transition.py --start 87094 --through 90000 --seconds 180 --write
timeout 180s /usr/bin/time -v python3 -B -u research/phase13/overnight/verify_transitions.py --write
python3 -B research/phase13/overnight/summarize.py --write
```

First check whether a later iteration has already certified this transition.
The producer computes a new minimum at `t+1` only when that prefix is absent.
The independent checker distinguishes a strict height increase from a
different witness at equal height. Refresh the replay manifest and inventory,
run smoke and check byte preservation before handoff. Keep the 8 MiB height
cap and 512 KiB transition cap; stop on a durable checkpoint if a budget is
exhausted. Do not generate a dense height profile.

This cannot decide `B=c`, asymptotic gcd size or behavior on other intervals.
Level 9 is optional future research and has not been run; the raw-shadow
implementation deliberately caps its full-integer computation at level 8.
No hard blocker has been reached and no `COMPLETE` marker is warranted.

The host driver's quota polling and deadline are unchanged. Driver logs are
outside this checkout; evidence and command logs are under `overnight/`.
