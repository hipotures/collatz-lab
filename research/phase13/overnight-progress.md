# Phase 13 overnight research journal — issue #30

## Resume here

- Branch: `codex/phase13-overnight`. Entry HEAD and cached origin ref:
  `68b38cf31ba28c4c8a8a1d6611473204fd08c05f`. PR #29 source:
  `65b087dc62e4950e1c504fe34865acaacb9188c9`. Entry was clean. No Git
  mutation or remote access occurred; the host driver owns commit/push.
- **Completed this iteration:** the actual `N=87120` witness first fails
  at zero-based index **87120**. Only the missing minimum at **87121**
  was computed. Exact finite results give
  **`H_87118 = H_87119 < H_87120 < H_87121 < H_90000`**.
  The maximal plateau at 87120 is a singleton. The new height has 51,875
  bits, its positive increase has 35,243 bits, and
  `1 < H_87121/H_87120 < 2` by exact integer comparisons.
- Literal forward iteration and the separate reverse-branch discrepancy
  valuation agree. Both endpoint minima have independently checked primitive
  positive odd-denominator witnesses, actual parities and no-smaller-height
  certificates. The positive failing numerator has 63,386 bits, SHA-256
  `a475e4f17a713773a0ad9791fb436b0c39f416d741ca489378103f4792fa9a7b`.
  The new exclusion has coefficient bound 1 and one exhaustive odd row.
- Producer and fourteen-link replay passed, exit 0, in 7.77s and 45.52s,
  peak 116,608 and 70,692 KiB. Evidence:
  `overnight/transition-87120-compute.log`, `transition-87120-replay.log`,
  `transition-verification.json`, `transition-87120-preflight.json` and
  the completed `transition-checkpoint.json`. Timeouts and the 1 GiB child
  address-space cap were respected.
- Twenty-two height records use 7,775,280 bytes, SHA-256
  `eae238301bbda84072afaeb016f8070ad388a349c21d3a2d535d30d033ab6f63`.
  All 7,649,382 previous bytes are preserved. The unchanged 8 MiB cap leaves
  **613,328 bytes**. Exactly one 125,898-byte line was appended.
- The sealed eleven-record base stays at 481,400 bytes, SHA-256
  `24ef2b65c32e804663b20833a7bb330e85a305674fd8f5ae725e7c4fb91a38a7`.
  Segment 2 has three records and 131,553 bytes, SHA-256
  `1e8fe5fb090b78f52159564ec3878b826aad707b09210543b5e778602dc0bf9d`.
  All 87,704 old segment-2 bytes are preserved; the new line is 43,849 bytes.
  Its fixed 512 KiB cap leaves **392,735 bytes**. Both exact output sizes
  were checked before publishing the new height. Do not append to the base,
  create a third segment or raise either cap.
- The fourteen maximal widths are **2,2,3,1,2,1,1,5,3,1,3,2,2,1**.
  The latest selected-basis update is `[[2,0],[-1,1]]`. The probe passed in
  2.00s, peak 71,116 KiB (`overnight/basis-87120-chain.log`): thirteen
  adjacent maximal pairs include six decreases; twenty-three equal-width
  pairs include six unequal updates. Old falsifications remain intact.
- **Validation passed:** `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh`, under a 1 GiB child cap, exit 0,
  **453.96s** wall time, peak **102,376 KiB**. All twenty-two heights,
  fourteen transitions, nine raw-shadow levels and existing regressions
  passed. Shell syntax, overnight Python compilation and `git diff --check`
  passed. Evidence: `overnight/smoke.log`, `overnight/checkpoint-audit.json`.
  All 60 historical command logs and all earlier replay results, basis
  intervals and journal sections are preserved. No computation is running.
- The `L_5` and `L_6` boundary triplets and raw-shadow levels 0..8 remain
  complete; gcds stay `[3,1,1,1,1,1,1,347,1]`. Level 9 is unattempted.
  No Python/shell implementation, original Phase 13 code, Lean/Rust, CI,
  main, PR #29, paper or other worktree was edited.
- **Evidence levels:** new results are exact computation and independent
  finite certificates. Basis comparisons are derived integer metadata;
  plateau maximality uses inherited written parity and monotonicity arguments.
  No new all-level written proof or Lean theorem was added. Exact `B`,
  asymptotic gcd cancellation and remaining intermediate minima stay open.
- **Next bounded obligation:** reread current files and capacity, then scan
  only the stored `N=87121` witness through 90000. Certify only its first
  missing failing prefix and independently replay it. Its next failure is
  unresolved; `H_87121 < H_90000` with distinct primitive witnesses. Do not
  repeat the 87120 producer or infer a failure from widths or basis updates.
  Useful bounded work remains; no `COMPLETE` marker is justified.

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
  every stored coordinate hash, bit length, sign and gcd. The independent
  transition verifier imports only the independent height checker, reconstructs
  the word by indexed substitution, locates the failure by reverse-branch
  discrepancy valuation and verifies compact proofs of both endpoint minima.
  The basis-pattern probe imports no project implementation. It compares
  exact basis coordinates, closed-form and repeated updates, literal actual
  parities, reverse-branch valuation and the failing numerator. Its result is
  an exact finite rejection of a specified extrapolation, not a minimum.
- **Written proof:** the floor-sum counting/telescoping argument is the
  existing theory Section 4. The all-level shadow minimum in Section 8 is
  inherited, not a theorem discovered by an overnight sample. No new Lean
  proposition or formal proof was added. The coefficient-bound and integer
  interval argument in `overnight/README.md` is written elementary mathematics
  with an implemented independent checker and finite adversarial tests;
  it is not a Lean proof. The expanded offset recurrences and split-gcd
  identity have the same written-arithmetic/Python trust boundary. Witness
  persistence plus monotonicity gives the finite plateau at `87092..87093`;
  the cylinder-valuation derivation is written in the same README. The next
  finite plateaux are `87094..87095`, `87096..87098`, the singleton
  `87099..87099`, and `87100..87101`, followed by the singletons at
  `87102` and `87103`, then `87104..87108`, `87109..87111`, and the singleton
  `87112`, then `87113..87115`, by the same monotonicity argument. Their
  strict left and right height changes make these maximal plateaux of lengths
  2, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3 on this finite chain.
  No new universally quantified transition law or Lean theorem was introduced.
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

## Second witness transition and basis-pattern probe

This iteration started from clean local HEAD and cached origin ref
`a51c4fe0819a2ce5d6c6b18b21d679f414fbdb1f`. It read current local instructions,
theory Sections 5–9, modules and evidence before choosing the absent transition.
The remote issue was not accessed because the user's instruction forbids it.
All timed commands below used a 1 GiB child address-space cap (`ulimit -v
1048576`); no host settings changed.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87094 --through 90000
  --seconds 180 --write` passed, exit 0: 7.94s wall time, peak 107,584 KiB.
  It located the failure at index 87095 after 1.568s, independently certified
  the new minimum at 87096 after 4.508s, and finished transition publication
  at 7.906s. The source and target compact coefficient bounds are both 1,
  with one exhaustive positive odd coefficient row. No old minimum was
  requested from the optimizer. Evidence: `transition-87094-compute.log`.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0:
  6.80s wall time, peak 66,580 KiB. The separate reverse-branch calculation
  verified both stored transitions and the new failure numerator: positive,
  63,384 bits, hash
  `190b24c45df4cf1ea17349c2e907856d9721ed7ef79cbeb90c3982ca7d9196d8`.
  It checked both referenced actual parity/minimality certificates per link.
  Evidence: `transition-87094-replay.log`, `transition-verification.json`.
- `python3 -B research/phase13/overnight/summarize.py --write` passed for
  all ten height records. Exact comparison gives `H_87096 < H_90000`, and
  their primitive witnesses differ. The new actual witness's next failure
  remains unresolved; the rejected extrapolated witness is a different vector.
- Implemented `probe_basis_pattern.py` to test one explicit finite prediction.
  Cramer's coordinates, independently checked by vector multiplication, give
  `[[4,0],[2,1]]` for each of the two observed selected-basis transitions.
  For `r=(90000-87092)/2=1454`, repetition predicts
  `f_r=4^r*f_0`, `g_r=g_0+2*(4^r-1)/3*f_0`. Exact stepwise updates agree with
  this closed formula. The resulting primitive positive odd-denominator vector
  has smaller height than `H_90000`, but is inadmissible: forward iteration
  first fails at 87097, and the independently computed reverse-branch
  discrepancy has valuation 87097. Reverse branches also reconstruct the same
  positive 63,383-bit failing numerator. The endpoint candidate is not the
  source witness at 87096. No new minimum at 87098 is claimed.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed initially
  in 1.66s, peak 66,632 KiB (`basis-pattern-probe.log`). After adding explicit
  known-prefix membership and the second failing-numerator reconstruction,
  the same bounded command passed in 1.81s, peak 66,704 KiB
  (`basis-pattern-final.log`). Both exited 0. The probe has its own 30-second
  signal budget and 32 KiB output cap. The final deterministic report is
  `basis-pattern-probe.json`; smoke replays it with `--check` and checks its
  source hashes. Neither run calls an optimizer or produces height records.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0: 404.91s wall time,
  peak 99,312 KiB. Its output confirms 25,432 signed floor sums, 4,095
  exhaustive residues, 31,750 signed parity cylinders, 262,400 direct `H_12`
  exclusions and seven malformed baseline certificates; 511 extended
  brute-force residues, twenty historical first/final records, four independent
  prefix/residue controls and seven extended corruptions; 27,540 direct compact
  boxes and thirteen malformed basis cases; all ten stored actual parity and
  minimum certificates plus inventory; raw-shadow controls and nine-level replay;
  5404 Fraction/valuation controls, 68 small transition certificates, eighteen
  corruptions and three publication/resumption controls; both large transition
  replays; and the two-route basis-pattern rejection. It also passed overnight
  Python compilation, shell syntax and `git diff --check`. No full historical
  producer, old sparse-sample producer or raw-shadow producer was repeated.
  Evidence: `smoke.log`.
- Final local audit compares all 6,138,652 prior height bytes and 43,773 prior
  transition bytes with entry HEAD, and checks unchanged raw-shadow evidence,
  manifests and previous transition logs; unchanged branch/HEAD/cached ref;
  unique new prefix 87096, matching references and completed checkpoint;
  source/evidence hashes and authorized changed paths. The final whitespace
  check also passed. Evidence: `checkpoint-audit.json`. No calculation remains
  running, and no Git mutation or remote action occurred.
- The first metadata-audit attempt stopped before writing because parsing
  `6:44.91` through binary floats produced `404.90999999999997`, which failed
  exact equality with the display value `404.91`. The resource parser was
  corrected to exact decimal arithmetic. This was a reporting assertion;
  every smoke/certificate check had already passed. No experiment was rerun.

The new independent minimum, finite extrapolation rejection, inherited written
proof arguments and open conjectures are separate evidence levels. No Lean,
Rust or remote CI result is claimed. No budget was exhausted or hard blocker
encountered; no `COMPLETE` marker is warranted.

## Three-prefix plateau validation and resource observations

Current files and local Git state were read before each research step. The
entry HEAD/cached ref is `05700214437a42e570128968356724bb7856622d`; issue #30's
local plan supplies scope while remote access is prohibited. All timed
commands below use `ulimit -v 1048576` only in their child shell.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87096 --through 90000
  --seconds 180 --write` passed, exit 0, 7.93s wall time, peak 108,244 KiB.
  Failure index 87098 was checkpointed at 1.568s; the new minimum at 87099
  was independently checked and published by 4.509s; complete publication
  finished at 7.891s. No other minimum was calculated. Evidence:
  `overnight/transition-87096-compute.log`.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  10.13s wall time, peak 66,908 KiB. Separate reverse integer branches
  verified all three transition records, both endpoint minima per link, and
  the latest positive 63,384-bit failing numerator. Evidence:
  `overnight/transition-87096-replay.log`, `transition-verification.json`.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all eleven records. Exact comparison shows `H_87099 < H_90000`
  and unequal primitive witnesses. No claim about their next failure follows.
- Implemented a finite chain summary in `probe_basis_pattern.py`: source-line
  hashes and replay results must match; consecutive links must join; Cramer's
  coordinates are checked by vector multiplication, signed determinants,
  lattice membership and denominator parity. The new update is `[[8,0],[4,1]]`.
  A constant interval becomes a maximal plateau only with certified strict
  height changes on both sides. The lengths 2, 2, 3 reject the precise
  constant-two-prefix claim on this chain; no general replacement is inferred.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.85s wall time, peak 67,160 KiB. The preserved extrapolation rejection at
  index 87097 is unchanged apart from source hashes and new derived fields.
  Evidence: `overnight/basis-chain-probe.log`, `basis-pattern-probe.json`.
- `timeout 60s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/test_transitions.py` passed, exit 0, 3.47s wall
  time, peak 42,164 KiB. In addition to all existing controls, a 31-link small
  chain is constructed from independently checked transitions. Its two tied
  witness changes do not falsely certify right plateau boundaries. Removing
  a known left boundary leaves it unclassified. Wrong replay intervals,
  changed source references, altered bases and disconnected links are rejected.
  Evidence: `overnight/basis-chain-controls.log`. Smoke already invokes this
  test and the updated probe; no extra historical producer is needed.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 410.70s wall time,
  peak 99,568 KiB. Actual output confirms baseline signed arithmetic, finite
  parity and `H_11=3`, `H_12=513` controls; quick extended and compact-box
  regressions; all eleven independent height certificates and exact inventory;
  raw-shadow controls and nine-level replay; all transition semantic,
  corruption and resumption controls; three independent large transition
  replays; and the preserved extrapolation plus new finite chain summary.
  Shell syntax, overnight Python compilation and `git diff --check` passed.
  Evidence: `overnight/smoke.log`. No old producer was repeated.
- Final local audit compares the first 6,264,543 height bytes and 87,545
  transition bytes with entry HEAD and verifies exactly one appended line in
  each file. Raw-shadow evidence/manifests/checkpoint and all old transition
  and probe logs remain unchanged. All preceding extrapolation-result fields
  are equal after excluding refreshed source hashes and the new chain field.
  Exact `H_87099 < H_90000`, the single odd-coefficient row, source references,
  completed checkpoint, unchanged branch/HEAD/cached ref and authorized changed
  paths are checked. Evidence: `overnight/checkpoint-audit.json`.
- Initial local inspection `git show-ref --remotes` failed because that option
  is unsupported; cached refs were then read with `git for-each-ref`. No fetch
  or remote access was attempted. No research, certificate or smoke check
  failed this iteration; no time or evidence cap was exhausted. No Lean,
  Rust or remote CI result is claimed. No calculation remains running.
- The first final metadata-consistency check stopped before changing evidence:
  a literal substring search for `pending` also matched the historical word
  `appending`. A whole-word check fixed this reporting-only assertion. All
  source/evidence hashes and the authorized changed-path inventory then matched;
  mathematical checks and smoke were already green. No experiment was rerun.

**Evidence levels:** the new sample is exact computation plus an independent
finite actual-parity/minimality certificate. Basis changes are exact integer
metadata; maximal-plateau interpretation uses the inherited written finite
monotonicity argument. No new Lean theorem or asymptotic statement was added.
`B=c`, asymptotic gcd cancellation and further intermediate minima remain open.

## Singleton plateau validation and resource observations

Current files, theory Sections 5–9, original Phase 13 engines, overnight
modules, certificates and local Git state were read before the research step.
Entry HEAD/cached ref is `26044953c3da434ca7a833ac3db717d0425f5aa4`.
Issue #30's local plan supplies scope; remote access is prohibited. All timed
commands below use `ulimit -v 1048576` only in their child shell.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87099 --through 90000
  --seconds 180 --write` passed, exit 0, 7.94s wall time, peak 108,660 KiB.
  Failure index 87099 was checkpointed at 1.578s; the new minimum at 87100
  was independently checked and published by 4.517s; complete publication
  finished at 7.904s. No other minimum was calculated. Evidence:
  `overnight/transition-87099-compute.log`.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  13.50s wall time, peak 67,076 KiB. Reverse integer branches independently
  verified all four transition records, both endpoint minima per link, and
  the latest positive 63,385-bit failing numerator. Evidence:
  `overnight/transition-87099-replay.log`, `transition-verification.json`.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all twelve records. Exact comparison shows `H_87100 < H_90000`
  and unequal primitive witnesses. The next actual failure remains unresolved.
- Extended `probe_basis_pattern.py` with the explicitly stated finite test
  that widths of consecutive certified maximal plateaux never decrease.
  It compares adjacent chain links only when both have independently certified
  strict height changes on both sides. The finite widths 2, 2, 3, 1 reject
  that claim at the pair beginning 87096 and 87099. Direct vector coordinates
  and signed determinants give the latest basis update `[[2,0],[-1,1]]`.
  This is selected-basis metadata, not an intrinsic or asymptotic recurrence.
- `timeout 60s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/test_transitions.py` passed, exit 0, 3.49s wall
  time, peak 42,368 KiB. The new control independently enumerates every
  constant-height run in the small complete profile; reported decreases agree
  with its exact widths and strict boundaries. Tied witness changes are
  excluded and an unknown left boundary cannot establish maximality.
  Existing 5404 Fraction/valuation controls, 68 small transition certificates,
  eighteen corruptions, three publication/resumption controls and four
  malformed-chain rejections also passed. Evidence:
  `overnight/width-decrease-controls.log`.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.89s wall time, peak 67,512 KiB. The old extrapolation rejection and all
  three preceding basis links remain unchanged; only source hashes and chain
  metadata are extended. Evidence: `overnight/basis-width-decrease.log`,
  `basis-pattern-probe.json`. No optimizer is called by the probe.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 414.37s wall time,
  peak 99,776 KiB. Actual output confirms all twelve independent height
  certificates and the inventory, four independent transition replays,
  nine-level raw-shadow replay, baseline signed arithmetic/parity and `H_12`
  controls, compact-box exclusions, and extended width-decrease controls.
  The preserved extrapolation also still fails at index 87097 by both routes.
  Shell syntax, overnight Python compilation and `git diff --check` passed.
  Evidence: `overnight/smoke.log`. No old producer was repeated.
- Final local audit compares the first 6,390,436 height bytes and 131,315
  transition bytes with entry HEAD and verifies exactly one appended line in
  each file. All 24 old command logs are unchanged, as are raw-shadow
  evidence/manifests/checkpoint and preceding extrapolation fields/chain links.
  Exact `H_87100 < H_90000`, the single odd-coefficient row, source references,
  completed checkpoint, unchanged branch/HEAD/cached ref, source/evidence
  hashes and authorized changed paths are checked. Evidence:
  `overnight/checkpoint-audit.json`. No calculation remains running.
- No research, certificate, smoke or reporting check failed this iteration;
  no time, memory or evidence cap was exhausted. No Lean, Rust or remote CI
  result is claimed. No Git mutation or remote action occurred.

**Evidence levels:** the new sample is exact computation plus an independent
finite actual-parity/minimality certificate. Basis changes and the explicit
width-decrease test are derived exact metadata; maximal-plateau interpretation
uses the inherited written finite monotonicity argument. No new Lean theorem
or asymptotic statement was added. `B=c`, asymptotic gcd cancellation and
further intermediate minima remain open.

## Fifth transition validation and resource observations

The current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before the bounded
step. Entry HEAD/cached origin ref is
`95fb0b67b3ca79382bc45db76d8263d1b1ea8323`. Issue #30's local plan supplies
scope while remote access is prohibited. All timed commands below use
`ulimit -v 1048576` only in their child shell.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87100 --through 90000
  --seconds 180 --write` passed, exit 0, 7.94s wall time, peak 109,356 KiB.
  First failure index 87101 was checkpointed at 1.576s. The sole new minimum,
  at 87102, was independently checked and published by 4.501s; transition
  publication finished at 7.905s. No earlier height sample was requested or
  republished. Evidence:
  `overnight/transition-87100-compute.log`.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  16.81s wall time, peak 67,268 KiB. Separate reverse-branch discrepancy
  valuation gives exactly 87101; reverse branches reconstruct the same
  positive 63,386-bit failing numerator. The replay independently checks
  all five links and actual parity/minimality certificates for both endpoints
  of every link. Evidence: `overnight/transition-87100-replay.log`,
  `transition-verification.json`.
- Exact comparison gives `H_87102 > H_87101 = H_87100 > H_87099`.
  The new height has 51,875 bits, its positive increase has 35,224 bits,
  and `1 < H_87102/H_87100 < 2`. The one new height line has 125,893 bytes;
  the one new transition line has 43,765 bytes. Direct comparison to the
  entry Git blobs confirms all 6,516,327 previous height bytes and all
  175,082 previous transition bytes are preserved verbatim.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all thirteen records. Exact arithmetic gives `H_87102 < H_90000`
  and different primitive witnesses. This does not locate the new witness's
  next failure.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.90s wall time, peak 67,840 KiB. Cramer's coordinates, direct vector
  multiplication, lattice membership and signed determinants give the new
  update `[[4,0],[2,1]]`. This selected-basis update returns after two other
  updates; it does not revive the already falsified constant-update claim.
  The five maximal plateau widths are 2, 2, 3, 1, 2. The earlier decrease
  from 3 to 1 and the rejected extrapolation at 87097 are unchanged. No
  probe source or control implementation needed modification. Evidence:
  `overnight/basis-87100-chain.log`, `basis-pattern-probe.json`.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 418.56s wall time,
  peak 100,104 KiB. Actual output confirms all thirteen primitive witness,
  actual-parity and no-smaller-height checks; five independent transition
  replays; nine raw-shadow levels; baseline signed arithmetic, `H_11=3`,
  `H_12=513` and corruption controls; quick extended and compact-box
  regressions; all transition semantic, corruption, resumption and width
  controls; and the preserved two-route extrapolation rejection. Shell syntax,
  overnight Python compilation and `git diff --check` passed. Evidence:
  `overnight/smoke.log`. No old experiment producer was repeated.
- Final local audit checks exactly one appended line in each evidence file,
  the unique new prefix 87102, source references, completed checkpoint and
  refreshed inventory/replay/probe hashes. All 28 old command logs, every
  producer/checker/smoke source, raw-shadow artifacts and the preceding four
  chain links are preserved. Branch/HEAD/cached origin ref are unchanged;
  all changed paths are authorized. Evidence: `overnight/checkpoint-audit.json`.
  No research, certificate or smoke check failed; no resource/evidence cap was
  exhausted. No calculation remains running. No Lean, Rust or remote CI result
  is claimed. No Git mutation or remote action occurred.

**Evidence levels:** the new minimum and failure are exact computation plus
an independent finite parity/minimality certificate. Basis coordinates are
derived exact metadata. The plateau interpretation uses the inherited written
monotonicity argument. No new Lean theorem, all-level transition theorem,
originality or asymptotic conclusion is claimed. `B=c`, asymptotic gcd
cancellation and further intermediate minima remain open.


## Sixth transition and equal-width basis falsification

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines, overnight modules and evidence were read before the step.
Entry HEAD/cached origin ref is `c214654df812331ed659fbf418ab65003557b574`.
The issue's local plan supplies scope; remote access is prohibited. All timed
commands below use `ulimit -v 1048576` only in their child shell.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87102 --through 90000
  --seconds 180 --write` passed, exit 0, 7.88s wall time, peak 109,996 KiB.
  First failure index 87102 was checkpointed at 1.568s; only the missing
  minimum at 87103 was independently checked and published, at 4.498s.
  Complete transition publication finished at 7.848s. Evidence:
  `overnight/transition-87102-compute.log`. No previous producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  19.94s wall time, peak 67,812 KiB. All six links and both actual parity/
  minimality endpoint certificates per link passed. Reverse branches give
  discrepancy valuation 87102 and reconstruct the same positive 63,385-bit
  failing numerator. Evidence: `overnight/transition-87102-replay.log` and
  `transition-verification.json`.
- Exact comparison gives `H_87103 > H_87102 > H_87101 = H_87100`.
  The new height has 51,875 bits, its positive increase has 35,226 bits,
  and `1 < H_87103/H_87102 < 2`. The new height line has 125,894 bytes;
  the new transition line has 43,765 bytes. Comparison with the entry Git
  blobs preserves all 6,642,220 old height bytes and 218,847 old transition
  bytes. Both fixed evidence caps are respected.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all fourteen records. Exact arithmetic gives `H_87103 < H_90000`
  and different primitive witnesses; it does not locate the next failure.
- An initial `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` refreshed the
  chain without changing the extrapolation. It passed, exit 0, 1.90s wall
  time, peak 68,216 KiB (`overnight/basis-87102-chain.log`). The sixth basis
  update is `[[2,0],[1,1]]`. Together with the earlier singleton's
  `[[2,0],[-1,1]]`, it supplies a useful finite falsification.
- Extended `probe_basis_pattern.py` with the explicit test that equal widths
  of certified maximal plateaux have equal selected-basis update matrices.
  Both strict height boundaries are required for every eligible interval.
  Four equal-width pairs are checked; 87099 and 87102, each of width 1,
  have different updates. The determinant is 2 in both, while the shear
  signs differ. This concerns the stored selected bases, not all bases of
  the lattices. No new minimum is computed by the probe.
- `timeout 60s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/test_transitions.py` passed, exit 0, 3.48s wall
  time, peak 43,128 KiB. New controls independently enumerate complete small
  height runs for pair eligibility and multiply raw basis vectors for update
  inequality. Tied witness changes and unknown left boundaries are excluded.
  Existing 5404 signed Fraction/valuation cases, 68 small transition
  certificates, eighteen corruptions, three resumption controls and four
  malformed-chain cases also passed. Evidence:
  `overnight/equal-width-update-controls.log`.
- The final bounded probe command passed, exit 0, 1.90s wall time, peak
  68,140 KiB (`overnight/basis-equal-width-probe.log`). Its previous
  extrapolation rejection, first five chain links and prior decreases are
  preserved. Six maximal plateau widths are 2, 2, 3, 1, 2, 1. Five adjacent
  pairs include decreases 3 to 1 and 2 to 1. No general replacement width
  or basis rule is inferred. Smoke already calls both updated checks.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 421.25s wall time,
  peak 100,404 KiB. Its actual output confirms all fourteen primitive witness,
  actual-parity and no-smaller-height checks, six independently replayed
  transitions, nine raw-shadow levels, baseline signed arithmetic and
  `H_11=3`, `H_12=513` controls, quick extended/compact-box regressions,
  corruption/resumption controls and both width/basis falsification checks.
  Shell syntax, overnight Python compilation and `git diff --check` passed.
  Evidence: `overnight/smoke.log`. No historical producer was repeated.
- Final local audit compares all previous height/transition bytes with entry
  Git blobs and checks exactly one new record per file, all source references,
  completed checkpoint, inventory/replay/probe hashes and the five old chain
  links. All 31 older command logs and raw-shadow artifacts are unchanged.
  Only the derived probe and its control source were extended; producers,
  independent minimum checkers, smoke and original Phase 13 files are
  unchanged. Branch/HEAD/cached origin ref are unchanged, and all changed
  paths are authorized. Evidence: `overnight/checkpoint-audit.json`.
- A documentation patch initially missed a wrapped line; it changed no
  evidence and was corrected. No research, certificate, control or smoke check
  failed; no resource cap was exhausted. No calculation remains running.
  No Git mutation or remote action occurred. No Lean, Rust or remote CI result
  is claimed.

**Evidence levels:** the new minimum and failure are exact computation plus
independent finite actual-parity/minimality certificates. Equal-width basis
falsification is derived exact integer metadata, checked by coordinate and
vector identities. Maximal-plateau interpretation uses the inherited written
monotonicity argument. No new Lean theorem, asymptotic result or originality
claim is made. Exact `B`, asymptotic gcd cancellation and further intermediate
minima remain open.

## Seventh transition validation and resource observations

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before the step.
Entry HEAD/cached origin ref is `8f9414e1f3cfb286e4e6de2e5bca01f7c290a3a2`.
Issue #30's local plan supplies scope; remote access is prohibited. All timed
commands below use `ulimit -v 1048576` only in their child shell.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87103 --through 90000
  --seconds 180 --write` passed, exit 0, 7.79s wall time, peak 110,572 KiB.
  First failure index 87103 was checkpointed at 1.568s; only the missing
  minimum at 87104 was independently checked and published, at 4.449s.
  Complete transition publication finished at 7.753s. Evidence:
  `overnight/transition-87103-compute.log`. No earlier producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  23.25s wall time, peak 68,236 KiB. All seven links and both actual parity/
  minimality endpoint certificates per link passed. Reverse branches give
  discrepancy valuation 87103 and reconstruct the same positive 63,385-bit
  failing numerator. Evidence: `overnight/transition-87103-replay.log` and
  `transition-verification.json`.
- Exact comparison gives `H_87104 > H_87103 > H_87102`, with
  `1 < H_87104/H_87103 < 2`. The new height has 51,875 bits; its positive
  increase has 35,225 bits. One new height line adds 125,892 bytes and one
  new transition line adds 43,763 bytes. All 6,768,114 old height bytes and
  262,612 old transition bytes remain intact, within both fixed evidence caps.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all fifteen records. Exact arithmetic gives `H_87104 < H_90000`
  and different primitive witnesses; the new witness's next failure is unresolved.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.93s wall time, peak 68,604 KiB. Coordinates, vector multiplication,
  lattice membership and determinants give `[[2,0],[-1,1]]` for the newest
  selected-basis update. Seven certified maximal plateau widths are
  2, 2, 3, 1, 2, 1, 1. Six adjacent pairs retain the two existing decreases;
  six equal-width pairs now include two unequal-update pairs. The earlier
  extrapolation rejection and all six old chain links are preserved. Evidence:
  `overnight/basis-87103-chain.log`, `basis-pattern-probe.json`. No optimizer
  is called by the probe; no source or control implementation needed changing.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 423.34s wall time,
  peak 100,528 KiB. Actual output confirms all fifteen primitive witness,
  actual-parity and no-smaller-height checks; seven independent transition
  replays; nine raw-shadow levels; baseline signed arithmetic and `H_11=3`,
  `H_12=513` controls; quick extended and compact-box regressions; transition
  corruption/resumption controls; and the preserved extrapolation, width and
  equal-width basis falsifications. Shell syntax, overnight Python compilation
  and `git diff --check` passed. Evidence: `overnight/smoke.log`.
- Final local audit preserves all previous height and transition bytes, checks
  exactly one new line per file, all source references, completed checkpoint,
  inventory/replay/probe hashes, unchanged extrapolation results and the six
  old chain links. All 36 older command logs, every Python/shell source, all
  raw-shadow artifacts and the historical journal sections are unchanged.
  Branch/HEAD/cached origin ref are unchanged; all changed paths are authorized.
  Evidence: `overnight/checkpoint-audit.json`. No calculation remains running.
- No research, certificate or smoke check failed; no resource or evidence cap
  was exhausted. No Git mutation, remote action, agents or detached processes
  occurred. No Lean, Rust or remote CI check was run or claimed. The host
  driver owns commit/push; issue #30 and PR #29 were not edited.
- The first final metadata audit stopped before writing: its broad unfinished-
  status word check matched the truthful sentence "No calculation remains
  running." The check was narrowed to unfinished smoke-status phrases. This
  was a reporting assertion; no mathematical check, experiment or smoke run
  was repeated. The corrected audit passed before handoff.

**Evidence levels:** the new minimum and first failure are exact computation
plus independent finite actual-parity/no-smaller-height certificates. Basis
coordinates are derived exact integer metadata; finite maximal plateaux use
the inherited written parity and monotonicity arguments. No new written
all-level theorem or Lean theorem was added. Exact `B`, asymptotic gcd size
and remaining intermediate minima remain open. Seven intervals do not determine
an asymptotic law. Useful bounded work remains; no `COMPLETE` marker is justified.

## Eighth transition and five-prefix plateau

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before the step.
Entry HEAD/cached origin ref is `4621523b29c0a156bb1ff72a3505b29cfd360639`.
Issue #30's local plan supplies scope; remote access is prohibited. All timed
commands below use `ulimit -v 1048576` only in their child shell.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87104 --through 90000
  --seconds 180 --write` passed, exit 0, 7.87s wall time, peak 111,252 KiB.
  First failure index 87108 was checkpointed at 1.556s; only the missing
  minimum at 87109 was independently checked and published, at 4.463s.
  Complete transition publication finished at 7.830s. Evidence:
  `overnight/transition-87104-compute.log`. No earlier producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  26.68s wall time, peak 68,564 KiB. All eight links and both actual parity/
  minimality endpoint certificates per link passed. Reverse branches give
  discrepancy valuation 87108 and reconstruct the same positive 63,385-bit
  failing numerator. Evidence: `overnight/transition-87104-replay.log` and
  `transition-verification.json`.
- Exact computation plus the inherited persistence/monotonicity argument gives
  `H_87103 < H_87104 = H_87105 = H_87106 = H_87107 = H_87108 < H_87109`.
  This new maximal plateau of width 5 is the longest in the stored chain.
  No minima at 87105..87108 were recomputed. The new height has 51,875 bits,
  its positive increase has 35,232 bits, and `1 < H_87109/H_87104 < 2`.
  One new height line adds 125,895 bytes and one new transition line adds
  43,760 bytes. All 6,894,006 old height bytes and 306,375 old transition
  bytes remain intact, within both fixed evidence caps.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all sixteen records. Exact arithmetic gives `H_87109 < H_90000`
  and different primitive witnesses; the new witness's next failure is unresolved.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.94s wall time, peak 68,896 KiB. Coordinates, vector multiplication,
  lattice membership and determinants give `[[32,0],[16,1]]` for the latest
  selected-basis update. Eight certified maximal plateau widths are
  2, 2, 3, 1, 2, 1, 1, 5. Seven adjacent pairs retain the two existing
  decreases; six equal-width pairs retain two unequal-update pairs. The
  earlier extrapolation rejection and all seven old chain links are preserved.
  Evidence: `overnight/basis-87104-chain.log`, `basis-pattern-probe.json`.
  No optimizer is called by the probe; no source or control change was needed.
- Final smoke and local scope/reference audit are still to be recorded.

**Evidence levels:** the new minimum and first failure are exact computation
plus independent finite actual-parity/no-smaller-height certificates. Basis
coordinates are derived exact integer metadata. The maximal-plateau deduction
uses the inherited written finite parity and monotonicity arguments. No new
written all-level theorem or Lean theorem was added. Exact `B`, asymptotic gcd
size and remaining intermediate minima remain open. Eight intervals do not
determine an asymptotic law. Useful bounded work remains; no `COMPLETE` is justified.

## Ninth transition and a further width decrease

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before the bounded
step. Entry HEAD/cached origin ref is `096fcff4dda6facb604b57c3edfd8c82267ff743`.
Issue #30's local plan supplies scope; remote access is prohibited. Each timed
command below used `ulimit -v 1048576` only in its child shell.

- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87109 --through 90000
  --seconds 180 --write` passed, exit 0, 7.79s wall time, peak 111,948 KiB.
  First failure index 87111 was checkpointed at 1.560s; only the missing
  minimum at 87112 was independently checked and published, at 4.447s.
  Complete transition publication finished at 7.751s. Evidence:
  `overnight/transition-87109-compute.log`. No earlier producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  29.78s wall time, peak 68,864 KiB. All nine links and both actual parity/
  minimality endpoint certificates per link passed. Reverse branches give
  discrepancy valuation 87111 and reconstruct the same positive 63,384-bit
  failing numerator with SHA-256 `80b4f02234fba60be3ea1f1fb9d8c365a8bbd5f21fcb84a80d8141e69895a0a6`.
  Evidence: `overnight/transition-87109-replay.log`, `transition-verification.json`.
  The new minimum's compact coefficient bound is 1 with one exhaustive odd row.
- Exact computation plus inherited persistence/monotonicity gives
  `H_87104 < H_87109 = H_87110 = H_87111 < H_87112`.
  This is a maximal plateau of width 3, following the width-5 plateau.
  No minimum at 87110 or 87111 was recomputed. The new height has 51,875 bits,
  its positive increase has 35,235 bits, and `1 < H_87112/H_87109 < 2`.
  One new height line adds 125,895 bytes and one transition line adds 43,757
  bytes. All 7,019,901 old height bytes and 350,135 old transition bytes remain
  intact. Totals are 7,145,796 and 393,892 bytes, within the fixed evidence caps.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all seventeen records. Exact arithmetic gives `H_87112 < H_90000`
  and different primitive witnesses; the new witness's next failure is unresolved.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.94s wall time, peak 69,264 KiB. Coordinates, direct vector multiplication,
  lattice membership and determinants give `[[8,0],[4,1]]` for the latest
  selected-basis update. Nine certified widths are 2, 2, 3, 1, 2, 1, 1, 5, 3.
  The eight adjacent pairs now include a third decrease, from 5 at 87104 to 3
  at 87109. Seven equal-width pairs retain the two unequal-update pairs.
  The old extrapolation rejection and all eight preceding chain links are
  preserved. Evidence: `overnight/basis-87109-chain.log`, `basis-pattern-probe.json`.
  No optimizer is called by the probe; no source/control change was needed.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 428.08s wall time,
  peak 100,708 KiB. Actual output confirms all seventeen primitive witnesses,
  actual parity prefixes and no-smaller-height certificates; all nine
  transition replays; nine raw-shadow levels; baseline signed arithmetic,
  `H_11=3`, `H_12=513` and corruption controls; quick extended and compact-box
  regressions; transition semantic/corruption/resumption controls; and the
  preserved extrapolation, width and equal-width basis falsifications.
  Shell syntax, overnight Python compilation and `git diff --check` passed.
  Evidence: `overnight/smoke.log`. No historical producer was repeated.
- At entry the summary and audit still described seven transitions, while
  the eighth journal section left smoke unrecorded. The full smoke just
  executed covers the eighth and ninth records. The earlier section is kept
  as history; no separate eighth-state smoke run is claimed retroactively.
- The local scope/reference audit checks byte preservation, exactly one new
  record per evidence file, refreshed manifests, completed checkpoint, all
  preceding chain links and extrapolation fields, raw-shadow artifacts,
  previous command logs, Python/shell sources and unchanged Git refs.
  Evidence: `overnight/checkpoint-audit.json`. All edits remain authorized.
  No calculation remains running. No resource/evidence cap was exhausted,
  no hard blocker occurred, and no Git mutation or remote action was made.
  The host driver owns commit/push; issue #30 and PR #29 were not edited.

**Evidence levels:** the new minimum and first failure are exact computation
plus independent finite actual-parity/no-smaller-height certificates. Basis
updates and pair comparisons are derived exact integer metadata. The finite
maximal-plateau deduction uses inherited written parity and monotonicity
arguments. No new written all-level theorem or Lean theorem was added.
Exact `B`, asymptotic gcd size and remaining intermediate minima remain open.
Nine intervals do not determine an asymptotic law. Useful bounded work remains;
no `COMPLETE` marker is justified.

## Tenth transition and another singleton plateau

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before the bounded
step. Entry HEAD/cached origin ref is `d2862296f93ae2808289e834a9c45517cd77bc73`.
Issue #30's local plan supplies scope; remote access is prohibited. All timed
commands below use `ulimit -v 1048576` only in their child shell.

- Preflight confirmed seventeen height records, nine transition records,
  absent source `87112`, a completed previous checkpoint and no `COMPLETE`.
  The clean isolated checkout has only the overnight cached origin ref; an
  initial query for cached `origin/main` failed because that ref is absent.
  `git for-each-ref` verified the relevant cached overnight ref. No remote
  state was queried, and no checkout, fetch or other Git mutation occurred.
  Headroom allowed reserves of 128 KiB for a height and 48 KiB for a transition.
- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87112 --through 90000
  --seconds 180 --write` passed, exit 0, 7.55s wall time, peak 112,572 KiB.
  First failure index 87112 was checkpointed at 1.497s; only the missing
  minimum at 87113 was independently checked and published, at 4.299s.
  Complete publication finished at 7.518s. Evidence:
  `overnight/transition-87112-compute.log`. No previous producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  32.57s wall time, peak 69,196 KiB. Separate reverse branches and discrepancy
  valuation locate the same first failure at 87112, reconstruct the same
  positive 63,384-bit numerator and check both actual parity/minimality
  endpoints on all ten links. Its magnitude SHA-256 is
  `90c1bfc3ba1803217f45765c4c82fdc7e916343b4c551d2f347853d45c32b58d`.
  Evidence: `overnight/transition-87112-replay.log`, `transition-verification.json`.
  The new minimum's coefficient bound is 1 with one exhaustive odd row.
- Exact endpoint minima give `H_87109 < H_87112 < H_87113 < H_90000`.
  The new maximal plateau is the singleton at 87112, following the certified
  `87109..87111` plateau. The new height has 51,875 bits, its positive increase
  has 35,236 bits, and `1 < H_87113/H_87112 < 2`. No intervening minimum was
  recomputed. A height line adds 125,896 bytes and a transition line adds
  43,755 bytes; every previous evidence byte is preserved. Totals are
  7,271,692 height bytes and 437,647 transition bytes. Fixed caps leave
  1,116,916 and 86,641 bytes, respectively. At these observed sizes only one
  further transition fits this segment; arrange a separate bounded segment
  before subsequent work, preserving the old evidence and fixed caps.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all eighteen records. Exact arithmetic gives `H_87113 < H_90000`
  with different primitive witnesses; the new witness's next failure is unresolved.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.95s wall time, peak 69,516 KiB. Determinants and direct vector identities
  give the tenth selected-basis update `[[2,0],[1,1]]`, returning to the
  update at 87102. The ten maximal widths are 2, 2, 3, 1, 2, 1, 1, 5, 3, 1.
  Nine adjacent pairs now include a fourth decrease, 3 to 1 from 87109 to
  87112. Ten equal-width pairs include four unequal-update pairs, adding
  `(87099,87112)` and `(87103,87112)`. The original extrapolation rejection
  and all nine earlier chain links remain unchanged. Evidence:
  `overnight/basis-87112-chain.log`, `basis-pattern-probe.json`.
  No optimizer is called by the probe; existing sources and controls suffice.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 431.57s wall time,
  peak 102,164 KiB. Actual output confirms all eighteen primitive witnesses,
  actual parity prefixes and no-smaller-height certificates, all ten large
  transition replays, nine raw-shadow levels, baseline signed arithmetic and
  `H_11=3`, `H_12=513` controls, quick extended/compact-box regressions,
  corruption/resumption/chain controls, and preserved basis falsifications.
  Shell syntax, overnight Python compilation and `git diff --check` passed.
  Evidence: `overnight/smoke.log`. This is certificate validation; no old
  large-sample or raw-shadow producer was repeated. No Lean, Rust or remote
  CI check was run or claimed.
- Local preservation checks against entry HEAD passed: all previous height
  and transition bytes, all nine old chain links, extrapolation fields,
  historical journal sections, raw-shadow artifacts and Python/shell sources
  are intact. The final audit records scope, unchanged Git refs, references,
  hashes and all 45 preceding command logs in `overnight/checkpoint-audit.json`.
  No calculation remains running, no cap was exhausted and no research or
  certificate check failed. No Git mutation, remote access, agents or detached
  processes occurred. The host driver owns commit/push; issue #30 and PR #29
  were not edited.

**Evidence levels:** the new minimum and first failure are exact computation
plus independent finite actual-parity/no-smaller-height certificates. Basis
updates and pair comparisons are derived exact integer metadata. The maximal
plateau interpretation uses inherited written parity and monotonicity
arguments. No new all-level written proof or Lean theorem was added.
Exact `B`, asymptotic gcd cancellation and remaining intermediate minima
remain open. Ten intervals do not determine an asymptotic law. Useful bounded
work remains; no `COMPLETE` marker is justified.

## Eleventh transition and a three-prefix plateau

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before the bounded
step. Entry HEAD/cached origin ref is `1b2161ccc62cf4d7a183ae676f71a1a083b2e8d5`.
Issue #30's local plan supplies scope; remote access is prohibited. Every
timed command below used `ulimit -v 1048576` only in its child shell.

- Preflight confirmed eighteen height records, ten transition records, no
  transition from 87113, a completed previous checkpoint and no `COMPLETE`.
  The clean isolated branch and cached origin ref agreed. Reserves of 128 KiB
  for one height and 48 KiB for one transition fit the unchanged fixed caps.
  Evidence: `overnight/transition-87113-preflight.json`. No remote query,
  fetch, checkout or other Git mutation was performed.
- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87113 --through 90000
  --seconds 180 --write` passed, exit 0, 7.68s wall time, peak 113,428 KiB.
  The first failure at index 87115 was checkpointed at 1.502s; only the
  missing minimum at 87116 was independently checked and published, at
  4.357s. Complete publication finished at 7.643s. Evidence:
  `overnight/transition-87113-compute.log`. No earlier producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  35.78s wall time, peak 69,388 KiB. Separate reverse branches and exact
  discrepancy valuation locate the same first failure at 87115 and reconstruct
  the same positive 63,386-bit failing numerator. Its magnitude SHA-256 is
  `96bea349e80e184c8a641f8eebc16c4e492ac4cf08e925ae83c1c10ab9b0fd44`.
  All eleven links received both endpoint actual-parity/minimality checks.
  Evidence: `overnight/transition-87113-replay.log`, `transition-verification.json`.
  The new minimum's coefficient bound is 1 with one exhaustive odd row.
- Exact endpoint minima and inherited persistence/monotonicity give
  `H_87112 < H_87113 = H_87114 = H_87115 < H_87116 < H_90000`.
  This is a maximal width-3 plateau at 87113..87115. No minimum at 87114
  or 87115 was recomputed. The new height has 51,875 bits, its positive
  increase has 35,239 bits, and `1 < H_87116/H_87113 < 2`.
  One height line adds 125,896 bytes and one transition line adds 43,753
  bytes. All 7,271,692 previous height bytes and 437,647 previous transition
  bytes are preserved verbatim. Totals are 7,397,588 and 481,400 bytes;
  fixed caps leave 991,020 height bytes and 42,888 transition bytes.
  Another transition of the latest size would exceed the transition cap.
  This is a file-capacity obligation for the next iteration, not a hard stop
  on useful research. Preserve both caps and all historical evidence.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all nineteen records. Exact comparison gives `H_87116 < H_90000`
  and different primitive witnesses; the new witness's next failure is unresolved.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.99s wall time, peak 70,016 KiB. Determinants and direct vector identities
  give the latest selected-basis update `[[8,0],[4,1]]`. The eleven certified
  maximal widths are 2, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3. Ten adjacent pairs
  retain four decreases; twelve equal-width pairs retain four unequal-update
  pairs. The new width-3 plateau adds two equal-update comparisons. No new
  falsification follows. The old extrapolation result and ten preceding
  chain links are preserved. Evidence: `overnight/basis-87113-chain.log`,
  `basis-pattern-probe.json`. No optimizer is called by the probe.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 435.96s wall time,
  peak 101,660 KiB. Actual output confirms all nineteen primitive witnesses,
  actual parity prefixes and no-smaller-height certificates; all eleven
  independent large transition replays; nine raw-shadow levels; baseline
  signed arithmetic and `H_11=3`, `H_12=513` controls; quick extended and
  compact-box regressions; corruption/resumption/chain controls; and the
  preserved basis falsifications. Shell syntax, overnight Python compilation
  and `git diff --check` passed. Evidence: `overnight/smoke.log`. No old
  large-sample or raw-shadow producer was repeated. No Lean, Rust or remote
  CI check was run or claimed.
- Final local audit checks all previous height and transition bytes, exactly
  one appended record per file, source references, completed checkpoint,
  refreshed inventory/replay/probe hashes, old extrapolation fields and ten
  earlier chain links. All 48 preceding command logs, every Python/shell
  source, raw-shadow artifacts and historical journal sections are unchanged.
  Branch/HEAD/cached origin ref remain unchanged, and all changed paths are
  authorized. Evidence: `overnight/checkpoint-audit.json`.
  No calculation remains running, no cap was exhausted and no research or
  certificate check failed. No Git mutation, remote access, agents or detached
  processes occurred. The host driver owns commit/push; issue #30 and PR #29
  were not edited.

**Evidence levels:** the new minimum and first failure are exact computation
plus independent finite actual-parity/no-smaller-height certificates. Basis
updates and pair comparisons are derived exact integer metadata. The maximal
plateau deduction uses inherited written finite parity and monotonicity
arguments. No new all-level written proof or Lean theorem was added.
Exact `B`, asymptotic gcd cancellation and remaining intermediate minima
remain open. Eleven intervals do not determine an asymptotic law. Useful
bounded work remains; no `COMPLETE` marker is justified.

## Twelfth transition with independently checked segments

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before research.
Entry HEAD/cached origin ref is `dbefca3041ead2a7fb98624cf579170ba5a4fe1e`.
Remote access is prohibited, so issue #30's local plan and supplied prompt
supply scope; no current remote issue/PR status is claimed.
Every timed command below used `ulimit -v 1048576` in its child shell.

- Added the fixed second segment `transitions-0002.jsonl`, preserving the
  first segment byte for byte and both 512 KiB caps. New links carry the
  exact preceding line's SHA-256. Producer, independent checker and probe
  use separately implemented readers, checking connected intervals,
  duplicate sources, cross-segment height references and predecessor hashes.
  Replay format v2 and the probe bind both segment partitions and their
  concatenation. Mathematical height/transition record formats remain v1.
- Before either evidence file is changed, the producer independently checks
  the proposed transition and both **exact output sizes**. A located
  checkpoint covers the separate atomic height, transition and completion
  writes. A published target is reused without optimization. A transition
  published before the completed checkpoint is independently rechecked and
  heals the checkpoint without another append. The base segment stays sealed.
- `timeout 60s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/test_transition_segments.py` passed, exit 0,
  0.07s wall time, peak 29,132 KiB. Three readers rejected 36 malformed-reader
  cases; nine publication/resumption/cap controls passed in tiny exact fixtures.
  Evidence: `overnight/segment-controls.log`. Smoke now invokes these controls.
- `timeout 60s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/test_transitions.py` passed, exit 0, 6.66s,
  peak 43,908 KiB. The 5,404 signed Fraction/valuation controls, 68 transition
  certificates, 18 corruptions, three legacy publication/resumption controls,
  31-link small chain and four malformed chains remain checked.
  Evidence: `overnight/segment-legacy-controls.log`.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` first passed for
  the eleven historical links, exit 0, 36.23s, peak 69,564 KiB. An exact
  comparison with entry HEAD confirmed every old result and evidence hash
  unchanged under the new reader. Evidence: `overnight/segment-legacy-replay.log`.
  This is certificate validation; no historical minimum was recomputed.
- Preflight re-read local evidence and confirmed nineteen heights, eleven
  links, no transition from 87116 and a completed previous checkpoint. It
  bound the entry SHA, source line, sealed segment and caps, with no remote
  access. Evidence: `overnight/transition-87116-preflight.json`.
- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87116 --through 90000
  --seconds 180 --write` passed, exit 0, 7.59s wall time, peak 114,796 KiB.
  The actual first failure at index 87117 was checkpointed at 1.504s;
  both sizes and the independent transition check passed before publication.
  Only the missing minimum at 87118 was published, at 7.556s. Evidence:
  `overnight/transition-87116-compute.log`. No old producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` then passed for
  all twelve links across the two segments, exit 0, 38.94s wall time,
  peak 70,056 KiB. Independent reverse branches and discrepancy valuation
  locate the same first failure at 87117 and positive 63,384-bit numerator,
  magnitude SHA-256
  `a44351a81ff4ef83f98b83747acbe985ee431bfce004573ef5007b0d2552f326`.
  Both endpoint minima have checked primitive positive odd-denominator
  witnesses, every actual parity and no-smaller-height proofs. The new
  coefficient bound is 1 with one exhaustive odd coefficient row. Evidence:
  `overnight/transition-87116-replay.log`, `transition-verification.json`.
- Inherited witness persistence and monotonicity give
  `H_87115 < H_87116 = H_87117 < H_87118 < H_90000`, a maximal width-2
  plateau at 87116..87117. The height has 51,875 bits and its positive
  increase 35,241 bits, with `1 < H_87118/H_87116 < 2`. No separate minimum
  at 87117 was computed. The one height line adds 125,897 bytes, leaving
  865,123 bytes under the unchanged 8 MiB cap. All nineteen historical lines
  are unchanged. The eleven-link base is unchanged at 481,400 bytes. The
  new segment uses 43,853 bytes, leaving 480,435 under its 512 KiB cap.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all twenty heights. Exact comparisons establish `H_87118 <
  H_90000` and different primitive witnesses; the new witness was not scanned
  beyond its certified prefix.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.97s wall time, peak 70,492 KiB. The selected-basis update is
  `[[4,0],[2,1]]`, checked by determinants and direct multiplication. Twelve
  maximal widths are 2,2,3,1,2,1,1,5,3,1,3,2. Eleven adjacent pairs give
  five decreases, including the new 3 to 2 at 87113 to 87116. Fifteen
  equal-width pairs retain four unequal updates. The old extrapolation
  result and all eleven previous intervals remain intact. Evidence:
  `overnight/basis-87116-chain.log`, `basis-pattern-probe.json`.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 443.77s wall time,
  peak 101,740 KiB. Actual output confirms all twenty primitive witnesses,
  actual parity prefixes and no-smaller-height certificates; all twelve
  transition replays across both segments; nine raw-shadow levels; baseline
  signed arithmetic and `H_11=3`, `H_12=513` controls; quick extended and
  compact-box regressions; new segment/cap/recovery controls; and all existing
  corruption/resumption/chain/falsification checks. Shell syntax, overnight
  Python compilation and `git diff --check` passed. Evidence: `overnight/smoke.log`.
  No historical height or raw-shadow producer was repeated. No Lean, Rust
  or remote CI check was run or claimed.
- Final preservation and scope audit checks all nineteen previous height
  lines, the sealed eleven-link base, the new cross-segment predecessor and
  exact height-line references, complete checkpoint, inventory/replay/probe
  hashes, all eleven old chain intervals and extrapolation fields. All 51
  prior command logs, raw-shadow artifacts and historical journal sections
  are unchanged. Branch/HEAD/cached origin ref are unchanged, all edits are
  authorized, no `COMPLETE` exists and no computation remains running.
  Evidence: `overnight/checkpoint-audit.json`. No check or computation failed
  this iteration. No Git mutation, remote access, agent or detached process
  occurred. The host driver owns commit/push; issue #30 and PR #29 are unchanged.

**Evidence levels:** the new minimum and first failure are exact computation
plus independent finite actual-parity/no-smaller-height certificates. Segment
hashes and basis comparisons are derived exact metadata. The maximal plateau
uses inherited written parity/cylinder and monotonicity arguments. No new
all-level written proof or Lean theorem was added. Exact `B`, asymptotic
raw-gcd cancellation and remaining intermediate minima stay open. Twelve
intervals do not determine an asymptotic law. Useful bounded work remains;
no `COMPLETE` marker is justified. The host driver owns commit/push.

## Thirteenth transition and a second consecutive width-two plateau

Current local instructions, plan, journal, theory Sections 5–9, original
Phase 13 engines and overnight modules/evidence were read before research.
Entry HEAD/cached origin ref is `fcb95d6754967d4ae783a619b53a40ce0e405335`.
Remote access is prohibited, so issue #30's local plan and supplied prompt
supply scope; no current remote issue/PR status is claimed. Timed commands
below use `ulimit -v 1048576` only in their child shell.

- The preflight re-read current evidence and confirmed twenty heights,
  twelve connected transitions across two segments, no transition from
  87118, and a completed preceding checkpoint. It bound the current height
  line, both segment hashes, the existing replay manifest, Git refs and
  entry file hashes. Reserves of 128 KiB for a height and 48 KiB for a
  transition fit the unchanged caps. Evidence:
  `overnight/transition-87118-preflight.json`. The initial read-only query
  for cached `origin/main` returned exit 128 because that ref is absent;
  `git for-each-ref` verified the relevant cached overnight ref. No remote
  query, fetch, checkout or other Git mutation occurred.
- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87118 --through 90000
  --seconds 180 --write` passed, exit 0, 7.76s wall time, peak 115,892 KiB.
  First failure index 87119 was checkpointed at 1.549s; only the missing
  minimum at 87120 was independently checked and published, at 7.729s.
  The separate exact output-size checks and independent endpoint/transition
  check passed before publication. Evidence:
  `overnight/transition-87118-compute.log`. No old producer was repeated.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  42.54s wall time, peak 70,356 KiB. All thirteen links and both endpoint
  parity/minimality certificates per link passed. The separate reverse
  branches and exact discrepancy valuation locate the same first failure
  at 87119 and positive 63,385-bit failing numerator, magnitude SHA-256
  `6de1f02a08b253980074d9e9d88ff06da5c628a62073f0427e5675d43dcdcc2d`.
  The new minimum's coefficient bound is 1, with one exhaustive odd row.
  Evidence: `overnight/transition-87118-replay.log`, `transition-verification.json`.
- Exact endpoint minima and inherited witness persistence/monotonicity give
  `H_87117 < H_87118 = H_87119 < H_87120 < H_90000`. The new maximal
  plateau is 87118..87119, width 2, following another width-2 plateau.
  No separate minimum at 87119 was computed. The new height has 51,875 bits,
  its positive increase has 35,243 bits, and `1 < H_87120/H_87118 < 2`.
  One height line adds 125,897 bytes; one segment-2 line adds 43,851 bytes.
  All 7,523,485 old height bytes and 43,853 old segment-2 bytes are intact;
  the sealed eleven-link base stays byte for byte unchanged. New totals
  are 7,649,382 height bytes and 87,704 segment-2 bytes, leaving 739,226
  and 436,584 bytes under their unchanged fixed caps.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all twenty-one heights. Exact comparisons give `H_87120 <
  H_90000` and different primitive witnesses. This does not locate the
  new actual witness's next failure.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  1.99s wall time, peak 70,836 KiB. Determinants and direct multiplication
  give the new selected-basis update `[[4,0],[2,1]]`. The thirteen maximal
  widths are 2,2,3,1,2,1,1,5,3,1,3,2,2. Twelve adjacent maximal pairs
  retain five decreases; nineteen equal-width pairs retain four unequal
  updates. No new falsification follows. Evidence:
  `overnight/basis-87118-chain.log`, `basis-pattern-probe.json`.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 449.94s wall time,
  peak 101,944 KiB. Actual output confirms all twenty-one primitive
  witnesses, actual parity prefixes and no-smaller-height certificates;
  all thirteen independent large transition replays; nine raw-shadow
  levels; baseline signed arithmetic and `H_11=3`, `H_12=513` controls;
  quick extended and compact-box regressions; corruption/resumption/chain
  and two-segment controls; and the preserved basis falsifications.
  Shell syntax, overnight Python compilation and `git diff --check` passed.
  Evidence: `overnight/smoke.log`. No historical producer was repeated.
  No Lean, Rust or remote CI check was run or claimed.
- The final preservation/scope audit records all twenty prior height lines,
  both old segment prefixes, the sealed base, exact height and predecessor
  references, completed checkpoint and refreshed inventory/replay/probe hashes.
  All twelve previous independent replay results and basis intervals,
  earlier extrapolation fields, historical journal sections, raw-shadow
  artifacts and 57 preceding command logs are preserved. Every Python/shell
  implementation is unchanged. Evidence: `overnight/checkpoint-audit.json`.
  Branch/HEAD/cached origin ref remain unchanged; edits are confined to the
  three authorized paths. No calculation remains running, no cap was
  exhausted and no research or certificate check failed. No Git mutation,
  remote access, agents or detached processes occurred. The host driver owns
  commit/push; issue #30 and PR #29 were not edited.

**Evidence levels:** the new minimum and first failure are exact computation
plus independent finite actual-parity/no-smaller-height certificates. Basis
updates and pair comparisons are derived exact integer metadata. The maximal
plateau deduction uses the inherited written parity and monotonicity arguments.
No new all-level written proof or Lean theorem was added. Exact `B`, asymptotic
raw-gcd cancellation and remaining intermediate minima stay open. Thirteen
intervals do not determine an asymptotic law. Useful bounded work remains;
no `COMPLETE` marker is justified. The host driver owns commit/push.

## Fourteenth transition and a further singleton plateau

Entry HEAD and cached origin ref were
`68b38cf31ba28c4c8a8a1d6611473204fd08c05f`. Current local instructions,
plan, journal, theory Sections 5–9 and existing Phase 13/overnight engines
and verifiers were read before research. Remote access is prohibited; the
supplied issue #30 instructions and local plan provide scope. No current
remote issue/PR status is claimed. All timed commands below used
`ulimit -v 1048576` only in their child shell.

- The bounded preflight confirmed twenty-one heights, thirteen connected
  transitions, no transition from 87120 and a completed previous checkpoint.
  It checked source-line references, replay and inventory hashes, both fixed
  segment names, the sealed base and capacity for one record per file.
  Evidence: `overnight/transition-87120-preflight.json`.
  Initial read-only `git show-ref --heads --remotes` returned exit 129
  because `--remotes` is unsupported. Cached refs were then verified with
  `git for-each-ref`; no fetch or other Git mutation occurred.
- `timeout 185s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/witness_transition.py --start 87120 --through 90000
  --seconds 180 --write` passed, exit 0, 7.77s wall time, peak 116,608 KiB.
  The first failure at index 87120 was checkpointed at 1.526s; the only
  missing minimum, at 87121, was independently checked and published at
  7.729s. Complete publication finished at 7.730s. Exact sizes of both
  proposed files and independent endpoint/transition checks passed before
  publication. Evidence: `overnight/transition-87120-compute.log`.
- `timeout 180s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/verify_transitions.py --write` passed, exit 0,
  45.52s wall time, peak 70,692 KiB. All fourteen links received both endpoint
  actual-parity/minimality checks. Indexed substitution, reverse branches and
  exact discrepancy valuation independently locate failure 87120 and the
  positive 63,386-bit failing numerator, magnitude SHA-256
  `a475e4f17a713773a0ad9791fb436b0c39f416d741ca489378103f4792fa9a7b`.
  The new minimum's coefficient bound is 1, with one exhaustive odd row.
  Evidence: `overnight/transition-87120-replay.log`, `transition-verification.json`.
- Exact endpoint minima, the preceding certificate and inherited
  persistence/monotonicity give
  `H_87118 = H_87119 < H_87120 < H_87121 < H_90000`.
  Thus 87120 is a maximal singleton plateau, following a width-2 plateau.
  The new height has 51,875 bits, the positive increase has 35,243 bits and
  `1 < H_87121/H_87120 < 2`. Only 87121 was sent to the minimum producer.
- The new height and segment-2 lines add 125,898 and 43,849 bytes.
  Every one of the 7,649,382 previous height bytes and 87,704 previous
  segment-2 bytes is preserved, as is the sealed 481,400-byte base segment.
  Totals are 7,775,280 and 131,553 bytes, leaving 613,328 and 392,735 bytes
  under the unchanged caps. Exact line hashes bind both endpoint heights
  and the preceding transition. The checkpoint is complete.
- `timeout 25s python3 -B research/phase13/overnight/summarize.py --write`
  passed for all twenty-two heights. A separate integer check confirms
  `H_87121 < H_90000` with different primitive witnesses. The new actual
  witness was not scanned beyond its certified prefix.
- `timeout 35s /usr/bin/time -v python3 -B -u
  research/phase13/overnight/probe_basis_pattern.py --write` passed, exit 0,
  2.00s wall time, peak 71,116 KiB. Determinants and direct multiplication
  give `[[2,0],[-1,1]]` for the new selected-basis update. Fourteen maximal
  widths are 2,2,3,1,2,1,1,5,3,1,3,2,2,1. Thirteen adjacent pairs include
  six decreases, adding 2 to 1 from 87118 to 87120. Twenty-three equal-width
  pairs include six unequal updates, adding pairs (87102,87120) and
  (87112,87120). This extends earlier finite counterexamples; no replacement
  law follows. All thirteen earlier intervals and extrapolation fields are
  unchanged. Evidence: `overnight/basis-87120-chain.log`, `basis-pattern-probe.json`.
- `timeout 750s /usr/bin/time -v bash
  research/phase13/overnight/smoke.sh` passed, exit 0, 453.96s wall time,
  peak 102,376 KiB. Actual output checks all twenty-two primitive witnesses,
  actual parity prefixes and no-smaller-height certificates; all fourteen
  transition replays; nine raw-shadow levels; baseline signed arithmetic,
  `H_11=3` and `H_12=513`; quick extended/compact-box regressions; and the
  corruption, resumption, chain, segment and basis-falsification controls.
  Shell syntax, overnight Python compilation and `git diff --check` passed.
  Evidence: `overnight/smoke.log`. No earlier large-sample or raw-shadow
  producer was repeated. No Lean, Rust or remote CI check was run or claimed.
- The final scope/preservation audit checks entry refs, both old segment
  prefixes, all twenty-one old height lines, exact predecessor/height
  references, complete checkpoint, refreshed manifests and source hashes.
  All thirteen prior replay results and basis intervals, historical journal
  sections, raw-shadow artifacts and 60 historical command logs are preserved.
  Every Python/shell implementation is unchanged. Evidence:
  `overnight/checkpoint-audit.json`. All edits remain in the authorized paths.
  No computation remains running, no resource cap was exhausted and no
  research or certificate check failed. No Git mutation, remote action,
  agent, detached process or host reconfiguration occurred. The host driver
  owns commit/push; issue #30 and PR #29 were not edited.

**Evidence levels:** the new minimum and failure are exact computation plus
independent finite actual-parity/no-smaller-height certificates. Basis updates
and comparisons are derived exact integer metadata. Maximality uses inherited
written parity and monotonicity arguments. No new all-level written proof or
Lean theorem was added. Exact `B`, asymptotic raw-gcd cancellation and remaining
intermediate minima stay open. Fourteen intervals do not determine an
asymptotic law. Useful bounded work remains; no `COMPLETE` is justified.

## Concrete continuation

Reread current local instructions, plan, journal, code, evidence and Git state
before each step; another Codex iteration may already have progressed.
Twenty-two sparse height records, fourteen post-`L_5` transitions and raw-shadow
levels 0..8 are complete. Do not repeat their producers. Smoke independently
rechecks certificates as validation.

Keep `transitions.jsonl` sealed byte for byte and the two fixed 512 KiB
segment caps. Append only to `transitions-0002.jsonl`; no third segment is
supported. Replay and probe bind both partitions and the cross-segment
predecessor; the checkpoint names its exact segment and line hash. Exact
height and transition sizes are checked before any new height is published.
Current headroom is **613,328 height bytes** and **392,735 second-segment
bytes**. Check it before another request; do not inflate caps to fit records.

The next bounded step is the actual first parity mismatch of the stored
`N=87121` witness through 90000, with a 180-second signal budget, outer timeout
and 1 GiB child cap. If the source has no transition, certify only its first
missing failing prefix `t+1`, independently replay, refresh inventory/probe
and run smoke. After checking current state, the producer command is:

```bash
ulimit -v 1048576
timeout 185s python3 -B research/phase13/overnight/witness_transition.py --start 87121 --through 90000 --seconds 180 --write
```

Exact comparisons give `H_87121 < H_90000` and distinct primitive witnesses;
the next failure index is unresolved. The actual 87120 witness failed at
index 87120. Earlier widths and basis shears do not determine the next failure.
Constant two-prefix widths, nondecreasing maximal widths and equal-width
determination of selected-basis updates remain falsified on this finite
chain; no replacement law follows.

This cannot decide `B=c`, asymptotic gcd size or behavior on other intervals.
Raw-shadow level 9 remains an optional alternative requiring separately
bounded resumable arithmetic: the current producer caps full-integer work
at level 8. No `COMPLETE` marker is warranted. No Git mutation, remote access,
agents, detached processes or host reconfiguration is authorized. The host
driver owns commit/push and its unchanged quota/deadline handling.
