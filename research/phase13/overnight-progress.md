# Phase 13 overnight research journal — issue #30

## Resume here

- Branch: `codex/phase13-overnight`. Entry local HEAD and cached origin ref:
  `26044953c3da434ca7a833ac3db717d0425f5aa4`. PR #29 source:
  `65b087dc62e4950e1c504fe34865acaacb9188c9`. Entry was clean. No Git
  mutation or remote access was performed; the host driver owns checkpoints.
- **Completed this iteration:** the next bounded transition for the actual
  `N=87099` witness. It first fails at zero-based index **87099**, immediately
  beyond its certified prefix. The independently certified next minimum gives
  **`H_87100 > H_87099 > H_87098 = H_87097 = H_87096`**.
  The new height has 51,875 bits; its positive difference from `H_87099`
  has 35,223 bits and `1 < H_87100/H_87099 < 2`.
- Literal forward numerator iteration and independent indexed-substitution,
  reverse-branch discrepancy valuation agree. Both endpoint minima have
  checked actual parities, primitive positive odd denominators and compact
  no-smaller-height certificates. The failing numerator is positive, 63,385
  bits, SHA-256
  `a2d3c72ec2a9ac6d2ec195db49c49e8feb4bf3a15cd9c9b2a1d5b06368902e76`.
- Evidence: `overnight/transitions.jsonl` (four records, 175,082 bytes,
  SHA-256 `0cfdbc285eed7ccd825b5e002e0807890eae66667dad6d4ff1eca707bb4410be`),
  `overnight/transition-verification.json`, `overnight/transition-87099-compute.log`,
  `overnight/transition-87099-replay.log` and completed
  `overnight/transition-checkpoint.json`. Computation passed in 7.94s, peak
  108,660 KiB; separate replay of all four links passed in 13.50s, peak
  67,076 KiB. Both ran under a 1 GiB child address-space cap and bounded timeouts.
- Appended only the genuinely new `N=87100` height record (125,891 bytes).
  The twelve-record file is 6,516,327 bytes, SHA-256
  `080fc8f26a3b54d6a93dfdf39d28bde7d8ac5022a71040b86ae35bd85d22661d`.
  Preserve the prior 6,390,436 height bytes and 131,315 transition bytes
  verbatim; no historical minimum was recomputed. Both evidence caps remain
  fixed (8 MiB height, 512 KiB transition).
- **Finite plateau and basis falsification:** the four consecutive certified
  maximal plateaux are `87092..87093`, `87094..87095`, `87096..87098`,
  and `87099..87099`, of lengths **2, 2, 3, 1**. The fourth selected-basis
  update is exactly `f'=2*f, g'=g-f`, after `f'=8*f, g'=4*f+g`.
  The certified decrease from width 3 to 1 rejects nondecreasing maximal
  plateau widths on this finite chain. No replacement width law is inferred.
- Extended `overnight/probe_basis_pattern.py` records the three adjacent
  maximal plateau comparisons and the explicit width-decrease counterexample.
  Bounded replay passed in 1.89s, peak 67,512 KiB (`basis-width-decrease.log`).
  `overnight/width-decrease-controls.log` passed in 3.49s, peak 42,368 KiB:
  decreases in the 31-link independently certified small chain agree with
  directly enumerated complete height runs. Tied witness changes and unknown
  left boundaries do not certify maximality. Existing semantic, corruption
  and resume controls also passed. Smoke already calls the extended checks.
- Earlier height triplets and raw-shadow `k=8` remain complete. Raw gcds:
  `[3,1,1,1,1,1,1,347,1]`. Raw-shadow evidence and all preceding transition
  and basis command logs are preserved. Do not repeat those producers.
  Level `k=9` is unattempted.
- **Final overnight smoke passed, exit 0:** 414.37s wall time, 99,776 KiB
  peak resident memory, under a 750-second timeout and 1 GiB child cap. It
  checked all twelve height certificates, four independent transition replays,
  nine-level raw-shadow replay, baseline/basis regressions and the extended
  width-decrease controls. Evidence: `overnight/smoke.log`. Final scope,
  byte-preservation and source hashes: `overnight/checkpoint-audit.json`.
  No calculation remains running.
- **Next bounded research obligation:** scan the actual new `N=87100` witness
  through 90000 and certify only its first failing prefix if absent. Exact
  arithmetic gives `H_87100 < H_90000` and different primitive witnesses;
  that witness's next failure is unresolved. Do not infer it from bit lengths,
  plateau widths, or the rejected extrapolated candidate. Concrete command
  appears below. Useful bounded work remains; no `COMPLETE` marker is justified.

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
  The new basis-pattern probe imports no project implementation. It compares
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
  finite plateaux are `87094..87095`, `87096..87098`, and the latest singleton
  `87099..87099`, by the same monotonicity argument. Their strict left and
  right height changes make these maximal plateaux of lengths 2, 2, 3, 1
  on this finite chain. No new universally quantified transition law or Lean
  theorem was introduced.
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

## Concrete continuation

Read the current plan, journal, modules, evidence and Git state before the
next step. Twelve sparse height samples, raw-shadow level 8 and the first
four post-`L_5` transitions are complete. Do not repeat their producers.
Smoke may independently recheck certificates; that is validation.

The next useful step is one bounded transition for the stored `N=87100`
witness, with search ending at 90000. Its height is strictly below the 90000
minimum and its witness differs. The next failure remains unresolved. The
completed checkpoint may be replaced by a new request while every existing
height and transition evidence line remains append-only. Start with:

```bash
ulimit -v 1048576
timeout 185s /usr/bin/time -v python3 -B -u research/phase13/overnight/witness_transition.py --start 87100 --through 90000 --seconds 180 --write
timeout 180s /usr/bin/time -v python3 -B -u research/phase13/overnight/verify_transitions.py --write
python3 -B research/phase13/overnight/summarize.py --write
timeout 35s python3 -B research/phase13/overnight/probe_basis_pattern.py --write
```

First check whether a later iteration has already certified this transition.
Compute a minimum at `t+1` only if missing. A changed witness alone does not
prove a strict height increase. Refresh the replay manifest, inventory and
probe source hashes, run smoke and check byte preservation. Keep the 8 MiB
height cap and 512 KiB transition cap; stop on a durable checkpoint if a
budget is exhausted. Do not generate a dense height profile.

The actual 87099 witness failed at index 87099; the actual 87096 witness
failed at index 87098; a different extrapolated candidate failed at 87097.
None determines the new 87100 witness's next failure. Constant two-prefix
widths and nondecreasing maximal plateau widths are both falsified by this
finite chain; do not infer another general width law from four intervals.

This cannot decide `B=c`, asymptotic gcd size or behavior on other intervals.
Level 9 remains optional and unattempted; the current raw-shadow producer
caps full-integer work at level 8. No hard blocker or evidence-cap exhaustion
has occurred. No `COMPLETE` marker is warranted.

The host driver's quota polling and deadline are unchanged. Driver logs are
outside this checkout; evidence and command logs are under `overnight/`.
