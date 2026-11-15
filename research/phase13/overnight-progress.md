# Phase 13 overnight research journal — issue #30

## Resume here

- Branch: `codex/phase13-overnight`. Local HEAD and cached origin ref at
  inspection: `fbe7b6cd120ee2c93ecce30b50712978652965f8`. PR #29 source:
  `65b087dc62e4950e1c504fe34865acaacb9188c9`. No Git mutation, fetch, push,
  network access, issue edit, PR edit, or integration was performed this turn.
  The host driver owns validation and any subsequent commit/push.
- Found three untracked partial modules at entry: `extended_height.py`,
  `verify_results.py`, and `test_extended.py` under `overnight/`. Read and
  continued them; there was no overnight JSONL evidence to repeat.
- Full extended regression **passed**: 511 brute-force residues, all 1,691
  historical minima and certificates, four independent prefix/residue
  controls through 16,384 bits, seven rejected corruptions, `H_11=3` and
  `H_12=513`. Evidence: `overnight/regression-checked.log`.
- Five exact samples are complete. In ascending `N=80000,87090,87091,87092,
  90000`, the height bit lengths are `35217,35217,35217,51875,51875`.
  Each has a primitive positive odd-denominator witness, actual parity check,
  and independently verified zero box count at `H-1`. No sample in this list
  needs recomputation. Evidence: `overnight/heights.jsonl` and the derived
  `overnight/height-inventory.json`; timing logs `l5-triplet.log`, `l5-sparse.log`.
- The first three primitive witnesses are identical and match the inherited
  k=5 shadow coordinate hashes. Thus height monotonicity gives a constant
  minimum throughout `80000..87091` (a finite deduction, not a dense scan).
  The ratio `H_87092/H_87091` lies in `[2^16657,2^16658)`. At `90000` both
  the witness and exact height differ from `87092`, although their height bit
  lengths agree; `1 < H_90000/H_87092 < 2`. Bit lengths alone are not plateaux.
- **Next task:** implement a compact independent basis/box certificate using
  the fully specified written argument in `overnight/README.md`, and test
  nonempty as well as empty boxes, denominator parity, and signed/zero
  coordinates. All five stored bases have coefficient bound 1 at `H-1`.
  This is a promising exact shortcut, not yet an accepted certificate type.
  Preserve the existing floor-sum evidence and its independent checks.
- Then attempt `N=522546,522547,522548` under explicit per-sample caps and
  the existing 8 MiB evidence limit. `L_6` is not attempted this turn: the
  measured floor-sum cost already dominates at `L_5`, so the sixfold increase
  in prefix length calls for a cheaper certificate within the cap. Next run
  commands and required validation are specified below.
- After those heights: raw-shadow gcd at k=8, exact noncommutative recurrence,
  comparison with the inherited k=0..7 signs/gcds/hashes, and independent
  replay; then basis-transition falsification. None is marked complete here.
  No hard blocker was reached; further bounded work is useful, so there is
  no `COMPLETE` marker. **Final overnight smoke passed, exit 0**, including
  standalone independent verification of all five records and the inventory.
  Output: `overnight/smoke.log`; final scope/preservation audit:
  `overnight/checkpoint-audit.json`.

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
  lattice determinant, and zero box count at `H-1`. The checker imports no
  optimizer or other project code. Full integers and Euclidean quotients
  use canonical hexadecimal strings in the bounded JSONL file.
- **Written proof:** the floor-sum counting/telescoping argument is the
  existing theory Section 4. The all-level shadow minimum in Section 8 is
  inherited, not a theorem discovered by an overnight sample. No new Lean
  proposition or formal proof was added. The optional coefficient-bound and
  integer-interval argument in `overnight/README.md` is written elementary
  mathematics only; its proposed verifier still needs implementation/tests.
- **Open:** exact `B`, subexponential raw-gcd cancellation, and competing
  intermediate approximants. Finite data do not prove asymptotic behavior.

## Actual validation and resource observations

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
- Smoke now prevents imported baseline modules from writing bytecode and
  runs a quick extended regression (first/final record of every historical
  family, all 511 small residues, parity controls and corruptions), plus the
  independent checker on every overnight record. The executed invocation was
  `timeout 450s /usr/bin/time -v bash research/phase13/overnight/smoke.sh`,
  under a 1 GiB child address-space cap, with output in `overnight/smoke.log`.
  It passed, exit 0: wall time 223.81s, peak resident memory 94,592 KiB.
  Actual output confirms 25,432 signed floor sums, 4,095 exhaustive residues,
  31,750 signed parity cylinders, 262,400 direct `H_12` exclusions, seven
  corrupt baseline certificates rejected; then 511 extended brute-force
  residues, 20 historical first/final records, four independent prefix/residue
  controls, seven extended corruptions rejected; finally all five overnight
  witness/parity/minimality checks and the exact inventory check. Shell syntax,
  overnight Python compilation and `git diff --check` also passed. No Lean,
  Rust or remote CI check was run or claimed this turn.
- Final checkpoint audit confirms the original triplet bytes were preserved,
  the five expected sample IDs are unique, the final source hash matches the
  inventory, all changed paths are authorized, HEAD is unchanged, and no
  `COMPLETE` marker exists. The final whitespace check passes. No calculation
  remains running; the durable files, not a background process, are the handoff.

## Concrete continuation

Read the current files and `git status --short --branch` / `git log -1`
before working. Implement the proposed compact certificate as a separate
explicit certificate type in the overnight producer and independent checker.
Never infer minimality from the optimizer's basis alone. Exhaustively test the
integer coefficient/interval exclusions against direct small box enumeration;
cross-check accepted minima against all 1,691 historical certificates and the
five existing overnight certificates. Reject nonempty boxes and malformed
bases/intervals. A finite enumeration cap must reject or fall back when the
bound is too large; do not silently omit coefficients.

After implementation and those checks, the concrete next sample command is:

```bash
python3 -B research/phase13/overnight/extended_height.py --samples 522546 522547 522548 --seconds-per-sample 180 --write
```

Use an outer timeout and child memory cap as above. Read the JSONL before
running; the producer must skip any sample a later iteration already certified.
If candidate/residue/parity checking alone exceeds the budget, checkpoint the
candidate separately and label it uncertified until its independent check
finishes. Do not raise the original Phase 13 engines' 16,384-bit cap. Refresh
the derived inventory after successful appends, then run overnight smoke.
Allow more than the observed 145.68s (for example, a 240s outer cap) when
repeating the full extended regression; the smoke regression is intentionally
the quicker subset. Host-driver commit/push remains outside Codex.

The host driver's ten-minute quota polling and eight-hour deadline are
unchanged. Driver logs remain outside this checkout; the research commands'
small logs and deterministic evidence are under `overnight/`.
