# Phase 13 overnight experiment plan — issue #30

This branch is intentionally based on the unmerged PR #29 at
`65b087dc62e4950e1c504fe34865acaacb9188c9`.
It is **not** the canonical Phase 13 branch, main, a new theorem, or a
publication branch. Read the active GitHub issue #30 and the Phase 13 theory.

## Non-negotiable boundaries

- All edits are confined to `research/phase13/overnight/`,
  `research/phase13/overnight-progress.md`, and
  `research/phase13/overnight-summary.md`.
- Never modify PR #29, main, Phase 9, reviewer reports, existing Phase 13
  engines or historical evidence.
- No force pushes, merges, publication, external agent spawning, secrets,
  host reconfiguration or unnecessary internet access.
- No unbounded computation. The host driver enforces an eight-hour deadline,
  but each expensive operation must also have its own timeout and checkpoint.
- Finite exact data do not determine `liminf log2(H_N)/N` or asymptotic
  gcd growth. Clearly distinguish finite certificates, mathematical proofs,
  conjectures, and known literature.

## Priority 1: certified larger-height samples

- Use the fixed word `1->100111, 0->111110`.
- Its exact shadow boundaries are `L_k=(56*6^k-1)/5`, for example
  `L_5=87091`, `L_6=522547`, `L_7=3135283`.
- The committed `height_lattice.py` and
  `verify_certificates.py` cap N at 16,384. Build **independent,
  separate extended experiments** here rather than weakening baseline
  guarantees in those modules.
- Begin with `L_5-1,L_5,L_5+1` and a sparse set of points before and
  after the boundary. Continue to `L_6` only if resource budgets allow.
  The exact shadow minima at L_k are already proved; the especially useful
  unknowns concern intermediate minima and basis transitions.
- A reported exact minimum needs a primitive positive odd denominator,
  an actual finite-parity witness, and an independently reproducible
  **no-smaller-height** certificate, not merely the optimizer's output.
- Build small tests against the 1,691 committed certificates and known
  `H_11=3, H_12=513` before exploring bigger N.
- Write compact records atomically in an append-only format. Avoid dense
  O(100k) certificate generation or giant uncontrolled output files.

## Priority 2: exact raw-shadow cancellations

- Derive raw `P_k,Q_k` using *noncommutative* affine/matrix substitution
  recurrences from `research/phase13/verify_modular.py` and theory §8.
- Reconstruct the exact known levels k=0..7. Independently compare gcd,
  sign, and SHA-256 hashes with `phase13/modular.json`.
- Extend to k=8, then optionally k=9 or k=10 under explicit
  timeout/memory caps. Store the gcd and **bit lengths**, not full huge raw
  integer strings. Store exact deterministic hashes for replay.
- Investigate divisibility using modular affine cycles and give fully
  specified finite certificates where appropriate. Never infer growth
  of gcd from a handful of examples.

## Priority 3: falsification and interpretation

- Inspect reduced best approximation transitions between consecutive
  L_k; report evidence of better intermediate approximants.
- Test and try to disprove simplistic claims `B=c`, constant gcd,
  monotone normalized height, no intermediate minima, or predictable
  fixed-length plateaux. Maintain known counterexamples instead of
  rediscovering them.
- If limits or irrationality exponents are discussed, classify
  statements according to the Phase 13 prior-art matrix; do not relabel
  an old result as novel.

## Output contract

1. `research/phase13/overnight-progress.md` — first section
   **Resume here**, clear exact next computation, results, verification,
   failed attempts, current checkpoint.
2. `research/phase13/overnight-summary.md` — owner-readable morning
   summary, bounded scientific outcome and open questions.
3. A small `research/phase13/overnight/` reference implementation,
   optimized calculation where justified, independent verification,
   and bounded JSON/JSONL evidence.
4. Modify `research/phase13/overnight/smoke.sh` to call the new
   independent verification checks when they exist.
5. Write `research/phase13/overnight/COMPLETE` **only** on a documented
   hard stop or after no further useful bounded research tasks remain.

The host driver owns git commit/push after validation. Do not commit or
push from Codex itself. Follow `AGENTS.md` and issue #30.
