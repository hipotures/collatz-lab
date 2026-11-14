# Phase 11 research journal — issue #19

## Resume here

- Issue: <https://github.com/hipotures/collatz-lab/issues/19> (open).
- Independent clone: `/home/user/DEV/collatz-lab-phase11`.
- Branch: `codex/phase11-noncontracting`, based on fetched `origin/main`
  `2efdd2b531d511a8c6204e1f43179761585ab066` (2026-11-14).
- No Phase 11 milestone pushed yet. No PR yet. Never merge without approval.
- First obligation: prove the literal `110/111` recurrences, eventual
  aperiodicity and failure of contraction for every complete-image grouping.
- Next: read the required Phase 8–10 implementations, then build the isolated
  clone and implement `CollatzLab/NonContracting110111.lean`.
- Gate B: reuse `Morphism.balance_power`; derive exact spectral statements
  with explicit degeneracies. Gate C: rational exclusion is open; investigate
  cocycles, congruences and actual seed transport without identifying real
  and 2-adic limits.
- Preserve `101/010` at `p=q=1` and all existing semantic controls. No changes
  to `paper/`, Phase 9 reports, issue #15 or other checkouts.
- Baseline CI configuration: 487 audited declarations. No local validations
  run yet. Baseline run cited by issue: 43598836400 (not yet independently
  inspected this session).

## Initial repository checks

Read root `AGENTS.md`, complete issue #19 and issues #15/#16. Original
checkout is clean on `main`, with a separate manuscript worktree. Created a
separate plain clone; source checkout was not switched. SSH authentication in
the clone failed; HTTPS fetch succeeded. No history was changed.

## Evidence levels

Every result will be labelled kernel proof, elementary mathematical argument,
finite deterministic regression, literature-dependent deduction or open
conjecture. Aperiodicity alone never proves rational-seed exclusion.

## Checkpoint A — validated structural obstruction

- Kernel proofs: exact literal images/columns and both bits; eventual
  aperiodicity; strict expansion of every positive complete-image group;
  no uniformly contracting partition for any positive chunk length, at any
  shift; exact power counts; all-prefix discrepancy bound `2k` below `3^k`.
- Independent literal list evaluation through length 81 is kernel checked.
  Python compares levels 0..8 and all prefixes, checks unaligned windows,
  positive/negative/unreduced/sign-normalized 81-bit itineraries and controls.
- `lake build` succeeds (fresh baseline and incremental additions); 503 exact
  declarations audited, parser self-tests pass; forbidden-proof scan empty;
  all 32 manuscript Lean names check without manuscript edits.
- `cargo fmt --check`, Clippy with all features and `-D warnings`, and all
  94 Rust tests pass. All nine pre-existing Python commands from issue #19
  pass, including Phase 9 and static manuscript checks. New verifier passes.
- Gate C promising lead: initial 11 yields unbounded square prefixes. Working
  draft `RepeatedPrefix.lean` is deliberately excluded from this checkpoint
  until independently validated; it is not yet an exported exclusion result.
