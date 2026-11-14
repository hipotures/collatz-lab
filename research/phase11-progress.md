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

## Checkpoint B — repeated-prefix exclusion

- Checkpoint A pushed as `5d9a1053eb7461d5c26007a9a94068f04ff8e484`.
  Reused the source repository's configured SSH identity in the isolated clone;
  push succeeds without revealing credentials. No external messages sent.
- `RepeatedPrefix.lean` now kernel-proves square-prefix divisibility by `4^m`,
  the nonzero period-closing form, its universal `C*3^m` height bound, and the
  general unbounded-square exclusion. No contraction assumption or real/2-adic
  comparison occurs. Equal-parent image transport proves the general initial-11
  morphism corollary.
- `NonContractingExclusion.lean` applies it to 110/111, with all finite shifts,
  all eventual shifted tails and either sign of odd denominator.
- The 254-small-block independent checker tests exact signed square congruences
  and heights. Lean and Python check positive, negative and unreduced 81-bit
  actual rational prefixes. Both rational controls remain intact.
- Current audit: 517 declarations. Gate B spectral boundary remains next.
- Primary-source reading: Monks–Yazinski Theorem 2.7 and its proof; López–Stoll
  Theorem 1 and its real/2-adic transfer; Molchanov theorem scan being checked.
  A recent rStation manuscript was located; its analytic proof is not an input
  to this elementary argument, and no novelty claim is made.

## Checkpoint C — spectral boundary and sharper returns

- Checkpoint B pushed as `2af12dd7092570d6d0fd375caf125f6e9ff5e819`.
- PR #20 is open and unmerged: <https://github.com/hipotures/collatz-lab/pull/20>.
  Observed CI success: <https://github.com/hipotures/collatz-lab/actions/runs/43605243707>.
- `SpectralThreshold.lean` compiles the exact iff classification for all
  prolongable binary uniform substitutions with D>0, including effective
  subcritical witnesses, arbitrary shifted supercritical obstructions, the
  impossible critical equality and the D=0 constant-one exceptional case.
- The general return precision is m+ell. The sharp weight-dependent offset
  and return bounds now compile, extending the research mechanism to partial
  repetitions. This uses actual numerator dynamics, with both controls intact.
- The two-step 110/111 prefix-height identity is kernel proved. A separate
  candidate Mahler relation for the actual seed has finite exact coefficient
  checks; analytic specialization/transcendence is not proved and not used.
- Independent spectral checks: 715 parameter triples, six explicit constructive
  witness levels, negative/zero eigenvalues, and nonprimitive/constant controls.
- Next: run the complete validation script, checkpoint C, then assess the
  strongest partial-return application within remaining session resources.

Checkpoint C full local validation passes: `bash research/phase11/validate.sh`
(build, 545-declaration exact audit, parser self-tests, empty proof-escape scan,
94 Rust tests, formatting/Clippy, every required Python checker, both new exact
verifiers, manuscript static check and all 32 Lean-name checks). The initial
validation-script invocation had an incorrect relative root; it was corrected
before the successful complete run. No mathematical check failed.
