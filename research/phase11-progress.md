# Phase 11 research journal — issue #19

## Resume here

- Issue: <https://github.com/hipotures/collatz-lab/issues/19> (open for review).
- PR: <https://github.com/hipotures/collatz-lab/pull/20> (**open, unmerged**).
- Independent clone: `/home/user/DEV/collatz-lab-phase11`.
- Branch: `codex/phase11-noncontracting`; base `origin/main`
  `2efdd2b531d511a8c6204e1f43179761585ab066`.
- Latest pushed proof checkpoint: **`ce21fdf78b055e2c798dd38d341491724fbba7b3`**;
  observed CI **success**: [run 43619205907](https://github.com/hipotures/collatz-lab/actions/runs/43619205907).
  The final checkpoint changes documentation only; inspect `git log -1` for
  that head. All implementation files were validated at the proof checkpoint.
- Completed: exact 110/111 semantics, aperiodicity, all-prefix frequency error,
  impossibility of every fixed-length contraction partition at every shift;
  general repeated-prefix rational exclusion and all shifts/tails; exact
  subcritical iff classification, including effective witnesses and D=0;
  sharp weight-dependent returns; second exclusion for 1011/1111.
- Validation: final `lake clean` followed by the complete
  `bash research/phase11/validate.sh` passes. **564 audited declarations**
  (487 baseline + 70 new theorems + 7 definitions), standard foundations only;
  **94 Rust tests**, all formatting/Clippy and required Python checks pass.
  All 77 new declarations are independently matched to the audit inventory.
- No required mathematical proof obligation remains for the implemented issue
  deliverables. Optional next work: the general spectral partial-return
  criterion, normalized H specialization/transcendence, or the length-five
  target in the findings. They are proposals, not proved exclusions here.
- PR #20 has the final scope and remains open and unmerged. The issue is open
  for owner review; no required implementation remains. For reproduction run
  `bash research/phase11/validate.sh` and
  `lake env lean research/phase11/Signatures.lean`.
- Preserve the 101/010 control at 1/1 and the all-one control at -1/1.
  No edits to paper, Phase 9 reports, issue #15 or another checkout.
- Owner decision: review PR #20 and authorize any eventual merge explicitly.
  Do not merge or close the issue merely because this session ends.

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

## Checkpoint D — a second exclusion from partial repetitions

- Checkpoint C pushed as `e435412021a6701b3b7cfc306f859ec371d0c2bc`.
- `NonContractingPartialReturn.lean` compiles a second noncontracting target,
  `1->1011,0->1111`. Independent aperiodicity, generic spectral noncontraction,
  exact signed prefix counts and inherited partial returns imply universal
  rational exclusion through the sharp height bound and `8192>6561`.
- Every finite shift and eventual shifted tail is excluded, including either
  sign of odd denominator. The word starts 10, so the first application via
  the initial-double hypothesis does not directly cover it.
- Literal list/index agreement through 256 bits and actual positive, negative
  and unreduced 81-bit rational witnesses compile by ordinary reduction.
  The third independent verifier reproduces the count/return/height ledger.
- The findings record a prospective wider criterion and the precise length-six
  failure of the same ledger, without calling it a rationality counterexample.
- Full current audit count: 564 = 487 baseline + 70 new theorems + 7 new
  definitions. Every new public declaration is explicitly audited.
- Final clean rebuild and complete validation passed before the D push.

Final D local checks: clean Lean build and full validation script passed;
separately piped the 564-entry Lean audit into `check_axioms.py`, and checked
all 21 interfaces in `research/phase11/Signatures.lean`. No forbidden proof
escapes or diagnostics. Source-to-audit comparison retains all 487 original
entries in exact order and covers every one of the 77 new declarations.
Checkpoint C CI observed success: run 43618593015. Phase 9/paper diff is empty.

## Final pushed milestones and review status

| Checkpoint | Exact pushed SHA | Observed CI |
|---|---|---|
| A: 110/111 structural obstruction | `5d9a1053eb7461d5c26007a9a94068f04ff8e484` | full local matrix; PR created at B |
| B: repeated-prefix exclusion | `2af12dd7092570d6d0fd375caf125f6e9ff5e819` | [43605243707 success](https://github.com/hipotures/collatz-lab/actions/runs/43605243707) |
| C: exact spectral boundary / sharp returns | `e435412021a6701b3b7cfc306f859ec371d0c2bc` | [43618593015 success](https://github.com/hipotures/collatz-lab/actions/runs/43618593015) |
| D: second noncontracting exclusion | `ce21fdf78b055e2c798dd38d341491724fbba7b3` | [43619205907 success](https://github.com/hipotures/collatz-lab/actions/runs/43619205907) |

The final proof run was observed completed/success at 17:10 UTC on 2026-11-14.
PR #20 was independently inspected open, unmerged and mergeable, based on
`2efdd2b531d511a8c6204e1f43179761585ab066`. Mergeability is not merge approval.
The issue remains open. No merge, issue closure, publication or manuscript edit
was performed. Original parity/numerator semantics, Rust files and dependencies
are unchanged. The isolated clone is clean after the final documentation push.

### Exact final validation record

All commands below were actually executed successfully at D; the script uses
`set -euo pipefail` and reads the exact count from the current CI configuration.

| Command / check | Verified outcome |
|---|---|
| `lake clean`, then `lake build` | fresh build succeeds, 82 jobs |
| `lake env lean research/lean-audit/FamilyAudit.lean` piped to `python3 research/lean-audit/check_axioms.py --expected-count 564` | 564 exact entries; approved standard foundations only |
| `python3 research/lean-audit/check_axioms.py --self-test` | 2 valid / 8 adversarial parser cases pass |
| forbidden-proof scan and source/audit inventory | no matches; all 487 baseline entries preserved in order, all 77 additions audited |
| `cargo fmt --check` | passes |
| `cargo clippy --locked --all-targets --all-features -- -D warnings` | passes without warnings |
| `cargo test --locked --all-targets` | 94 pass, zero failures |
| `python3 research/phase8/verify_polynomial.py` | passes |
| `python3 research/mahler-uncovered/verify_uncovered.py --check` | passes |
| `python3 research/phase9/verify_independent.py` | passes |
| `python3 paper/check_tex.py` and generated Lean names | static check passes; all 32 names compile |
| `python3 research/phase10/verify_unequal.py --check` | passes |
| `python3 research/phase10/search_unequal.py --check` | passes |
| `python3 research/phase10/verify_spectral.py --check` | passes |
| `python3 research/phase10/verify_sparse_family.py --check` | passes |
| `python3 research/phase10/generate_catalogue.py --check` | passes |
| all three Phase 11 verifiers | pass: literal, signed semantics, controls, counts, return/height and spectral checks |
| `lake env lean research/phase11/Signatures.lean` | all 21 exact interfaces check |
| `git diff --check` | passes |

No unresolved validation failure remains. The primary pending owner decision is
review/integration of PR #20. Originality is unverified; the analytic Mahler and
wider partial-return proposals remain research tasks, not completion blockers.

**One-line resumption prompt:** Resume issue #19 on
`codex/phase11-noncontracting`: read this Resume here section and
`research/phase11-findings.md`; review PR #20 without merging, or pursue the
explicitly unfinished general partial-return / normalized H hypotheses while
preserving both rational controls and Phase 9 isolation.
