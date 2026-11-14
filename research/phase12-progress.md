# Phase 12 research journal — issue #24

## Resume here

- Issue: <https://github.com/hipotures/collatz-lab/issues/24>, **open**.
- Isolated clone: `/home/user/DEV/collatz-lab-phase12`.
- Branch: `codex/phase12-novelty-frontier`; base
  `47f34bdff38d876c394dc7326e457f686d112c13` (live origin/main checked).
- First pushed gate checkpoint:
  [`a873a82afe36650c80e5b1b57122c6e34a432a9c`](https://github.com/hipotures/collatz-lab/commit/a873a82afe36650c80e5b1b57122c6e34a432a9c).
  The compiling proof/report checkpoint follows it; the next journal-only
  handoff will record that exact pushed SHA. Use `git log -1` in the meantime.
- Minimum issue outputs complete locally: primary coverage matrix; rigorous
  findings; independent exact checker/evidence; three Lean modules; explicit
  audit/CI updates; signatures and complete reproducible validation script.
- **Scientific result:** the candidate is already excluded by earlier
  density-sensitive criteria. The two-return determinant congruence is
  automatic for arbitrary binary words with those finite matches. Its proposed
  nonzero/small premise is impossible. **No novel exclusion found.**
- **K:** aperiodicity, counts, all-prefix discrepancy, no shifted fixed-length
  contraction, global return cap/no initial squares; general finite rational
  compatibility, elimination congruence and small-determinant no-go.
- **H, not K:** known-method rational exclusion of the candidate, uniform real
  frequency, exact return recurrence and asymptotic failure of the weight-only
  ledger. **F:** bounded exact languages/return pairs and actual signed seeds.
- Clean rebuild and `bash research/phase12/validate.sh`: **exit 0**. Current
  exact audit count **593 = 564 + 29**, approved standard foundations only;
  all 94 Rust tests and inherited Python/static manuscript checks pass.
- Next task: push the validated proof checkpoint, open the requested PR against
  main, inspect its exact-head CI, then record a final durable handoff. Do not
  merge or close the issue. Human review of the mathematics/attribution is next;
  no unproved Lean obligation is hidden by the completed minimum output.
- Optional research obligation remains explicitly open: determine the optimal
  finite rational-reconstruction height exponent H_N (findings §5), after
  comparing the specified primary approximation sources. Not needed to finish
  the issue's minimum reliable level. Stretch novelty goal was not achieved.

## Initial state and research plan

The original checkout was clean on main at the base above. A fresh HTTPS
clone was created and the exact issue branch selected. Live remote refs
confirmed the base. Read-only inspection of the other existing checkouts did
not modify them. Gate 0 is bounded to one source-triage pass: inspect the
specified accessible originals and directly relevant leads, record proof
access limits, then choose a precise provable structural/no-go target.

The three planned deliverables are distinct: checked prior-art coverage;
faithful structural arithmetic for the literal candidate; and an independently
falsified two-return proposal. A known-method reduction is a useful negative
novelty result, not a reason to rename it a new exclusion.


## Gate 0 completed: a negative novelty decision

Read the full issue and empty comments, AGENTS.md, Phase 9 prior-art report,
Phase 10 unequal-weight report, corrected Phase 11 findings, referee §§1–3,
6–7, all six required Lean modules, exact rational semantics and CI/audit.
Baseline [CI 43633860186](https://github.com/hipotures/collatz-lab/actions/runs/43633860186)
was independently observed completed/success at base 47f34bd.

The original primary-source pass read Allikvere's deposited TeX, Cassidy and
Pham at pinned commits, Dubickas's publisher proof, De Jesús's v3 §§9–10,
Monks–Yazinski's density proof and Bernstein–Lagarias's isometry/finite-lift
proof. rStation v3's scope and critical coherence interfaces were inspected;
its long analytic lifting proof is not independently certified here. The
Molchanov full-proof access limitation is explicit in the matrix. No equal-
weight Mahler specialization is assumed for an unequal-weight seed.

The decisive catch was Allikvere's **density-sensitive** §5, not its crude
single-block corollary. A global `P(6^k)<=4*6^k` and frequency 5/7 meet it.
A second exact shadow-height reconstruction gives the same known exclusion.
A directly applicable later primary was then found: De Jesús's 30 September
2026 drift-sensitive note, Zenodo 23071770, Theorem 9/Corollary 15. Its exact
statement and relevant elementary proofs were obtained and checked. Two
additional earlier determinant/lattice sources were inspected and included
so that the seed-free no-go is not overstated as excluding all multi-return
height arguments. Source URLs and fresh SHA-256 hashes are committed in
`phase12/sources.json`; third-party full texts remain outside the repository.
The timeboxed source-triage pass ended with **covered**, not a new criterion.

## Proof and adversarial checkpoints

- `TwoReturn.lean` proves the requested sign-correct congruence, then constructs
  rational witnesses for every finite truncation using the existing inverse
  branches. This removes infinite rationality entirely from the determinant
  conclusion and proves the rigorous small-iff-zero no-go.
- `FrontierSix.lean` derives literal columns and handles every nonzero eventual
  period residue, with period-multiple descent. Its signed integer prefix
  discrepancy is effective at all lengths. The full Phase 11 iff is reused
  for contraction. A separate global match bound proves no initial squares.
- `FrontierSixChecks.lean` compares independent literal substitution and checks
  actual positive/negative/unreduced 81-bit numerator trajectories by kernel
  reduction. The Python code does not import any existing verifier.
- Finite evidence: 1,023 binary words; 574,327 pairs, 46,390 overlapping;
  85,484 failures of an unjustified extra precision bit; 1,016 signed finite
  witnesses; 7,168 form checks. Both required rational controls preserved.
  The 60,000-symbol observations 724/2,676 are reproduced and separately
  upgraded to exact finite global-language counts by closure/occurrence.
- Two fundamentally different routes were tested: determinant elimination
  (proved automatic), and return/language structure (global weak-ledger no-go,
  but stronger known height/counting methods apply). No converse of a
  sufficient exclusion theorem was assumed.

### Failures and corrected approaches

The initial HTTPS push lacked a credential helper; the first SSH attempt
lacked the repository-specific key setting. Configuring this isolated clone
with the **existing original checkout's** `core.sshCommand` enabled a normal
non-force push. No credentials were printed or new identity/contact metadata
chosen. The first gate commit remains unchanged in history.

Initial Lean elaboration caught (1) unfolding `cycleCoeff` before a newly
unfolded determinant had exposed it, (2) a finite-tail shift simplification,
and (3) an eta-expanded prefix-weight expression needing an explicit `change`
before integer arithmetic. These were corrected, with no altered mathematical
hypotheses. Both standalone modules then compiled, followed by a clean complete
build. No mathematical proof gap or unresolved validation failure remains.

### Actual validation at the proof checkpoint

`lake clean` was executed, then `bash research/phase12/validate.sh` exited 0.
It executes `bash research/phase11/validate.sh` and the added checks. All rows
below were actually executed successfully; script failure propagation uses
`set -euo pipefail`.

| Executed command/check | Observed result |
|---|---|
| `lake build` after `lake clean` | Full fresh build succeeds |
| `lake env lean research/lean-audit/FamilyAudit.lean` piped through `python3 research/lean-audit/check_axioms.py --expected-count 593` | 593 exact entries; standard allowlist only; also saved in a separate pipefail audit |
| `python3 research/lean-audit/check_axioms.py --self-test` | 2 valid / 8 adversarial cases pass |
| Forbidden proof-escape scan, source inventory and base-manifest comparison | Empty forbidden scan; all 29 new declarations audited; all 564 baseline names preserved in order |
| `cargo fmt --check` | Pass |
| `cargo clippy --locked --all-targets --all-features -- -D warnings` | Pass |
| `cargo test --locked --all-targets` | 94 pass, zero failures |
| `python3 research/phase8/verify_polynomial.py` | Pass |
| `python3 research/mahler-uncovered/verify_uncovered.py --check` | Pass |
| `python3 research/phase9/verify_independent.py` | Pass |
| `python3 paper/check_tex.py` and generated Lean-name compilation | Static check and all 32 names pass; no manuscript change/PDF-readiness claim |
| `python3 research/phase10/verify_unequal.py --check` | Pass |
| `python3 research/phase10/search_unequal.py --check` | Pass |
| `python3 research/phase10/verify_spectral.py --check` | Pass |
| `python3 research/phase10/verify_sparse_family.py --check` | Pass |
| `python3 research/phase10/generate_catalogue.py --check` | Pass |
| `python3 research/phase11/verify_noncontracting.py` | Pass |
| `python3 research/phase11/verify_spectral_boundary.py` | Pass |
| `python3 research/phase11/verify_partial_return.py` | Pass |
| `lake env lean research/phase11/Signatures.lean` | All existing exact interfaces pass |
| `lake env lean research/phase12/Signatures.lean` | All six new exact interface checks pass |
| `python3 research/phase12/verify_returns.py --check` | Complete deterministic evidence matches; all assertions pass |
| `git diff --check`, Markdown fence/table-boundary check | Pass |

External raw logs: `/home/user/DEV/collatz-lab-phase12-evidence/validate.log`
SHA-256 `1a76901bd992c3d9e6ee7f367dbd91789e5883bce117555aee620e826baedb6c`.
The scripts, exact finite record, source hashes, complete proof arguments and
command matrix are committed, so these external logs are supplementary.

No `paper/`, Phase 9 reports, Phase 11 referee report, existing proof body,
authorship data, issue #15, main branch or other agent checkout was modified.
No new agents, external messages, publication, merge or issue closure occurred.
