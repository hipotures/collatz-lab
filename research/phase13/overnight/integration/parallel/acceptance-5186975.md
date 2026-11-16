# Independent issue #33 acceptance audit

Target: `codex/phase13-overnight-integration`, pushed commit `518697503580f632d19bdab4b92c6f4d9e5caffe` ([commit](https://github.com/hipotures/collatz-lab/commit/518697503580f632d19bdab4b92c6f4d9e5caffe)). Issue [#33](https://github.com/hipotures/collatz-lab/issues/33) read through the GitHub connector. Audit checkout: `/tmp/collatz-lab-acceptance-audit-5186975-20261115`, detached at that exact commit; clean after checks. No parent-checkout changes, pushes, PR creation, merges, or issue edits were performed.

## Priority and verdict

No material scientific, evidence-continuity, historical-attribution, or issue-scope discrepancy was found at the audited commit. The parent subsequently identified a maintainability issue in the guard's blanket whole-repository equality, which would block unrelated future edits. That metadata-only follow-up is pending separate bounded re-audit. Original arithmetic validation remains historical and must not be relabeled as a fresh run after a guard-code change.

Technical evidence is ready for review. **Owner merge is not yet recommended:** the parent is handling the new open unmerged PR, final delivery SHA, and actual head CI. No PR/CI result is inferred here.

## Acceptance checklist

- PASS: overnight `76bf6136c334c1db9e52e399fcc33fd4c20b9c24`, main `0190d57f43164ce2ec6016b3d3314c94ff98e06b`, implementation `65b087dc62e4950e1c504fe34865acaacb9188c9`, and reviewer `3daf62c2c4b06e158375df16d6ca757969fba47e` are ancestors of the integration head. HTTPS remote readback confirms the expected main/source/reviewer pins and pushed integration head. SSH readback failed with publickey authentication; HTTPS succeeded without modifying refs.
- PASS: all 225 existing main files are byte-identical except the intended five-line CI addition. All 107 original overnight files are byte-identical except the intended summary, audit, prepended progress entry, appended README instructions, and driver guard. Scientific data, core semantics, theorem/proof files, original certification scripts/logs, manuscript, and merged reviewer report are unchanged.
- PASS: 24 heights / 11+5 transitions / nine raw-shadow levels k=0..8, under unchanged caps; no added records or recomputation. Final transition is N=87122, first failure index 87123, target N=87124. Finite certificate claims and inherited written plateau arguments remain distinct from Lean verification, asymptotic statements, and unresolved research.
- PASS: source summary and v2 audit are exact historical copies. They equal both the frozen source files and actual older artifact commit `caaa37cf68e399b48dae0fa975a45f9cc2447d9f`; cached entry head `bcfc2a7d9f57b8001b3041453ada7dc6ff08ae10` is correctly distinguished. The older 23 height / 11+4 transition evidence is an exact prefix of the final files. Original journal bytes survive as a suffix, explicitly labeled historical.
- PASS: v3 audit and canonical summary bind final 24/16/9 source bytes and distinguish original 464.54-second smoke (102832 KiB) from current validation. Existing historical “validation in progress” text is retained only beneath the historical-journal label; current handoff states successful completion and actual remaining delivery work.
- PASS: the final ledger embeds exact observed commands, tools, input manifest, resource caps, logs, chronology, exit 0, and unchanged-input flags for all four completed commands. Independent resource parsing matches every stated wall time and RSS value. All log/resource file hashes match. Current code/evidence/CI fingerprint at this audited commit matches the recorded manifest.
- PASS: three earlier unsuccessful overall attempts remain distinct: initial matrix failed under 4 GiB; second matrix passed but metadata inputs drifted; third matrix/interfaces/smoke passed but metadata inputs drifted. None is represented as final complete validation.
- PASS: deterministic guard and six hostile/cache regressions pass locally; stale counts/source pins/summary/smoke/log hashes and changed evidence are rejected. The driver checks final provenance after successful smoke. Metadata checks run in CI without replaying the experiment.
- PENDING: parent-managed maintainability follow-up, new PR URL and final actual-head CI. Issue remains open; no merge or closure occurred in this audit.

## Frozen evidence, independently rehashed

| File | Records | Bytes | SHA-256 |
|---|---:|---:|---|
| heights.jsonl | 24 | 8027076 | `08bcbb623aee8fd0bf8d6e6bcf919feed9e0cf171e2dafcb5ce89afbfc6c74a3` |
| transitions.jsonl | 11 | 481400 | `24ef2b65c32e804663b20833a7bb330e85a305674fd8f5ae725e7c4fb91a38a7` |
| transitions-0002.jsonl | 5 | 219248 | `786cf600dc93222ab38fa1ef70cac3cb810840b188f6396f70b981ee0892e23e` |
| raw-shadows.jsonl | 9 | 6288 | `72088c34e8e8ac6666da741466fd8c244168350de12c124be38b086d849acad7` |

## Validation evidence inspected, not repeated

| Recorded command | Exit | Wall seconds | Peak RSS KiB | Address-space cap KiB / timeout seconds |
|---|---:|---:|---:|---:|
| combined-matrix | 0 | 269.91 | 292976 | 25165824 / 1200 |
| combined-interfaces | 0 | 9.52 | 292848 | 1048576 / 180 |
| overnight-smoke | 0 | 467.32 | 102696 | 1048576 / 750 |
| pinned-referee | 0 | 585.64 | 6288872 | 25165824 / 1200 |

The matrix scripts include all inherited Lean/Rust/Python/static-manuscript checks. Logs show successful Lean build, exact 653-name approved-foundation audit, 94 Rust tests, 60 signatures, and 85 trusted-source scans. Fresh pinned reproduction logs verify exact implementation/source pins, 1691 baseline minima, 24 overnight minima, 16 transitions, and raw shadows through k=8; arithmetic stage 193.739 seconds. Unchanged reproduce.sh explicitly byte-compares both committed reviewer JSON files. Its historical provenance FAIL is deliberately preserved, and the corrected current audit addresses it separately.

## Commands actually run by this auditor

`git clone --no-hardlinks`, detached checkout, `git status`, `git log`, `git show-ref`, `git merge-base --is-ancestor`, `git ls-tree`, `git show`, tree diffs, SHA-256/record/prefix/resource/log/manifest inspections; GitHub connector issue and branch reads; HTTPS `git ls-remote`; `python3 -B research/phase13/overnight/test_provenance.py` (six tests OK); `python3 -B research/phase13/overnight/finalize_provenance.py --check` (PASS); `bash -n` on driver and interface script; `git diff --check` (PASS). No heavy validation or optimizer was rerun. One initial detached-checkout command used `/tmp` instead of the newly cloned directory and failed without changes; rerun in the clone succeeded. An exploratory attempt to read nonexistent `research/phase10/validate.sh` failed; actual validation follows phase13 → phase12 → phase11, which were read successfully.

## Limits and remaining owner decisions

This is an integration/provenance acceptance audit, not a new mathematical proof, novelty review, publication review, or fresh execution of the heavy validation matrix. Exact B, asymptotic gcd cancellation, unsampled minima, the N=87124 witness's next failure, and k=9 remain unresolved/unattempted as labeled. Parent must finish the new PR and verify final CI; owner retains the merge decision.
