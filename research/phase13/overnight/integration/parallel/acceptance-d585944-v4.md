# Independent issue #33 v4 acceptance re-audit

**Verdict: technical acceptance PASS; no material blocker.** The blanket repository-freeze problem is resolved. Owner-merge readiness remains conditional on the parent confirming the new open unmerged PR and successful CI at its final head. This auditor did not open a PR, push, merge, close an issue, or edit the parent checkout.

Target: branch `codex/phase13-overnight-integration`, exact local commit `d5859449613ba559c00dc3614237bbdd448eb834`, independently fetched into `/tmp/collatz-lab-acceptance-audit-5186975-20261115` and checked out detached. Issue [#33](https://github.com/hipotures/collatz-lab/issues/33) reread through the GitHub connector. Earlier full acceptance report: `/tmp/collatz-lab-issue33-acceptance-audit-5186975.md`.

## Scope and unchanged evidence

- All four source pins plus prior acceptance head `518697503580f632d19bdab4b92c6f4d9e5caffe` remain ancestors. All 225 existing main files still match pinned main `0190d57f43164ce2ec6016b3d3314c94ff98e06b` byte-for-byte except the intended CI step. Of 107 original overnight files, only the same intended summary/audit/progress/README/driver files change. Core mathematical semantics, proofs, certificate data, original certification scripts, original logs, manuscript, and merged referee report remain unchanged.
- The original full validation ledger is byte-identical to 5186975: SHA-256 `6dfeea6d534f46dea1b11cb50f42039d30b4f994bf482a6296307d8d475850b4`, entry HEAD `d6466ed71f2036f39cb0506a4a659bfecc7a0791`. All four original command scripts and eight log/resource files are byte-identical. Recorded runs remain exit 0, 269.91 / 9.52 / 467.32 / 585.64 seconds; smoke RSS 102696 KiB; pinned referee RSS 6288872 KiB. No heavy run was repeated or relabeled.
- Final evidence rehashed again: heights 24 records, 8027076 bytes, `08bcbb623aee8fd0bf8d6e6bcf919feed9e0cf171e2dafcb5ce89afbfc6c74a3`; base transitions 11, 481400 bytes, `24ef2b65c32e804663b20833a7bb330e85a305674fd8f5ae725e7c4fb91a38a7`; segment 2 transitions 5, 219248 bytes, `786cf600dc93222ab38fa1ef70cac3cb810840b188f6396f70b981ee0892e23e`; raw shadows 9, 6288 bytes, `72088c34e8e8ac6666da741466fd8c244168350de12c124be38b086d849acad7`.

## V4 review findings

The v4 audit explicitly selects 217 frozen dependencies from the immutable historical validation manifest, records 215 protected source files, and hashes four current metadata tools separately. The guard pins the raw original ledger SHA and exact recorded entry HEAD, verifies log hashes and PASS/counts, independently derives wall/RSS/exit fields from the hashed resource output, and rejects unexpected extra transition segments. Original historical snapshots and journal continuity remain protected. The canonical summary accurately identifies the N=87124 final target and distinguishes historical arithmetic runs from later metadata-tool tests. It makes no independent timestamp-authentication claim.

The selector excludes unrelated Rust/CI/Markdown, new standalone files, and later metadata code from the historical arithmetic comparison. The complete historical input manifest remains unchanged in the ledger. Source identity/count/hash checks and current metadata-tool hash checks remain active. This meets the scoped stale-metadata requirement without making unrelated future development rewrite or rerun the archived experiment.

## Checks actually run

1. In the clean exact-head audit clone, `python3 -B research/phase13/overnight/test_provenance.py`: all nine tests pass; `python3 -B research/phase13/overnight/finalize_provenance.py --check`: PASS; `git diff --check`: PASS; final checkout clean.
2. Independent Git-byte comparisons confirm ancestry, existing-main/source preservation, all four unchanged command scripts, unchanged original ledger/eight outputs, counts and SHA-256 values above.
3. An independently created disposable full clone at d585944 modified existing Cargo.toml, src/main.rs, CI YAML and README, and added standalone files including a new Phase 13 experiment file. The actual finalizer `--check`, `--write`, and `--check` each pass. Generated audit and original ledger remain byte-identical to their pre-edit bytes.
4. In that fixture, a byte change to existing `research/phase13/height_reference.py` causes the actual finalizer to fail with the frozen-certification mismatch. After restoring it, all nine provenance tests also pass in the fixture with unrelated edits intact. The disposable fixture was removed; the exact-head audit checkout stays clean.

## Delivery and limits

No mathematical or evidence-continuity blocker remains. The correction changes metadata tooling and reporting; it does not claim the earlier arithmetic matrix executed the later tooling. Final CI must validate that tooling at the delivered PR head. PR creation/URL, final pushed SHA and CI status remain the parent agent's responsibility. No novelty, new theorem, asymptotic result, publication-readiness, k=9, or N=87124-next-failure claim is introduced. Owner retains merge authority.
