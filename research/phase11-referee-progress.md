# Phase 11 independent referee journal — issue #21

## Resume here

- Review branch: `review/phase11-independent-audit`, based on `main`
  `2efdd2b531d511a8c6204e1f43179761585ab066`.
- Review clone: `/home/user/DEV/collatz-lab-phase11-review`.
- Exact audited PR #20 head: `d270b4466794badc49da6feebefeda77f5793e16`,
  branch `codex/phase11-noncontracting`, open and unmerged when inspected.
- Detached validation clone: `/home/user/DEV/collatz-lab-phase11-audit`.
- External evidence directory: `/home/user/DEV/collatz-lab-phase11-evidence`.
- Last pushed full-report checkpoint:
  [`8a56e3357a600ac62e5082d8da3a04418f2549d0`](https://github.com/hipotures/collatz-lab/commit/8a56e3357a600ac62e5082d8da3a04418f2549d0).
  This final journal-only handoff follows it; use the review PR head or
  `git log -1` for that later commit, which cannot contain its own hash.
- Separate review [PR #22](https://github.com/hipotures/collatz-lab/pull/22)
  is open and unmerged against `main`, with only the two requested reports.
- Completed input reading: complete issues #21/#19, PR #20 metadata and empty
  discussion threads; root AGENTS.md; the six Phase 11 modules; all three
  Phase 11 Python verifiers, signatures and validation script; the specified
  Phase 9/10 context reports and paper README; rational, substitution, signed
  normalization, inverse branch, balance, contraction and exponential-gap
  source interfaces and proofs. `RationalSeed.lean` does not exist: the actual
  definitions are in `CollatzLab/Word.lean`.
- Completed: standalone square/partial-return and spectral proofs, a different
  valuation-based aperiodicity proof for both examples, signs/tails/domain
  audit, full fresh validation (exit 0), separate 564-entry axiom audit (exit 0),
  all 21 signatures (exit 0), and independent exact computation (exit 0).
- Independent computation: 2047 offset words, 36,800 signed return witnesses,
  680 literal substitutions. No counterexample found to a formal statement.
- Decisive priority finding: obtained Allikvere's full July 2026 preprint
  (Zenodo 21543841), including exact sharp bound, partial-repetition inequality
  and universal square criterion. Their elementary proofs check; these are
  prior results, not merely a vague methodological parallel. Cassidy's pinned
  September note supplies an earlier general repetition framework as well.
- Documentation defect: findings line 105 incorrectly says deleting either
  safeguard makes the theorem false. Without repetition the remaining claim
  is the open Periodicity Conjecture, not falsified by the periodic controls.
- Completed report: all 77 exact signatures, audit matrix, 18 primary-source
  rows, two reproducible scripts/outputs and the broader counting deduction.
  Verdict: mathematical PASS; merge CONDITIONAL on documentation/attribution;
  separate new-theorem publication FAIL on present evidence.
- Review work complete: no unproved obligation is concealed. Source access
  limits and unchecked stronger literature claims remain explicitly bounded
  in report §6.3; they are not needed for its mathematical verdict.
- Next owner task: arrange the P1/M1 documentation corrections on the
  implementation branch and decide whether to authorize its integration.
  Human review and a contribution-based editorial decision are needed before
  commissioning any formalization note. Do not modify or merge PR #20 as
  part of this review handoff.
- No source proof, manuscript, author metadata, issue #15, original checkout,
  or Codex branch has been changed. No PR has been merged and no issue closed.

## Final handoff — 14 November 2026

The complete report was committed and pushed as
`8a56e3357a600ac62e5082d8da3a04418f2549d0`; PR #22 was opened with that
checkpoint. Its journal-only follow-up records this durable handoff. Final
`git diff --check` and the document structure/Python syntax checks passed.
The report embeds both independently executed checkers and their outputs;
the external evidence directory is supplementary, not required to recover
the independent finite checks.

Immediately after opening PR #22, its separate main-baseline CI
[run 43627704656](https://github.com/hipotures/collatz-lab/actions/runs/43627704656)
was **in progress**, not recorded as passed. This does not replace the
completed local 564-declaration validation at PR #20's exact head. A later
journal-only push may trigger another run; inspect the actual review head
when using GitHub evidence.

Final live reads reconfirmed PR #20 open/unmerged at the pinned SHA, issue
#19 open, and issue #15 open with its update timestamp unchanged. Remote
`main` and the Codex branch retained their initial SHAs. Both original main
and detached audit checkouts remained clean. No approval to merge either PR
or to publish/submit a manuscript was inferred from the mathematical PASS.

## Review protocol and evidence levels

This is an independent AI-assisted mathematical review, not human peer review.
Independent means that the elementary arguments are reconstructed and tested
against the exact propositions; it does not mean independence of Lean's kernel
or the runtime. Classify separately: hand proof, kernel theorem, finite check,
external theorem with checked applicability, unchecked claim, unresolved item.

All changes belong to issue #21. Review outputs target the two requested
English reports. Findings about PR #20 are recorded here, without modifying its
implementation. Merge readiness and publication readiness are separate gates.

## Repository baseline

The original shared checkout was clean on `main` at `2efdd2b531d511a8c6204e1f43179761585ab066`.
Remote main and PR head were confirmed with `git ls-remote`. Two fresh HTTPS
clones were created; the first SSH clone attempt failed authentication. Only
the isolated review clone has a new branch. PR #20 changes 16 files, 2202
insertions and one deletion; none is in `paper/` or the Phase 9 reports.
CI at the reviewed head specifies exactly 564 audit records and the three
standard foundation axioms as its only allowlist. Local validation starts with
no `.lake` build cache. Existing green CI is treated as an input, not a proof
of mathematical interpretation or priority.

## Source investigation started

Primary search on 2026-11-14 found Halbeisen–Hungerbühler's rational-cycle
paper, Monks–Yazinski's original author PDF, and rStation's pinned v2 **and
newer v3 (27 October 2026)**. The latter is an AI-authored platform manuscript,
not evidence of journal publication. SSRN refused the newly found Dejesus
record `7662483`; full-text availability remains to be investigated. These
discoveries are leads, not yet a priority conclusion.

## Checkpoint B — validated mathematical reconstruction and decisive prior art

- `bash research/phase11/validate.sh` passed on the pinned PR head from a fresh
  build: 82 jobs; 94 Rust tests; all formatting, Clippy and Python checkers;
  static manuscript check and 32 generated Lean names. No PDF work performed.
- Separate audit pipeline passed with the exact CI count 564; parser self-test
  passed. Baseline 487 entries are preserved, all 77 additions are covered;
  only `propext`, `Classical.choice`, `Quot.sound` appear. Forbidden scan empty.
- Signature attempt during initial build failed for missing root olean; the
  command was rerun after build and all 21 interfaces passed. No proof failed.
- Independent checker uses `fractions.Fraction`, parity lifting, explicit
  closed-form offsets and literal substitutions, importing no repository code.
  Its source/output are in the evidence directory and will be embedded in the
  report for durable reproducibility.
- Allikvere primary files were accessible through Zenodo's public records API
  even though its HTML/DOI routes failed in the web tool. Record creation and
  update timestamps: 2026-07-25 and 2026-08-13. Read Lemma 2.1, Theorem 2.3,
  Corollary 3.2 and proofs, plus the stronger Section 5 statement/argument.
- Retrieved De Jesús irrationality v3 through Zenodo 23108370 (record created
  2026-10-02, updated 2026-11-08); the SSRN page alone had refused access.
  Retrieved both rStation paper 16 v2 and v3. Their broader analytic claims
  are not assumed as proved here. Read the original Cassidy note at pinned
  commit `6b805eed1613edaedd87965e2b1986390fa84f0e` after correcting a name
  spelling in the PDF reference (`eliottcassidy2000`, one l in Eliott).

## Checkpoint C — complete review, broader known-method exclusion

The final report contains all four standalone reconstructions, exact
signatures for all 77 added declarations, the semantic audit matrix, hostile
edge cases, 18 primary-source rows, explicit publication/integration decisions,
and both independent scripts with their actual outputs.

An additional independently reconstructed deduction (§2.4) applies the
published Dubickas collision argument to fixed odd-denominator signed
numerators. It bounds their lower factor-complexity ratio by
`log(2)/log(3/2)`. For images `0->1^L`, `1->1^c 0 1^(L-c-1)`, L≥2 and
1≤c<L, iterated images have one variable position. This gives
`P(L^k)≤(L+1)L^(k-1)` and excludes the entire family, including both Phase 11
examples and the length-six target whose partial-return ledger fails.
The argument is mathematical deduction, not a new Lean export or a priority
claim. De Jesús v3 §9 already states the general signed-rational liminf
criterion. Pham's pinned July note was also read: its Corollary 4 literally
uses limsup, so these statements have not been conflated.

The exact factor-language closure check gave 4*3^(k-1) factors at lengths
3^k, and 5*4^(k-1) at lengths 4^k, for k=1..6. Both scripts embedded in the
report were extracted and rerun, exit 0, independently of their external
copies. The factor proof is supplied on paper, not inferred from these counts.

The documentation correction also applies to “Both conditions are essential”
at findings line 53. The stale research paragraph is at lines 42–47. No
modification of the Codex branch was made to fix either statement.

### Commands actually executed against PR #20

All commands in this table passed after the explicitly recorded initial
signature sequencing failure. The validation script uses `set -euo pipefail`.
Its output is in `validate.log`; the separate audit/signature outputs are in
`axioms.log` / `signatures.log`.

| Command/check | Actual result |
|---|---|
| `bash research/phase11/validate.sh` | Exit 0, complete matrix below on exact d270b446 head; no prior `.lake` cache |
| `lake build` | 82-job fresh build completed successfully |
| `lake env lean research/lean-audit/FamilyAudit.lean` piped through `python3 research/lean-audit/check_axioms.py --expected-count 564`, with pipefail | 564 exact records, approved foundations only; also run separately |
| `python3 research/lean-audit/check_axioms.py --self-test` | 2 valid and 8 adversarial cases pass |
| `rg` forbidden-proof scan in `CollatzLab/` and `CollatzLab.lean` | No matches; exit 1 is the expected empty-scan result |
| Source-to-audit inventory | All 487 baseline names retained in order, all 70 theorems and 7 definitions added explicitly |
| `lake env lean research/phase11/Signatures.lean` | 21 exact interfaces pass after build completed |
| `lake env lean --version` | Lean 4.18.0, x86_64-unknown-linux-gnu, commit 11ccbced7964, Release |
| `cargo fmt --check` | Pass |
| `cargo clippy --locked --all-targets --all-features -- -D warnings` | Pass, no warnings |
| `cargo test --locked --all-targets` | 94 tests pass, zero fail |
| `python3 research/phase8/verify_polynomial.py` | Pass, 686 convolution identities and listed exact ledgers |
| `python3 research/mahler-uncovered/verify_uncovered.py --check` | Pass: 48 Padé rows, 8 checkpoints, 32800 signed candidates, 144 controls |
| `python3 research/phase9/verify_independent.py` | All independent checks pass |
| `python3 paper/check_tex.py` | Pass: 49 labels, 46 distinct references, 21 bibliography entries, 32 Lean names |
| Generated manuscript Lean-name file, checked by `lake env lean` | All names pass; no manuscript edit or PDF-readiness claim |
| `python3 research/phase10/verify_unequal.py --check` | Pass |
| `python3 research/phase10/search_unequal.py --check` | Pass, existing bounded catalogue reproduced |
| `python3 research/phase10/verify_spectral.py --check` | Pass |
| `python3 research/phase10/verify_sparse_family.py --check` | Pass |
| `python3 research/phase10/generate_catalogue.py --check` | Pass |
| `python3 research/phase11/verify_noncontracting.py` | Pass, 254 small square blocks and the signed/literal checks |
| `python3 research/phase11/verify_spectral_boundary.py` | Pass, 715 parameter cases and effective witness fixtures |
| `python3 research/phase11/verify_partial_return.py` | Pass, exact 8192>6561 ledger and signed witnesses |
| `git diff --check` | Pass |

These commands belong in the **detached PR-head clone**. The review branch
intentionally contains only two reports atop main; it does not import or
repackage the Phase 11 proof files. Its own CI will therefore audit the main
baseline, not replace the separately executed 564-declaration PR-head audit.

### Independent checks and review-document verification

- `python3 .../adversarial.py`: exit 0, 2047 offsets, 36,800 signed returns,
  680 literal substitutions, both controls and signed finite examples.
- `python3 .../factor_check.py`: exit 0, exact closed languages at six levels
  per target, all factor caps and numerical base gaps pass.
- Report Appendix B extraction and both embedded script executions: exit 0.
- Markdown structure check: 77 signature headers, two anchored script markers,
  balanced fences and table columns, no unfinished sections. Initial checks
  caught a marker counted inside the extractor and unescaped absolute-value
  bars in one table cell; both formatting checks were corrected.
  A final harness initially looked for nonexistent `# BEGIN` delimiters;
  rerunning it against the actual HTML script markers passed, including
  Python syntax compilation of both extracted scripts.
- Original main checkout and detached audit checkout remain clean. Review diff
  has only the two requested Markdown files. No proof/manuscript changes.

### Source versions and local SHA-256 evidence

The raw texts/logs remain in `/home/user/DEV/collatz-lab-phase11-evidence`.
Their essential mathematical findings, exact signature inventory, independent
scripts/outputs and reproducible commands are committed in the reports. Raw
third-party PDFs are not redistributed in the repository.

```text
226cb4898202160dcf58178dc0a79234352b372d6857f2a963622be64997cbc7  validate.log
6a7805933078487bbb068bfa1b039227b76962c69d853278fdaaf7a9f06f5795  axioms.log
9d19eaf7a3dbb535dd5f1c69dbd051dab9bad0de53c69a572978c1d891d84b90  signatures.log
bcf6661c98916d765c634057ff8f455506b80e14f07e8094aa04097fca45b3b8  adversarial.py
cefa94e24b51354cdc353a8ee6a1abddbab94b73c1b698361c2f2c9a669ac523  adversarial.log
014e7305f20bef784af3c0bb001baa5a82d7cfcf15d053de9557b56f838be80f  factor_check.py
daa85a2fafb32abd3d7071dc29de57660ada0cff31d4928fd4b6a24461eebf49  factor_check.log
6c6a98e37fb86bd0b6ad121d810e6575b12f36f74a2720f9a5366f51163eb56a  embedded-checks.log
51db68cad02a6e9ddebf405582bd669f79d9740478a8825f4f62d2969feece3e  allikvere.pdf
629e9de77b6ccb06a7dc27193fbee4f6bcaa97bad0e1a697a593fe53d805c522  allikvere.tex
aad0ea5bd88fc9158a46f5c7d61bc78d5f905e8fc16689dba2491f7c8bc4a6cc  dejesus-irrationality-v3.pdf
4018320b5675b56bf671e828d3eb322207fc3a29dbd15d621022f46ef7c8cce3  cassidy.md
07da25ce1903f4da90038d77493270c4781b5d2ef87f7e03d3fa6d03545e07f5  rstation-v2.md
e541e2a7be94a20a9880ecefdca4459a5c346579203b9222f4556f62cce561d9  rstation-v3.md
d2366667b18ad5d58baf8be8675be5e20a7207f280be3223cee407f752dbb340  zenodo-21543841.json
b09a8f1f89076c03720cf2fe54fe4b2e86adc81645933a0ebf3f9db4c1da12a3  zenodo-23108370.json
```

Other source versions are pinned by their DOI/arXiv version/Git SHA in the
report. Monks–Yazinski's author PDF is dated July 10, 2002; its journal year
is 2004. The Rozier–Terracol comparison uses arXiv v5, not a guessed journal
version. The rStation v3 consumer is positive-rational and its platform
acceptance is not called journal peer review. Molchanov OCR and inaccessible
full-proof details remain explicitly limited in the report.

### Live state recheck before the final report push

Remote refs still give main `2efdd2b531d511a8c6204e1f43179761585ab066`,
PR #20 `d270b4466794badc49da6feebefeda77f5793e16`. The GitHub connector
independently confirms PR #20 open/unmerged at that SHA. Its run
[43619826721](https://github.com/hipotures/collatz-lab/actions/runs/43619826721)
is completed/success. This is separately observed CI, not the source of the
mathematical verdict. The review does not authorize integration.
