# Phase 11 independent referee journal — issue #21

## Resume here

- Review branch: `review/phase11-independent-audit`, based on `main`
  `2efdd2b531d511a8c6204e1f43179761585ab066`.
- Review clone: `/home/user/DEV/collatz-lab-phase11-review`.
- Exact audited PR #20 head: `d270b4466794badc49da6feebefeda77f5793e16`,
  branch `codex/phase11-noncontracting`, open and unmerged when inspected.
- Detached validation clone: `/home/user/DEV/collatz-lab-phase11-audit`.
- External evidence directory: `/home/user/DEV/collatz-lab-phase11-evidence`.
- Last pushed checkpoint: `031e4a7bbf4ff29c4633b97e46d008e31a246747`
  (initial journal). The next checkpoint adds the independently reconstructed
  proofs and verified results; a commit cannot contain its own hash.
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
- Outstanding: finish exact Lean audit/signature matrix, literature matrix,
  source checksums, independent checker appendix, final publication advice,
  and separate review PR. Draft report already contains all elementary proofs.
- Next: complete report sections 5–6 and appendices; verify source mapping,
  refresh live refs without altering the audited SHA, commit and push.
- No source proof, manuscript, author metadata, issue #15, original checkout,
  or Codex branch has been changed. No PR has been merged and no issue closed.

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
