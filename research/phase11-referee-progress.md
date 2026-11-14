# Phase 11 independent referee journal — issue #21

## Resume here

- Review branch: `review/phase11-independent-audit`, based on `main`
  `2efdd2b531d511a8c6204e1f43179761585ab066`.
- Review clone: `/home/user/DEV/collatz-lab-phase11-review`.
- Exact audited PR #20 head: `d270b4466794badc49da6feebefeda77f5793e16`,
  branch `codex/phase11-noncontracting`, open and unmerged when inspected.
- Detached validation clone: `/home/user/DEV/collatz-lab-phase11-audit`.
- External evidence directory: `/home/user/DEV/collatz-lab-phase11-evidence`.
- Pushed checkpoint: this initial journal; obtain its exact SHA with
  `git log -1` and `git ls-remote origin refs/heads/review/phase11-independent-audit`.
  The next checkpoint records this SHA explicitly (a commit cannot contain its
  own hash).
- Completed input reading: complete issues #21/#19, PR #20 metadata and empty
  discussion threads; root AGENTS.md; the six Phase 11 modules; all three
  Phase 11 Python verifiers, signatures and validation script; the specified
  Phase 9/10 context reports and paper README; rational, substitution, signed
  normalization, inverse branch, balance, contraction and exponential-gap
  source interfaces and proofs. `RationalSeed.lean` does not exist: the actual
  definitions are in `CollatzLab/Word.lean`.
- Preliminary independent arithmetic: a repeated prefix gives the modulus
  `2^(m+ell)`; a vanishing closing form gives an actual positive-time return,
  without the global Periodicity Conjecture. No defect found in these steps.
- Running: fresh `bash research/phase11/validate.sh`, output `validate.log`
  in the evidence directory. Its outcome is not yet claimed.
- Outstanding: independent exact-arithmetic adversarial computation; finish
  spectral reconstruction and edge cases; exact signature/axiom checks;
  primary-source comparison; complete referee report and separate review PR.
- Next: inspect the validation exit status; run the signature command and
  exact 564-entry axiom audit; obtain primary texts, particularly earlier
  repetition criteria and the October 2026 Dejesus/rStation manuscripts.
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
