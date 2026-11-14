# Phase 10: unequal-weight contraction checkpoints

Issue: <https://github.com/hipotures/collatz-lab/issues/16>

Branch: `codex/unequal-weight-contraction` exclusively. Base: fetched
`origin/main` at `d2a71facd7135118a562de8a7903b8827934c3ac` (2026-11-14 UTC).
No changes to the Phase 9 manuscript, reports, or Fable's research files.
Do not merge this branch. Integration requires completion of issue #15 and
explicit user approval. Never force-push.

## Milestone A: validated generic criterion

- Read the complete issue and its specified Lean sources and Phase 8 scope.
- Confirmed the real signed numerator dynamics and positive odd denominator
  semantics can be reused without modification.
- The generic affine-prefix identity already supports variable odd counts;
  the equal-weight block recurrence and aperiodicity theorem cannot be applied
  to the new example.
- Kernel-checked `variable_contracting_recurrence_bounded` with radius
  `absInt (y 0) + C`; the existing constant theorem is a specialization with its
  public signature preserved.
- `MorphismContraction.lean` proves the exact variable single-block and arbitrary
  chunk recurrences, source-image weight sum identity, universal offset cap
  `3^k-2^k`, bounded-block periodicity, and the generic unequal-weight exclusion
  criterion. Generic inverse-branch shift and eventual-tail closure compile.
- `research/unequal-weight-contraction.md` records the complete generic proof
  and source/theorem mapping. No external literature result enters the proof.
- Full validation passed: `lake build`; **318 exact audited declarations**;
  parser self-tests; **94 Rust tests**, formatting and Clippy; both required
  Python verifiers; empty forbidden-proof scan; `git diff --check`.
- Pushed commit: `264f694d978e8756c1b59d01501626122affdbd2`.

## Milestone B: validated concrete exclusion and every tail

- `Unequal100110.lean` kernel-proves literal images, weights 1/2, distinctness,
  prolongability, all three recurrences, and non-eventual-periodicity by strong
  induction on the period. The proof handles an arbitrary eventual starting index.
- Proved no `000` in any source window, image-weight sum at most five over
  three source symbols, every aligned nine-step odd count at most five,
  `243<512`, the uniform offset cap 19171, and the true nine-step recurrence.
- `no_rational_seed_realizes_unequal_100_110 (p q : Int)` has no extra seed
  hypotheses. Every finite shift, eventual shifted tail, integer seed, and
  integer forward-orbit corollary is proved via the verified generic closures.
- Independent literal iterates through 81 symbols match the indexed word.
  An actual positive integer and signed/reducible rational pairs have the same
  81-bit prefix, with exact end states. Universal signed/unreduced parity
  equivalence is proved via the unchanged `numIter_equiv`.
- The `101/010` rational control remains explicitly realized and periodic.
- `research/phase10/verify_unequal.py --check` reproduces seven finite 9-step
  rows, the three signed prefix witnesses and a negative-denominator normalized
  prefix. It performs no interval seed search. The finite sharper offset cap
  761 is not yet the cap used by the infinite Lean proof.
- Full validation passed: `lake build`; **350 exact audited declarations**;
  parser self-tests; **94 Rust tests**, formatting, Clippy; both existing Python
  verifiers and the new deterministic checker; empty forbidden-proof scan;
  `git diff --check`.
- Pushed commit: `fc5bf15375bb8a3a00ed08508b9672c1045bb937`.
- [PR #17](https://github.com/hipotures/collatz-lab/pull/17) is open, unmerged,
  with the explicit hold for issue #15 and user approval. GitHub reported it
  mergeable on inspection; that is not permission to merge.

## Milestone C1: validated finite certificate interface and second example

- `WindowCertificate.lean` proves infinite coverage by strong induction on
  window position from finite initial membership and substitution closure.
  It links finite image-weight and expanded-offset tables to every window.
  No primitivity or recurrence hypothesis is needed for this certificate.
- `UnequalCertificates.lean` gives the exact six-window language for `100/110`,
  kernel-checks closure and occurrence of each row, applies the generic finite
  certificate to rational exclusion, and proves the sharp infinite offset cap
  **761**, attained at index zero. The two-source criterion fails at the aligned
  `00` window beginning at source index ten.
- `ColumnAperiodic.lean` proves the generic ternary-column period descent for
  an injective middle-column map and forced endpoint columns 1 and 0.
- `Unequal110100.lean` proves a second genuinely aperiodic unequal example,
  `1 -> 110`, `0 -> 100`, with weights two/one, a locally expanding image,
  exact finite language, nine-step count/offset/recurrence, universal rational
  exclusion, shifts, eventual tails, and an actual positive 81-bit witness.
- `SignedContraction.lean` proves universal normalization of both numerator
  and odd denominator signs using unchanged `numIter_equiv`, and extends raw
  eventual-tail exclusions for both examples to either sign of odd denominator.
- Bounded exhaustive Python search: **2092 unequal pairs**, **16736 languages**
  at lengths 2..6 and h=1..8; **1284** have a contraction certificate, **688**
  including a locally expanding image. Only the two named Lean examples are
  claimed as rational exclusions; periodic `101/010` also contracts at h=2.
- Full validation passed: `lake build`; **396 exact audited declarations**;
  parser self-tests; **94 Rust tests**, formatting, Clippy; all four Python
  checkers; empty forbidden-proof scan; `git diff --check`.
- Checkpoint follows B above, commit message: "Certify finite languages and a second unequal rational exclusion".

## Failed routes / cautions

- No mathematical candidate claim failed. A per-image maximum multiplier
  cannot prove contraction: the zero image has `9>8`; grouping is necessary.
- `000` alone must be excluded globally, not just within images. The Lean proof
  quantifies over every source index and uses the forced multiple-of-three column.
- The universal safe offset cap is 19171; C1 now proves the sharper 761 cap
  universally using the finite language and expanded-window bridge.
- Finite maxima need not contract at every larger h: `1000/1110` passes at
  h=4 and h=8, but fails at h=5,6,7. The length-five candidate `10000/11110`
  fails at all h<=8 despite a candidate frequency one-half; this cutoff is not
  a proof that every longer uniform certificate fails.

## Required validation at a compiling milestone

```sh
lake build
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 396
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/phase8/verify_polynomial.py
python3 research/mahler-uncovered/verify_uncovered.py --check
python3 research/phase10/verify_unequal.py --check
python3 research/phase10/search_unequal.py --check
git diff --check
```

Update the exact audit count as new theorem exports are added. Scan Lean source
for forbidden proof escapes using the existing CI pattern. Push each validated
milestone to `origin/codex/unequal-weight-contraction`.

## Resume here

1. Run `git status --short --branch`; stay on the named feature branch.
2. Inspect the latest commit with `git log -1 --format='%H %s'` and this file.
3. The generic criterion is complete; do not redo it. See theorem map in
   `research/unequal-weight-contraction.md`.
4. Milestones A/B/C1 are complete and fully validated; PR #17 stays unmerged.
5. Continue C2: derive an exact uniform frequency/spectral bound with controlled
   boundary errors, and finish focused primary-source comparisons. Optional:
   kernel-prove length-four `1000/1110` (h=4, R=10) and its aperiodicity;
   its middle columns are both complements and endpoints are forced 1/0.
   No extra global search is needed; the existing bounded search is complete.
6. Commit/push each validated milestone. Do not merge, force-push, touch Fable's
   files, or infer completion from a context/token limit.
