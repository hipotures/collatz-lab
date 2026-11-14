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
- This checkpoint follows the exact Milestone A commit above. Recover its SHA
  with `git log --format='%H %s'` (message: "Prove aperiodic unequal 100/110 rational exclusion and tails").

## Failed routes / cautions

- No mathematical candidate claim failed. A per-image maximum multiplier
  cannot prove contraction: the zero image has `9>8`; grouping is necessary.
- `000` alone must be excluded globally, not just within images. The Lean proof
  quantifies over every source index and uses the forced multiple-of-three column.
- The universal safe offset cap is 19171; the sharper finite cap 761 requires
  a language or expanded-window certificate before use in an infinite theorem.

## Required validation at a compiling milestone

```sh
lake build
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 350
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/phase8/verify_polynomial.py
python3 research/mahler-uncovered/verify_uncovered.py --check
python3 research/phase10/verify_unequal.py --check
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
4. Milestones A/B are complete and fully validated. Open an unmerged PR against
   main, with `Refs #16` and explicit hold for issue #15 and user approval.
5. Continue Milestone C: bounded length-2..6 / h<=8 substitution search, exact
   finite-language certificates, a second aperiodic example (`110/100` is a
   promising independent column-recursion candidate), and uniform frequency
   bounds. Consult a small set of primary sources and record precise comparisons.
6. Commit/push each validated milestone. Do not merge, force-push, touch Fable's
   files, or infer completion from a context/token limit.
