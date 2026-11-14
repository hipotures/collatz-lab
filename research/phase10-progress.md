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
- This checkpoint's commit is the first feature-branch commit after the exact
  base above; resolve its full SHA with `git log --format='%H %s'`.

## Required validation at a compiling milestone

```sh
lake build
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 318
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/phase8/verify_polynomial.py
python3 research/mahler-uncovered/verify_uncovered.py --check
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
4. Prove `100/110` aperiodicity by period reduction modulo three, its nine-step
   bound, rational exclusion, and every shifted-tail corollary.
5. Validate, commit, push, and open an unmerged PR against main; continue bounded
   finite-language research only after the principal theorems compile.
