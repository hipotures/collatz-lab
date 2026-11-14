# Phase 7 research campaign — issue #13

Work directly on `main`; never force push. Starting HEAD (2026-11-14 UTC):
`d0ced40fd35af9b94fa6373c9f5e913a58018cc7`. `git fetch origin` and
`git pull --ff-only` succeeded; working tree was clean.

## Milestone status

- A: COMPLETE — `lean-family-semantic-audit.md`; no critical defect found.
  Eight new declarations in `CollatzLab/FamilySemanticChecks.lean`.
- B: NOT COMPLETE — generic Theorem 8.1 is still a written proof.
- C: NOT STARTED — prioritize `10/01`, then `101/011`; exact degree 1–24 search.
- D: NOT STARTED — choose after the primary obstruction is understood.

## Verified starting facts

- Read issue #13 and its required current sources, including §§8–9 of
  `mahler-generalization.md`, the family modules, the semantic audit,
  Python/Rust finite checks, README, axiom audit and CI.
- Existing public predicate is `RealizesWord p q v`, with positive odd `q`
  and the accelerated map's actual numerator parity at every natural index.
- Existing family theorem quantifies over every `L >= 4` and every integer
  `p,q`; it has no finite search parameter. New verification is pending.

## Next three proof obligations

1. Encode arbitrary binary morphisms, prove the correct fixed point and literal
   block recurrence without imposing extra mathematical hypotheses.
2. Derive the generic affine offsets and signed, exactly cancelled congruence
   tower; isolate any unproved obligations explicitly before proceeding to C.
3. Formalize the generic first-difference/height contradiction under (C).

## Checkpoint A (2026-11-14 UTC)

- `lake build`: success. Axiom audit: 52 expected declarations; only standard
  foundations (or none). Forbidden-token scan: empty.
- `cargo fmt --check`: success; Clippy with `-D warnings`: success;
  `cargo test --locked --all-targets`: **90 passed**, zero failures.
- Literal substitution lists, direct integer residue lifts, negative rational
  prefixes at denominator 5, unreduced denominator 15, and infinite negative
  all-one realization are independently kernel checked.
- No change to a mathematical theorem was needed. Repaired a stale README
  claim about compilation and identified the Phase 6 audit count as historical.

## Resume here

Read this file and `git log -5 --oneline`, fetch/pull `origin/main`, then inspect
the milestone documents and existing Lean modules. Starting commit is recorded
above; A is complete. Continue B, then C, D. Run the complete issue-required
checks before each formal checkpoint:

```text
lake build
lake env lean research/lean-audit/FamilyAudit.lean
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
rg -n '\b(sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|extern)\b' CollatzLab CollatzLab.lean
```

An empty last command output is success (exit status 1). Commit and push each
validated milestone to `origin/main`; leave issue #13 open while B is incomplete.
