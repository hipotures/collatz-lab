# Phase 7 research campaign — issue #13

Work directly on `main`; never force push. Starting HEAD (2026-11-14 UTC):
`d0ced40fd35af9b94fa6373c9f5e913a58018cc7`. `git fetch origin` and
`git pull --ff-only` succeeded; working tree was clean.

## Milestone status

- A: COMPLETE — `lean-family-semantic-audit.md`; no critical defect found.
  Eight new declarations in `CollatzLab/FamilySemanticChecks.lean`.
- B: PARTIAL — arbitrary finite images, correct fixed point, affine blocks,
  finite Mahler/base identities, exact signed offset valuation, first
  disagreement, multiplier factorization and the exactly cancelled signed
  tower and exact residual valuation kernel-check. The generic irrationality
  theorem is NOT VERIFIED.
- C: PRIMARY TARGET PROVED in Lean — `10/01`, all shifts and eventual shifted
  matches. Both targets have degree 1–24 exact certificates; secondary
  `101/011` has a complete written proof, kernel work remains.
- D: GENERIC SUBCRITICAL THEOREM PROVED in Lean with explicit aperiodicity
  hypothesis; extends the contraction proof beyond the single primary instance.

## Verified starting facts

- Read issue #13 and its required current sources, including §§8–9 of
  `mahler-generalization.md`, the family modules, the semantic audit,
  Python/Rust finite checks, README, axiom audit and CI.
- Existing public predicate is `RealizesWord p q v`, with positive odd `q`
  and the accelerated map's actual numerator parity at every natural index.
- Existing family theorem quantifies over every `L >= 4` and every integer
  `p,q`; it has no finite search parameter. New verification is pending.

## Next three proof obligations

1. Prove the generic height bound under (C)'s exact exponent ledger.
2. Prove the strict-gap contradiction under (C),
   including the singly exponential factor `(2L)^k`.
3. Kernel-check the secondary degree-2 certificate using the division-free
   `s=0,e=1,L=3` tower described in the uncovered-morphism report.

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

## Checkpoint B1 (2026-11-14 UTC)

- A pushed as `1d9d111489e9cf97858e3aecc4c39b7f3e714197`.
  CI success: https://github.com/hipotures/collatz-lab/actions/runs/43552062967.
- New generic modules: `MorphismWord`, `MorphismPrefix`, `MorphismParameters`,
  `MorphismOffset`. No finite catalogue is substituted for the generic result.
- Exact signed offset quotient and first disagreement are proved for arbitrary
  images. Canonical criterion examples `110/011` (passes), `10/01` and
  `101/011` (fail) are kernel reductions.
- Next B obstruction is the signed cancelled congruence tower with full modulus
  after division by `a^s`. Full target signatures and subsequent obligations
  are in `lean-equal-weight-formalization.md`; B is incomplete.
- Pursue C's elementary invariants next before spending the remaining session
  exclusively on tower bookkeeping. The `10/01` blocks have slope `3/4`:
  bounded fixed-denominator rational dynamics may exclude their aperiodic word.
  This is a proof direction, not yet a claimed theorem.

## Checkpoint C1 / D1 (2026-11-14 UTC)

- B1 pushed as `f0096192a39587f009ccae133b628babe44486b8`.
  CI success: https://github.com/hipotures/collatz-lab/actions/runs/43552993269.
- `Subcritical.lean`: bounded natural collision, deterministic repetition,
  contracting integer recurrences, and generic subcritical rational exclusion.
- `ThueMorse.lean`: independent even/odd recurrences, full aperiodicity proof,
  `no_rational_seed_realizes_thueMorse`, arbitrary shifted and eventual tail
  exclusions. All numerators and positive odd denominators are covered.
- `verify_uncovered.py --check`: 48 Padé rows, 8 residue checkpoints, 32,800
  signed rational candidate checks. Three independent Rust tests verify all
  pairs and the selected form valuations. No degree extension beyond 24.
- The secondary pair is **not novel**: upstream's existing finite catalogue
  at `ec8174b` already records `[1],[-1,0,1]`, order 5, coefficient -1.
  The report gives a full infinite algebraic proof and its exact kernel gap.
- Validation: `lake build`; 83-declaration axiom audit; formatting; Clippy;
  **93 Rust tests pass**; no forbidden library tokens. Only standard Lean
  foundations. Python artifacts reproduce exactly; CI runs that check too.
- Do not repeat unsuccessful degree-0 truncations or treat (C)'s failure as a
  rational example. Do not infer generic aperiodicity from H1–H3 without proof.

## Checkpoint B2 (2026-11-14 UTC)

- C1/D1 pushed as `cef06e304de989d36820de80496b61ccbed84dcb`.
  CI success: https://github.com/hipotures/collatz-lab/actions/runs/43553950577.
- The B1 tower obstruction is resolved by signed denominators. New modules:
  `MorphismTransport.lean`, `MorphismPolynomial.lean`, `MorphismTower.lean`.
- Kernel proves Gamma's exact support factor and odd unit, `s<e<L`, exact
  initial division, all-level `a_k^s | delta_k`, odd signed denominators,
  and full congruences at every `k,n` for arbitrary admissible images.
- The initial congruence uses old length `n+1`; the tower transport uses old
  length `L*(n+1)`. Removing powers of 2 at shorter lengths loses precision.
- Still no generic irrationality export: valuation, heights and the final
  strict-base-gap growth lemma must be supplied first.
- B2 also completed `MorphismApprox.lean`: a generic finite convolution/tail
  identity proves a unit leading residual and exact all-level valuation
  `N*L^(k+1)`. Only heights and the strict-gap growth argument remain on the
  principal route. The audit now has 95 declarations; Rust tests remain 93.

## Resume here

Read this file and `git log -5 --oneline`, fetch/pull `origin/main`, then inspect
the milestone documents and existing Lean modules. Starting commit is recorded
above; A and the primary C target are complete. B remains incomplete. Follow
the next three obligations above. Run the complete issue-required
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
