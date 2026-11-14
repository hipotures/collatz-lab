# Phase 7 research campaign — issue #13

Work directly on `main`; never force push. Starting HEAD (2026-11-14 UTC):
`d0ced40fd35af9b94fa6373c9f5e913a58018cc7`. `git fetch origin` and
`git pull --ff-only` succeeded; working tree was clean.

## Milestone status

- A: COMPLETE — `lean-family-semantic-audit.md`; no critical defect found.
  Eight new declarations in `CollatzLab/FamilySemanticChecks.lean`.
- B: COMPLETE — generic Theorem 8.1 with exactly H1–H3 and (C), shifted
  tails and eventual shifted matches kernel-check. No finite catalogue or
  additional sign/height hypotheses. See `lean-equal-weight-formalization.md`.
- C: BOTH TARGETS PROVED in Lean — `10/01` and `101/011`, all shifts and
  eventual matches. Primary has independent contraction and Mahler proofs.
  Both targets have degree 1–24 exact finite certificates.
- D: GENERIC SUBCRITICAL AND PERIODIC-CONTROL THEOREMS PROVED in Lean.
  Uniform aperiodicity now removes the first theorem's extra premise.
  Periodic-control data cover all 144 listed small morphisms. Numerical
  degree-six and non-unit leading-coefficient lemmas also kernel-check;
  a universal supercritical exclusion is NOT claimed.

## Verified starting facts

- Read issue #13 and its required current sources, including §§8–9 of
  `mahler-generalization.md`, the family modules, the semantic audit,
  Python/Rust finite checks, README, axiom audit and CI.
- Existing public predicate is `RealizesWord p q v`, with positive odd `q`
  and the accelerated map's actual numerator parity at every natural index.
- Existing family theorem quantifies over every `L >= 4` and every integer
  `p,q`; it has no finite search parameter. New verification is pending.

## Next three proof obligations

1. Generalize the finite convolution/interface to arbitrary polynomial pairs;
   integrate the proved non-unit leading-coefficient lemma and finite `k0`.
2. Prove the binary finite-memory recurrence -> eventual periodicity bridge;
   use the now-proved generic aperiodicity to exclude an identically zero residual.
3. Kernel-prove existence of a degree-six/order-at-least-thirteen integer pair
   (six equations, seven unknowns), or certify the finite 13-symbol-prefix cache.
   Keep the raw degree-six pair to avoid common-shift order bookkeeping.

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

## Checkpoint B3 (2026-11-14 UTC)

- B2 pushed as `ade482f541ab0d314cec860f12144bc450ea5f08`.
  CI success: https://github.com/hipotures/collatz-lab/actions/runs/43554808926.
- `MorphismHeight.lean` proves the general height chain retaining `(2L)^k`.
  `ExponentialGap.lean` proves that any strict positive integer base gap
  dominates that factor using homogeneous Bernoulli and a finite index.
- `EqualWeight.lean` exports the single generic rational theorem and both
  tail corollaries. Positive denominator/sign conversion is also kernel-checked.
- `EqualWeightChecks.lean` specializes both `110/011` and `1100/1010`.
  The second has `A>B`, `s=1`, and negative signed `D_0=-7` at `q=1`;
  literal prefixes and actual integer witnesses 187 and 12947 verify semantics.
- Current full audit: 118 declarations; expected Rust tests: 93.
  A clean rebuild is used for this major checkpoint; no unproved theorem
  or forbidden proof escape is introduced.

## Checkpoint C2 / D2 (2026-11-14 UTC)

- B3 pushed as `f365bf53998d53054a05d479863d838251deb91e`.
  CI success: https://github.com/hipotures/collatz-lab/actions/runs/43556057828.
- `PeriodicCertificate.lean` proves a generic periodic-control exclusion from
  finite validity and `2^(L*(L-1)*N)>m^(P*(L-1)+L+e)`. The control period is
  independent of the substitution length. Exact all-level valuation and heights
  reuse the generic tower; no irrationality assertion is a certificate input.
- `Secondary.lean` kernel-checks block `10`, `P=2,N=5`, for `101/011`, plus
  its rational theorem and tails. The actual 32-symbol integer prefix witness
  2567104865 reaches 6252160216.
- A second primary certificate, block `100101`, `P=6,N=10`, gives
  `2^20>4^9` and `no_rational_seed_realizes_thueMorse_mahler`, independently
  of the contraction/aperiodicity proof.
- Current validation: 137 approved axiom-audit declarations, 93 Rust tests,
  formatting, Clippy, build and Python reproduction. No forbidden library tokens.

## Checkpoint D3 (2026-11-14 UTC)

- C2/D2 pushed as `2a59ac3` (full SHA available from `git rev-parse 2a59ac3`).
- Deterministic period 1–24 search finds certificates for all 144 admissible
  morphisms with `2<=L<=5`; maximum selected period 15, maximum order 23.
  Old (C) covered 65; improved certificates add 79 words.
- `SmallCertificates.lean` is generated by `verify_uncovered.py` and accepted
  by the kernel. Its explicit-list theorem excludes every rational seed for
  each listed word. A fourth independent Rust test verifies the complete
  finite enumeration and every control/ledger.
- Period <=12 misses exactly four L=5 cases, all with image `1 -> 10011`;
  period 15 covers them. This justified testing the rest of the original
  period <=24 bound, without extending Padé degrees beyond 24.
- Validation: 140 approved audit declarations, 94 Rust tests, build, formatting,
  Clippy and deterministic Python/Lean artifact reproduction all pass.

## Checkpoint D4 (2026-11-14 UTC)

- D3 pushed as `8215b87f1ebab15349e59692aa260a977e5b8a61`.
  CI success: https://github.com/hipotures/collatz-lab/actions/runs/43557345614.
- `MorphismAperiodic.lean`: all admissible equal-weight fixed points are not
  eventually periodic. Kernel proof descends period by gcd; the coprime case
  gives `L|r`, contradicting `1<=r<L`. This is word combinatorics, not the
  rational Periodicity Conjecture.
- Thus all subcritical `3^r<2^L` cases and all tails are rationally excluded
  with exactly H1–H3 and the subcritical inequality.
- `DegreeSix.lean`: numerical gap for degree 6/order 13 holds for all admissible
  parameters. This does not prove existence/nonvanishing of a Padé pair.
- `LeadingCoefficient.lean`: exact valuation of `2^v*c_odd+2^m*t` for `v<m`,
  and existence of a finite tower starting level. The degree-six TM coefficient
  8 refutes a unit-leading shortcut; it does not refute the proposal.
- `UnequalControl.lean`: distinct prolongable images `101/010` have unequal
  weights and the rational fixed word `(10)^infinity`, realized by seed 1.
  Dropping equal weights is refuted, including infinite rational semantics.
- `phase7-next-directions.md` gives exact current signatures, the complete
  aperiodicity proof, the unfinished proposal and ranked next obligations.
- Local validation: 157 approved audit declarations, 94 Rust tests, build,
  formatting, Clippy and deterministic artifact reproduction pass. Long public
  names caused Lean to wrap audit lists; the new strict parser accepts only
  approved-foundation continuations and checks the exact source declaration
  order/count. Its 2 positive and 8 adversarial tests pass; no trust gate is relaxed.

## Resume here

Read this file and `git log -5 --oneline`, fetch/pull `origin/main`, then inspect
the milestone documents and existing Lean modules. Starting commit is recorded
above; A, B and the primary C target are complete. Follow
the next three obligations above. Run the complete issue-required
checks before each formal checkpoint:

```text
lake build
lake env lean research/lean-audit/FamilyAudit.lean
lake env lean research/lean-audit/FamilyAudit.lean | python3 research/lean-audit/check_axioms.py --expected-count 157
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
rg -n '\b(sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|extern)\b' CollatzLab CollatzLab.lean
```

An empty last command output is success (exit status 1). Commit and push each
validated milestone to `origin/main`. B is complete; the open research extension
is the arbitrary polynomial-pair certificate and its degree-six existence proof.
