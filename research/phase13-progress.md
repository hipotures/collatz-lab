# Phase 13 research journal — issue #28

## Resume here

- Isolated clone: `/home/user/DEV/collatz-lab-phase13`.
- Branch: `codex/phase13-rational-height`, based on live origin/main
  `93647176a526eb8660b4dbf2ac428b0053117659` (checked 2026-11-15).
- Checkpoint A pushed normally:
  [`25eaf8e992108bf4bc3aeccfd4b020551951d2a7`](https://github.com/hipotures/collatz-lab/commit/25eaf8e992108bf4bc3aeccfd4b020551951d2a7).
- Checkpoint B pushed normally:
  [`282b3715c95c26bac1077fecd0df457bd277cb57`](https://github.com/hipotures/collatz-lab/commit/282b3715c95c26bac1077fecd0df457bd277cb57).
- Checkpoint C/D pushed normally:
  [`2684bc31f434ea988f60ac6687345cd18ab8474f`](https://github.com/hipotures/collatz-lab/commit/2684bc31f434ea988f60ac6687345cd18ab8474f).
- Checkpoint E pushed normally:
  [`aa446dad0c1e096ec82e44c5ae93f0fe93eff7ca`](https://github.com/hipotures/collatz-lab/commit/aa446dad0c1e096ec82e44c5ae93f0fe93eff7ca).
  All-level explicit rational shadows and finite height bounds are Lean
  verified; full clean validation passes. Ten families through 16,384 bits
  have 1,691 independently verified optimality certificates. This journal-only
  handoff follows that immutable proof checkpoint; `git log -1` identifies
  the handoff's own SHA.
- Review [PR #29](https://github.com/hipotures/collatz-lab/pull/29) is open,
  unmerged, against unchanged main `93647176a526eb8660b4dbf2ac428b0053117659`.
  Issue #28 remains open; issue #15 and the manuscript are untouched.
- Main checkout `/home/user/DEV/collatz-lab` and the manuscript worktree are
  untouched. No agents were spawned. Do not switch those checkouts.
- Gate 0 found direct prior coverage: Klapper–Goresky 1997 minimizes exactly
  our odd-denominator norm; Klapper 2007 gives accumulation set `[B,1-B]`.
  Candidate-specific B is still unresolved. No original theorem advertised.
- Read `phase13-prior-art.md` and `phase13-theory.md` first. Source cache and
  supplementary evidence: `/home/user/DEV/collatz-lab-phase13-evidence/`.
  Third-party texts are not committed; source hashes are reproducible metadata.
- Engine obligation completed: reference floor-sum search, adaptive odd-coset
  search, independent minimality verifier, all small residues and signed parity
  cylinders. H_11=3 / H_12=513 reproduced by actual numerator scans.
- Research conclusion: the normalized profile does **not** converge, with
  `(1-c)/6<=B<=c`, `c=(25/98)log2(3)`. The reduced shadows give exact minima
  along every L_k. Raw coprimality fails at k=7 (gcd 347), and exact modular
  cycles prove infinite common factors 347 and 347^2. All are known-method
  specializations, with no priority claim. Real-limit / modular-cycle deductions
  are written proofs, not separate Lean limit theorems.
- **Next mathematical obligation:** determine B, controlling odd gcd growth
  and possible better approximants between L_k. A precise conditional bound
  `(1-c)/(1+5c)<=B` is proved if shadow heights have exponent c; that premise
  is not assumed unconditionally. Do not redo the completed engine or known
  irrationality proof. Read theory Sections 6–9 and `modular.json` first.
- **Next command after fetching/checking status:** `bash research/phase13/validate.sh`.
  It reproduces all inherited checks and bounded new evidence. The audit has
  **653** exact entries (60 new, 593 baseline preserved), wired to CI.
- All gates have a reviewable conclusion at PR #29. Integration, issue closure
  and any publication remain owner decisions. The final handoff below records
  PR/head CI without merging anything. Check live PR head/CI before continuing;
  no process or agent is assumed to remain active after this session.

## Source-gate record

Read issue #28 and its full requirements, AGENTS.md, live refs/CI, Phase 12
findings Section 5 and source matrix, both independent referee reports, Phase 9
prior-art review, and the required Lean word/return/balance/spectral modules.
Primary-source matrix records exact original passages and proof-access limits.
Allikvere, Cassidy, Dubickas, Monks–Yazinski and De Jesús downloads match the
Phase 12 hashes. De Weger, WGD, Klapper–Goresky, Klapper and Romeo originals
were obtained. Bernstein 1994 was supplied locally by the owner during this
session and read. Publisher Bernstein–Lagarias was obtained after the author
URL returned 403. Ward's 2021 original statements were obtained; the 2026
publisher original was inaccessible and is not claimed read.

Failed source guesses: Romeo arXiv 2306.14823 is unrelated; discard it.
Correct version: 2306.14837v1. Bernstein's first guessed AMS suffix was
incorrect; the owner's 1186982-9 PDF is the correct original. These are access
errors, not mathematical counterexamples. No proof or implementation has
been abandoned as an unstated gap.

## Checkpoint discipline

Keep exact outputs separate from runtime/memory observations. Every proof
checkpoint must run the current full inherited validation and update audit
names/count together. Before the final handoff, clean-build Lean and read
remote PR CI at the exact head. Store durable failed approaches, counterexamples,
open proof obligations and next commands here; do not assume a background
agent or process survives a session.

## Checkpoint B actual validation and failures

- `python3 research/phase13/test_height.py`: pass, 25,432 signed floor sums,
  all 4,095 residues through 11 bits, 31,750 signed cylinder controls,
  262,400 actual numerator exclusions below H_12, seven hostile certificates.
- `python3 research/phase13/experiments.py --write --max-bits 1024`: complete,
  ten word/control families, 1,340 certificates. Independent certificate
  command passes for every witness, parity prefix and minimality transcript.
- Reference/optimized comparisons also pass at 64,127,256,511 bits and on
  separate residues `7^n mod 2^n` at 1,024 and 2,048 bits. Reference runtimes
  in this environment were 0.995s / 11.488s (not a complexity theorem).
- Large-integer intermediate states initially made certificates 14 MB at
  1,024 bits. Quotient-only transcripts preserve every checked identity and
  reduce the same dataset to 2.8 MB. Full states are reconstructed by the
  independent verifier. No floating-point height decisions occur.
- Initial HTTPS push failed without a credential helper. Changing only this
  clone's origin to the repository's existing SSH destination and reusing its
  existing SSH setting enabled an ordinary push. No force push or credential
  exposure occurred. Automatic local Git committer metadata was used; no
  manuscript identity/contact details were selected.
- No Lean changes yet; inherited validation is due at the theorem checkpoint.

## Checkpoint C/D research and validation

Historical C/D record (superseded by E where stated): read theory Sections 5–7.
The exact
first failures are L_k=(56*6^k-1)/5 and the shadow height is at most
T_k=14*6^k*3^((20*6^k-6*(-1)^k)/7). The retained-height determinant gives
H_(L_k)<=T_k and 2^L_k<=2*T_k*H_(L_k+1). Thus B<=c and limsup>=1-c,
c=(25/98)log2(3)<1/2: the normalized profile **cannot converge**. Choosing
the last failed shadow also gives B>=(1-c)/6. The exact B and infinite
minimality/gcd pattern are open. All are written deductions, with generic
kernel support under development; no novelty or optimality assertion.

Two serious approaches: height/exponent transfer and finite drift/confinement
(the latter needs finite state distinctness), and noncommutative substitution
inverse products / explicit rational shadows. The finite drift bound is
weaker, so it is retained as an attributed alternative, not a competing
headline. Primary source re-triage classifies the headline as a known-method
specialization. The nonconvergence claim was not inferred from a chart.

Actual commands/results:

- `experiments.py --write --max-bits 16384`: complete for all ten families;
  both sides of large jumps recorded. Highest primary failure is 14,516.
- Independent verifier: all **1,688** records pass primitive witness, actual
  parity, independent residue, determinant and no-smaller-height checks.
- `verify_analytics.py --write`: passes five exact shadow levels and first
  failures, all corresponding minimum/crossing checks and pressure controls.
- A first matrix-offset guess 89 was rejected by independent iteration.
  The correct literal 100111 offset is **179**; no theorem or data used 89.
  The noncommutative matrix entry is -28454. This illustrates the bit-order
  hazard in external tables; preserve this failed route as a regression.
- A 4,096-bit floor-sum reference search was cancelled by `timeout 55s`, exit
  124, without a result. Only the completed 2,048-bit comparison is claimed.
- Quotient transcripts at 16,384 bits were 58 MB as indented JSON; standard
  deterministic-time gzip stores the same exact evidence in 3.0 MB.
- Inherited clean baseline `lake build` completed successfully while the new
  module was developed separately. New-module direct compilation succeeds.
  Final full validation, axiom inventory and clean rebuild remain required.

## Checkpoint E: exact interfaces, deeper cancellation and validation

All 60 public declarations in the two scoped modules are explicitly audited.
The final source signatures check the parameter order, signed odd denominators,
finite quantifiers, primitive minimizers, all-level actual shadow realizations,
exact first mismatch, both integer height inequalities and both small minima.
No existing numStep/numIter/seedParity/RealizesWord meaning was changed.

The late gcd investigation was necessary: full integer matrices through k=7
give raw gcds `3,1,1,1,1,1,1,347`. Independent normalized affine-map cycles
have repeated states at 1/87 modulo 347, and 62/14940 modulo 120409. The
identity levels are 7 and 5425. The written induction proves infinitely many
raw common factors on the corresponding progressions. Constant factors do
not establish exponential cancellation. Exact subsequence minimality instead
follows from the strict height bound, with a finite base and `T_(k+1)<=T_k^6`.

Corrected formalization attempts: implication/iff precedence initially placed
oddness inside an equivalence; explicit parentheses repaired the exact intended
statement before any checkpoint. Lean's core has no Nat.find here, so the
minimum is constructed by strong induction and classical choice. The H_12
lower-bound proof needed the explicit odd-q identity
`p+3q=4096*(d+q/2)+2048`; giving that integer witness made the 513 bound
transparent. Intermediate elaboration failures were fixed without stronger
mathematical hypotheses or proof escapes. The final kernel build succeeds.

Actual completed clean validation: `lake clean` followed by
`bash research/phase13/validate.sh`, exit 0. Its inherited script actually ran:

| Command/check | Result |
|---|---|
| `lake build` after clean | Pass, final two new modules included |
| Full FamilyAudit and exact foundation parser | 653 names, only standard allowlist |
| Parser self-test and forbidden-escape scan | Pass; no forbidden proof escape |
| `lake env lean research/phase11/Signatures.lean`, Phase 12 and Phase 13 signatures | All pass |
| `cargo fmt --check` | Pass |
| `cargo clippy --locked --all-targets --all-features -- -D warnings` | Pass |
| `cargo test --locked --all-targets` | 94 pass, no failures |
| Phase 8 polynomial / Phase 7 uncovered / Phase 9 independent checkers | All pass |
| All five live Phase 10 checkers, all three Phase 11 checkers | All pass |
| Phase 12 exact return evidence and source inventory | Pass |
| `paper/check_tex.py` and generated Lean names | Pass; no manuscript/PDF change or readiness claim |
| Phase 13 exhaustive/signed/hostile tests | Pass, exact counts in checkpoint B |
| Phase 13 `experiments.py --check` | All ten 16,384-bit profiles reproduced |
| Independent certificate verifier | All 1,688 minimum certificates pass |
| Independent literal shadow checker | Five levels, first failures and exact bounds pass |
| `git diff --check`, Markdown fence check | Pass |

The later added modular checker separately passed `--write` and `--check`,
then was added to the final full wrapper/CI. A final wrapper rerun includes
it. Verification-only profile reproduction now omits tracemalloc, keeping
exact results/certificates identical while avoiding benchmark overhead in CI.
Approximate display ratios alone allow 1e-14 libm rounding; integer evidence
must match exactly. No performance improvement or mathematical result is
inferred from omitting that instrumentation.

Separate executed pipeline with `set -o pipefail`:
`lake env lean research/lean-audit/FamilyAudit.lean | tee /home/user/DEV/collatz-lab-phase13-evidence/axioms.log | python3 research/lean-audit/check_axioms.py --expected-count 653`.
It passed, as did separate Phase 12 and Phase 13 signature invocations.

Supplementary evidence in `/home/user/DEV/collatz-lab-phase13-evidence/`:

- Clean full `validate.log`, SHA-256
  `370e941d326d3dc92f3c8186bbb61193f716524b157d5a306a65e0e7a0a9e2d8`.
- Separate `axioms.log`, SHA-256
  `f96445e541b3068b67e596f6e9fe8941ef739a238f67933a5849c5be15e2a926`.
- Final wrapper output `validate-final.log`, exit 0, SHA-256
  `bddbf5760c56e78dcb0cdc8bded53a886509fb728b84460e15c78e5ffe5f35e9`.
  This includes the added modular checker. All scripts and exact fixtures are
  committed, so raw logs are supplementary, not required for reproduction.

After that full validation, three additional exact certificates were added
for every remaining reported dense extremum (Phase 8 N=141, SHA-256 N=141/204).
The complete **1,691-record** profiles were reproduced with the updated
checkpoint-selection rule, exit 0; the independent full certificate checker
also passed, exit 0. Supplemental certificate-only timing observations are
explicitly separated from the earlier benchmark run. No Lean/Rust source or
theorem changed after the clean validation.

- `profile-final.log` SHA-256
  `246eb42bd7ae5b0089ac12def2eaf920bc4f9194c4bf286732c84d3a2564e8f9`.
- `certificates-final.log` SHA-256
  `cb79a4754f655244084179de90cf9d66ae4ee1c42b8bd8cbadbad3397a8d664d`.

Late primary-source hits on algebraic digit values, maximum-order complexity
and p-adic continued fractions are explicitly screened in the source matrix's
last section, with inaccessible full texts marked. They supply no verified
premise about the digit or continued-fraction expansion of Phi(w). No negative
search or raw-gcd observation is treated as an originality proof.

No paper/, Phase 9 report, historical referee report, author/contact metadata,
main checkout, other branch or issue state was modified. No agents were
spawned, and no merge, publication or unsolicited message was performed.

## Review handoff and CI

The complete proof/evidence checkpoint was pushed as
`aa446dad0c1e096ec82e44c5ae93f0fe93eff7ca`. [PR #29](https://github.com/hipotures/collatz-lab/pull/29)
was opened against live main `93647176a526eb8660b4dbf2ac428b0053117659`.
The PR was independently read back open, unmerged and mergeable; mergeability
is not integration authorization. Issue #28 remains open. The original main
checkout was rechecked and remains clean on its original branch.

Proof-head [GitHub Actions run 43662662430](https://github.com/hipotures/collatz-lab/actions/runs/43662662430)
was actually read **completed/success** at 01:26:44 UTC on 15 November 2026.
Both `check` and `lean`, including every listed step, completed successfully.
The local clean build and full matrix are independently recorded above. This
final handoff commit changes only this journal; its own SHA is given by
`git log -1 --format=%H`. Check the live PR for any subsequent head and CI.

The reviewable program has passed Gates 0–5: primary-source comparison and
well-posed definitions; exact signed formal bridge/minima; independent exact
engines and certificates; bounded multi-family data; two serious analytical
routes, exact subsequence shadows and a falsified coprimality shortcut; scoped
kernel verification and independent replication. It does **not** determine
the exact B or claim a novel general theorem. Owner decisions are mathematical
review/integration and any separate publication assessment. No owner input is
needed to finish this handoff, and no background continuation is assumed.

**One-line resumption prompt:** Continue issue #28 / PR #29 on
`codex/phase13-rational-height`, proof checkpoint `aa446dad0c1e096ec82e44c5ae93f0fe93eff7ca`;
read this Resume here section and theory Sections 6–9, inspect live head/CI,
then investigate asymptotic odd-gcd cancellation and intermediate best
approximants. Preserve nonconvergence, the known-method attribution, 653-name
audit, 1,691 exact certificates, and the 347 / 347^2 cycle counterexamples.
Do not repeat the completed algorithm, claim a limit exists, remove gcds,
change paper/, merge the PR or close the issue without owner authorization.
