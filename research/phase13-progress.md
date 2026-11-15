# Phase 13 research journal — issue #28

## Resume here

- Isolated clone: `/home/user/DEV/collatz-lab-phase13`.
- Branch: `codex/phase13-rational-height`, based on live origin/main
  `93647176a526eb8660b4dbf2ac428b0053117659` (checked 2026-11-15).
- Checkpoint A pushed normally:
  [`25eaf8e992108bf4bc3aeccfd4b020551951d2a7`](https://github.com/hipotures/collatz-lab/commit/25eaf8e992108bf4bc3aeccfd4b020551951d2a7).
- Checkpoint B pushed normally:
  [`282b3715c95c26bac1077fecd0df457bd277cb57`](https://github.com/hipotures/collatz-lab/commit/282b3715c95c26bac1077fecd0df457bd277cb57).
- Checkpoint C/D: ten families through 16,384 bits, 1,688 independently
  checked minimum certificates; written all-level substituted-shadow theorem
  proves nonconvergence. Exact constant B remains unresolved. Its pushed SHA
  is recorded at the next journal update.
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
- Next: complete the scoped Lean formalization, independent signatures and
  CI audit wiring; validate the full inherited matrix and clean build. The
  untracked `CollatzLab/RationalHeight.lean` already compiles locally but is
  not part of this data/report checkpoint. Do not mistake written all-level
  asymptotics for a kernel theorem. A reviewable PR must explain this boundary.
- Current CI expected audit count is 593, read from live CI. No Lean/source
  changes or proof checks at this documentation checkpoint. No remote branch
  CI is triggered by pushes under the present workflow (PRs trigger it).
- Issue #28 remains open. No PR until a reviewable conclusion of all gates;
  no merge, issue closure or publication is authorized.

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

Read the theory report Sections 5–7 before resuming analytical work. The exact
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
