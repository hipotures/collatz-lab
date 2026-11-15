# Phase 13 research journal — issue #28

## Resume here

- Isolated clone: `/home/user/DEV/collatz-lab-phase13`.
- Branch: `codex/phase13-rational-height`, based on live origin/main
  `93647176a526eb8660b4dbf2ac428b0053117659` (checked 2026-11-15).
- Checkpoint A pushed normally:
  [`25eaf8e992108bf4bc3aeccfd4b020551951d2a7`](https://github.com/hipotures/collatz-lab/commit/25eaf8e992108bf4bc3aeccfd4b020551951d2a7).
- Checkpoint B: two independent exact engines and first 1,024-bit datasets.
  Its SHA is recorded in the next immutable journal update.
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
- Next: extend experiments, saving both sides of large jumps. The dense
  4,096-bit exploratory scan has systematic frontierSix jumps at
  N=12,68,404,2420, obeying `n_next=6*n-4`. Investigate substituted rational
  shadows from `100111...` (seed -3), and pursue finite drift lower bounds.
  Then formalize a selected meaningful subset in Lean. A preliminary known
  lemma is not the conclusion of this program.
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
