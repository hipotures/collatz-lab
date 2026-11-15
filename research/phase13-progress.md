# Phase 13 research journal — issue #28

## Resume here

- Isolated clone: `/home/user/DEV/collatz-lab-phase13`.
- Branch: `codex/phase13-rational-height`, based on live origin/main
  `93647176a526eb8660b4dbf2ac428b0053117659` (checked 2026-11-15).
- Checkpoint A: source gate and independent mathematical definitions ready.
  Its exact commit SHA is `git log -1 --format=%H` when checking out this
  checkpoint; the next journal update records the pushed immutable SHA.
- Main checkout `/home/user/DEV/collatz-lab` and the manuscript worktree are
  untouched. No agents were spawned. Do not switch those checkouts.
- Gate 0 found direct prior coverage: Klapper–Goresky 1997 minimizes exactly
  our odd-denominator norm; Klapper 2007 gives accumulation set `[B,1-B]`.
  Candidate-specific B is still unresolved. No original theorem advertised.
- Read `phase13-prior-art.md` and `phase13-theory.md` first. Source cache and
  supplementary evidence: `/home/user/DEV/collatz-lab-phase13-evidence/`.
  Third-party texts are not committed; source hashes are reproducible metadata.
- Next obligation: implement **independent** floor-sum bounded-box search and
  adaptive odd-denominator lattice search, certify minimality, exhaust all
  small residues, and reproduce H_11=3 / H_12=513. Then pursue both analytic
  routes and a small Lean development. A preliminary known lemma is not the
  conclusion of this program.
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
