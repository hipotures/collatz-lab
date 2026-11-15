# Phase 13 independent referee journal — issue #31

## Resume here

- Task: <https://github.com/hipotures/collatz-lab/issues/31>. No issue may be
  closed and neither implementation branch nor `paper/` may be changed.
- Reviewer clone: `/home/user/DEV/collatz-lab-phase13-referee`, initially
  checked out at pinned PR #29 head on `review/phase13-independent-referee`.
- Pinned implementation: `65b087dc62e4950e1c504fe34865acaacb9188c9`;
  base: `93647176a526eb8660b4dbf2ac428b0053117659`;
  overnight: `76bf6136c334c1db9e52e399fcc33fd4c20b9c24`.
  All live refs matched at startup. PR #29 is open/unmerged; issues #28/30/31
  are open. CI run 43663195328 at the pinned PR head was read as success.
- **Review complete.** Separate [review PR #32](https://github.com/hipotures/collatz-lab/pull/32)
  is open and unmerged against unchanged main, with only 11 new research files.
  Mathematical/source review and final fresh reproduction are complete.
  Main theorem verdict **PASS**;
  see report section 13 for separate provenance/priority/integration decisions.
  A new empty build directory successfully rebuilt all 87 Lean targets.
  `bash research/phase13/validate.sh` completed, exit 0: 94 Rust tests,
  all inherited/current CI checks, 653 audited records, 1,691 certificates.
  Logs and downloaded originals are in the separate
  `/home/user/DEV/collatz-lab-phase13-referee-evidence/` directory.
- Independent proof route completed in the checkpoint draft report: signed
  inverse branches, expanded one-position sum, all-prefix pressure and
  determinant separation. Both subsequence bounds, all-N interpolation,
  all-k exact minima, modular cycles and finite-state distinctness check out.
  The source matrix, all-k/conditional refinements and final verdict table
  are now complete. No blocking central mathematical defect was found.
- Independent certificate route completed: validate lattice index
  and membership, bound **both** Cramer coefficients, enumerate the shorter
  signed coefficient range and solve the other coordinate interval with
  `1 <= q <= H-1` and odd q. Ignore producer exclusion transcripts when
  proving minimality. This differs from replaying their optimizer or their
  positive-beta symmetric-box transcript. All 24 overnight records have
  shorter coefficient cap 0 or 1. Two complete runs passed; final run
  195.854 seconds. Every one of the 1,691 baseline minima, 24 overnight
  minima, 16 transitions and raw gcds k=0..8 independently checks. Exact
  compact results are committed in `phase13/referee/independent-results.json`.
- All 60 exact Lean interfaces were read and assessed in report section 9.
  Exact source headers and foundation lists are in `lean-statements.json`;
  separate `Declarations.lean` and signed `Signatures.lean` compile, exit 0.
  The full pipefail axiom pipeline passes at 653; an independent parser
  also checks the exact order, dependencies and 85-file escape scan.
- Overnight files were extracted read-only from the pinned Git object into
  the evidence directory, not read from the author's mutable checkout.
  The actual files have 24 heights and 16 transitions. `overnight-summary.md`
  **and checkpoint-audit.json** are stale at 23/15; their old hashes and smoke
  description must not be treated as final-head evidence. The actual final
  smoke log says 24/16, exit 0, 464.54 seconds, peak 102,832 KiB. This is a
  provenance defect, not a failure of the independently checked certificates.
  Exact heights are stored integers; 35,217/51,875/
  211,281/311,267 describe bit lengths.
- Fresh downloads match the pinned hashes for Klapper–Goresky, Klapper,
  Bernstein–Lagarias, Allikvere, Cassidy, Dubickas, De Jesús, de Weger, WGD
  and Monks–Yazinski. The local Bernstein 1994 original was independently
  hashed. Newly obtained Chen–Winterhof arXiv:2504.09933v1 fills an author's
  source-access gap. Its Theorem 1 and proof have now been read, as have
  the Klapper/Klapper–Goresky originals, Allikvere's density-height proof,
  Cassidy G/R, De Jesús's finite lemmas and Dubickas's counting proof.
  Fresh maximum-order arXiv:2309.12769v1 was obtained and its theorem read.
  Fifteen exact primary versions and actual read scopes are recorded in
  `phase13/referee/source-provenance.json`. Molchanov full text remains
  unavailable and is not used. Cassidy's literal signed-b gap formula has
  counterexample (-1,1/3); Chen–Winterhof's unqualified Roth sentence needs
  algebraicity, with an independent Liouville counterexample. These do not
  invalidate the scoped Phase 13 proof or their corrected useful mechanisms.
- **No remaining issue #31 review obligation.** Owner decisions are whether
  to consider PR #29 alone as scoped research/formalization, and whether to
  authorize a separate overnight-provenance repair. Do not merge, publish or
  close an issue. A changed implementation head needs a new incremental audit.
  Check PR #32's current CI before any later integration proposal; its ordinary
  CI tests main's baseline and does not replace the pinned-source reproduction.
  The clean whole
  reproduction in `/tmp/collatz-phase13-final-reproduction-2` completed,
  **exit 0**, including both bytewise JSON comparisons. `reproduce-canonical.log`
  and `phase13/referee/validation.json` preserve its results/hashes. Do not
  repeat completed large computations without a new failure or source change.
- Checkout isolation was completed before the first push: preserve a detached,
  pinned source checkout for reproduction, then transplant only new
  referee-owned commits onto unchanged base main locally. This reconciles
  the issue's required initial PR-head checkout with its required reviewer PR
  containing only new files relative to main. Never rewrite a pushed branch
  or move either implementation branch. Final standalone checker will accept
  an explicit pinned `--source` path. Record the first pushed SHA here in the
  next checkpoint. This local transplant was performed before publication;
  only new referee-owned files differ from main. The detached pinned source
  clone is `/home/user/DEV/collatz-lab-phase13-referee-source`.
- **First pushed checkpoint:**
  [`b5ece650e78eaef81c8cd70c81bd618745cfb7a6`](https://github.com/hipotures/collatz-lab/commit/b5ece650e78eaef81c8cd70c81bd618745cfb7a6).
  Remote branch was read back; no pushed history was rewritten.
- **Second pushed checkpoint:**
  [`3d828cfcd8b40ff480a03ef5e111c54811f485f3`](https://github.com/hipotures/collatz-lab/commit/3d828cfcd8b40ff480a03ef5e111c54811f485f3),
  primary-source matrix, explicit verdicts and source/provenance findings.
- **Canonical checker checkpoint:**
  [`deac930476c000b8aa8bfb1bb27201dcbcabcafc`](https://github.com/hipotures/collatz-lab/commit/deac930476c000b8aa8bfb1bb27201dcbcabcafc).
  The final fresh whole reproduction validated this exact code and fixtures.
- **Final validated report/evidence checkpoint:**
  [`4002044218b64f819feb4a9679a4c8555bb42ed7`](https://github.com/hipotures/collatz-lab/commit/4002044218b64f819feb4a9679a4c8555bb42ed7).
  Pushed and used to open PR #32. A final journal-only handoff follows;
  `git log -1 --format=%H` / PR #32 identify that delivery commit.

## Startup and actual failures

Read issue #31, #28, #30, root AGENTS.md, CI, PR metadata and the required
Phase 13 reports/interfaces and prior referee report. The ordinary checkout
remains untouched. No sub-agents were spawned.

- SSH fetch in the new clone initially failed (`Permission denied
  (publickey)`, exit 128). Public HTTPS fetch succeeded; this is an access
  configuration failure, not a mathematical or test failure. Reuse the
  existing repository's SSH command safely for an authorized reviewer push.
- An exploratory baseline JSON read hit Python's default 4,300-decimal-digit
  limit (exit 1). Repeating with a finite 20,000-digit limit succeeded. New
  large evidence uses hexadecimal; no numerical truncation was accepted.
- Independent literal early shadows give raw `(-9,3)` at k=0, hence reduced
  `(-3,1)`, and `(-297087259,81310473)` at k=1. The strict bound with the
  **actual reduced height** holds at both levels; the coarser T bound does
  not, so the all-k minima proof must keep its separate early checks.
- The first reviewer Lean fixture used reserved token `prefix` as a local
  hypothesis name and failed parsing, exit 1. Renaming it `hprefix` fixed
  the fixture; the final independent fixture compiles without stronger
  hypotheses or a proof escape.

## First validated milestone

The report contains the full independent main proof, exact-subsequence and
modular proofs, all 60 declaration assessments, finite-state route and
certificate/provenance audit. The first checkpoint left the primary-source
table and final decision pending; those are now added in the next checkpoint.
This was a durable intermediate checkpoint, not completion
of issue #31. Validation commands, verified exit codes and output hashes
are in `phase13/referee/validation.json`. The reproduction script requires a
new directory and clones the pinned implementation separately, so the final
review PR can contain only new research files against main.

## Final source gate and environment failure

The fresh `reproduce.sh` attempt in
`/home/user/DEV/collatz-lab-phase13-referee-reproduction` rebuilt Lean cleanly
and passed clippy, but `cargo test` compilation failed with **exit 101**:
`No space left on device (os error 28)`. The 9.8 GiB home filesystem was
full. This does not supersede the earlier passing complete matrix, and this
fresh attempt is not called PASS. Logs are preserved in the reproduction
directory and `phase13-referee-evidence/reproduce.log`.

Only the disposable Rust `target/` directories generated by this review
were removed: 598 MiB from the reviewer clone and 202 MiB from the failed
reproduction. No preexisting checkout or evidence was cleaned. The final
fresh reproduction uses the available `/tmp` filesystem; no host setting
or dependency was changed. Its completion remains to be read before handoff.

Live refs were read back unchanged after the source gate, and PR #29 still
has exact pinned head and is open/unmerged. CI run 43663195328 was read
in detail: both `lean` and `check`, with every listed step, succeeded.
Actual tools: Lean 4.18.0 (commit 11ccbced7964), rustc 1.100.0
(0ef1bc386, 2026-11-09), Python 3.14.4.

## Deterministic-output correction and final reproduction

The first `/tmp` fresh reproduction passed the entire clean Lean/Rust/Python
matrix and the independent full mathematical checks (193.758 seconds), then
exited **1** at bytewise JSON comparison. The discrepancy was only key order
in the modular-state metadata: integer dictionary keys sorted numerically,
whereas reloading and re-saving the fixture had sorted string keys lexically.
Parsed JSON values were checked equal before any correction.

The reviewer checker now converts state-level keys to strings explicitly.
A complete JSON round-trip comparison verifies that the new canonical
serializer produces exactly the committed fixture, without changing any
mathematical data. Self-tests and cycle identities pass. The report also
adds short written arithmetic proofs of the strict uniqueness base and the
two small exact minima. No implementation fix was made or required.

The final whole reproduction completed in
`/tmp/collatz-phase13-final-reproduction-2`; log:
`/home/user/DEV/collatz-lab-phase13-referee-evidence/reproduce-canonical.log`.
It passed **exit 0**, with byte-identical statement and independent-result
JSON. The full arithmetic stage took 193.793 seconds. No computation remains
running and no mathematical proof/source/certificate obligation remains.
The separate reviewer PR was then opened and read back open/unmerged.
Its remote changed-file list agrees exactly with the 11 added local paths;
no implementation, CI, existing research or paper file is changed.

## Completed review handoff

- [PR #32](https://github.com/hipotures/collatz-lab/pull/32), branch
  `review/phase13-independent-referee`, is the reviewer-only deliverable.
- Scientific verdict: the written nonconvergence theorem and the exact scoped
  finite statements **PASS**. Neither analytic limits nor modular infinite
  deductions are mislabeled as separate Lean theorems.
- Adverse finding: supplementary `overnight-summary.md` and
  `checkpoint-audit.json` fail as final-head provenance (23/15 versus 24/16).
  The mathematical certificates themselves pass independent verification.
- Historical-method attribution passes; exact priority remains unverified.
  Publication is not ready. The corrected-source sign/algebraicity limits
  and all genuine access limitations are in report section 11.
- The final clean reproduction passed in full, exit 0, with two byte-identical
  JSON outputs. The validation manifest preserves exact hashes, 94 passing
  Rust tests, 653-record audit, all 1,691/24 minima, 16 transitions and gcds
  k=0..8, plus failed attempts and their resolutions.
- No background work remains, no other agents were used, no PR was merged,
  and issues #28/#30/#31 remain open. Exact B and asymptotic gcd cancellation
  are original research questions, not uncompleted referee obligations.
- Resume only if the owner requests an incremental source review, an
  overnight metadata repair, or an explicit integration/publication action.
  The complete evidence and reports are pushed; no active process is needed.
