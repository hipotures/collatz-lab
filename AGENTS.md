# Agent Instructions — collatz-lab

These instructions apply to all automated contributors. Read the active GitHub issue and verify the current repository state before making changes. An issue's explicit branch and scope requirements override the default workflow below.

## 1. Git and collaboration

- **Default to `main` only for an exclusive, sequential task.** If the user or active issue assigns a feature branch or an isolated clone, use that exact target instead. Never move a concurrent agent's checkout between branches.
- Before editing, inspect `git status --short --branch`, `git log -1`, and the relevant remote refs. Fetch and fast-forward only when the working tree is clean and the target checkout is not being used by another agent.
- **Isolate concurrent agents:** each must have its own clone or explicitly authorized worktree. Do not share an active working directory, run competing Git operations, or clean up a workspace used by someone else.
- Respect the active issue's push destination. A feature-branch task must push to its assigned branch, **not to `main`**. An unmerged PR must remain unmerged until the user explicitly authorizes integration.
- Never discard unrelated changes, reset another agent's work, force-push, rewrite shared history, or silently resolve competing changes in favor of one agent.
- Commit and push small, independently validated milestones. Record exact commit SHA, branch, issue/PR URL, executed tests, failures, and open obligations.
- Before integrating concurrent branches, re-fetch, review changed paths, reconcile any overlapping Lean index / audit / CI files, and rerun the full relevant validation. A green feature-branch CI is not sufficient evidence that integration is safe.

## 2. Mathematical and semantic integrity

- Distinguish clearly among conjecture, heuristic, finite test, exact algebraic proof, Lean-kernel-verified proposition, and cited external theorem. Never promote one evidence level to another.
- The accelerated Collatz map and its rational 2-adic parity semantics are the source of truth. Keep the intended `RealizesWord`, `numStep`, `numIter`, and `seedParity` meanings unless a documented, independently validated correction is required.
- Audit **exact theorem statements**: hypotheses, quantifiers, denominators, signs, shift/tail semantics, and non-vacuity. Compilation alone establishes only the specified formal proposition, not its intended interpretation.
- Do not introduce `sorry`, `admit`, new unproved `axiom` / `opaque` assumptions, `unsafe`, `native_decide`, `implemented_by`, `extern`, or similar proof bypasses into trusted Lean arguments. Check `#print axioms` and the exact CI allowlist.
- If an attempted proof fails, identify the precise missing lemma, falsifying example, or mathematical blocker. Do not hide a gap by strengthening assumptions silently.
- Prefer finite exact integer arithmetic, transparent constructions, reproducible certificates, and independent adversarial checks. Numerical exploration and enumerations are supporting evidence, never proofs of universally quantified claims.
- **Scope matters:** the proven equal-weight theorems do not automatically cover unequal-weight substitutions, all automatic words, arbitrary 2-adic rational parity sequences, or the general Collatz / Periodicity Conjectures. Preserve known rational controls and counterexamples.

## 3. Prior art and scientific claims

- Treat originality as **unverified** until the hypotheses and conclusions have been compared against actual primary sources. Search the literature before asserting priority, novelty, or a stronger theorem.
- In particular, review the precise scope of Molchanov's 1983 p-adic Mahler result, Monks–Yazinski (2004), and López–Stoll (2021) before discussing the equal-weight result; document unresolved proof/source uncertainties rather than treating a citation as a verified lemma.
- Distinguish a new result from an independent proof of a known result, a new formalization, a quantitative refinement, or a computational certificate. Never call a theorem new just because a repository or recent article did not mention it.
- For third-party mathematical claims, give exact source details and explicitly mark whether the original theorem statement and proof were read and checked. Do not claim peer review, publication, or journal acceptance that has not occurred.
- Any correction to a mathematical claim must propagate consistently to dependent proofs, README, reports, issue status, and manuscripts.

## 4. Validation

Run the relevant commands before committing Lean/Rust changes; report actual outcomes, not expected ones:

```bash
lake build
lake env lean research/lean-audit/FamilyAudit.lean
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/phase8/verify_polynomial.py
python3 research/mahler-uncovered/verify_uncovered.py --check
```

- Pipe the Lean audit into `research/lean-audit/check_axioms.py --expected-count N`, using the **actual current exact count from CI** for `N`. Do not put a placeholder such as `<current-count>` into an executable shell command.
- Read the repository's current `.github/workflows/ci.yml` for additional required checkers; do not hardcode historical declaration counts or assume every optional tool exists in the environment.
- Add new public Lean declarations to the explicit audited-name list and update the exact expected count in lockstep with CI.
- For a release-quality theorem change, prefer a clean Lean rebuild and an independently constructed semantic regression test.
- Do not describe a local check or GitHub Actions job as passing unless its output was actually verified. Preserve deterministic evidence formats.

## 5. Manuscript and publication workflow

- Before changing `paper/`, read `paper/README.md`, `research/phase9-prior-art.md`, and the current manuscript. Keep mathematical claims and proof-status labels aligned with the Lean repository.
- The author name, affiliation, email and ORCID are the **human owner's decisions**. Do not infer, invent, or publish identity/contact details. Leave placeholders until the owner explicitly supplies approved values.
- AI systems are tools and should be acknowledged or disclosed according to the venue's rules, not added as human authors. The human author must approve the work, take responsibility for its content, and review the disclosure text.
- Before calling a PDF ready for external review, build `paper/main.tex` with a real TeX engine and bibliography processing. Also run `python3 paper/check_tex.py` and the generated Lean-name checks.
- Inspect all rendered pages for overflow, broken running heads, truncated formulas/tables, font or Unicode problems, references, author placeholders, and PDF metadata. Static syntax checks are not a substitute for a compiled, visually inspected PDF.
- Mark any result that is written only on paper, imported from another author, or verified only in a finite experiment; do not label it Lean-verified.
- Do not submit, post a preprint, contact a journal/referee, or otherwise publicize the manuscript without explicit approval from the owner.

## 6. Long-running tasks and resumption

- Read the active issue, the relevant `research/phase*-progress.md` journal, and the latest commits before starting or resuming. Continue from the last verified checkpoint instead of repeating completed work.
- Keep a concise factual `Resume here` section: branch and pushed SHA, achieved milestones, exact current proof obligation, evidence paths, failed approaches, and the next command/task.
- Push only compilable, independently useful checkpoints. Distinguish a partially proved lemma from completion of an issue; do not close issues based only on a token limit or an unreviewed PR.
- Do not assume agents continue running after a session ends; a pushed commit and readable checkpoint are the durable handoff.

## 7. Files, language, and reporting

- All created source files, comments, documentation, commits, research reports, and manuscripts must be written in **English**, unless the user explicitly requests another language.
- Keep source changes scoped to the active issue. Do not edit another concurrently active agent's files, PR, research report, or manuscript.
- Final reports must name the branch, pushed commit SHA/URL, issue or PR status, exact validated results, commands actually run, known limits, and any owner decisions still outstanding.
