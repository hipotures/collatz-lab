# Phase 12 research journal — issue #24

## Resume here

- Issue: <https://github.com/hipotures/collatz-lab/issues/24>, open.
- Isolated clone: `/home/user/DEV/collatz-lab-phase12`.
- Branch: `codex/phase12-novelty-frontier`; base
  `47f34bdff38d876c394dc7326e457f686d112c13` (current `origin/main`).
- Initial checkpoint: this journal and the Gate 0 matrix; use `git log -1`
  for its SHA until the next journal update records the pushed checkpoint.
- Baseline CI independently observed: completed/success,
  [43633860186](https://github.com/hipotures/collatz-lab/actions/runs/43633860186).
  Baseline exact audit count: **564**, read from current CI.
- Required repository reading completed: issue and empty comments, AGENTS.md,
  Phase 9 prior-art report, Phase 10 unequal-weight report, corrected Phase 11
  findings, referee report §§1–3, 6–7, exact semantics, the six specified Lean
  modules and CI/audit interfaces. Original main and manuscript checkout are
  untouched. No other agents were started.
- Gate 0 finding under investigation: Allikvere §5's **density-sensitive**
  factor-complexity criterion may cover this candidate even though the
  worst-case Dubickas bound does not immediately do so. Check the elementary
  rational part independently, rather than assume the Subspace Theorem proof.
- Gate B falsification target: two matching prefixes of *any* binary word
  have finite rational witnesses. Their determinant congruence might therefore
  be automatic without infinite rationality; a small nonzero determinant
  premise would then be impossible for genuine returns.
- Next command: inspect the primary originals listed in
  `research/phase12-prior-art-matrix.md`; independently derive those two
  implications before implementing a major proof.
- No new exclusion or originality claim. No implementation validation yet.

## Initial state and research plan

The original checkout was clean on main at the base above. A fresh HTTPS
clone was created and the exact issue branch selected. Live remote refs
confirmed the base. Read-only inspection of the other existing checkouts did
not modify them. Gate 0 is bounded to one source-triage pass: inspect the
specified accessible originals and directly relevant leads, record proof
access limits, then choose a precise provable structural/no-go target.

The three planned deliverables are distinct: checked prior-art coverage;
faithful structural arithmetic for the literal candidate; and an independently
falsified two-return proposal. A known-method reduction is a useful negative
novelty result, not a reason to rename it a new exclusion.
