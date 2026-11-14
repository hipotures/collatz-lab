# Phase 9 research journal — issue #15

Independent theorem audit, priority literature comparison and manuscript.
Work directly on `main`; no branches, worktrees, PRs or force pushes.

Starting HEAD (2026-11-14 UTC): `d6df8a2e498725e43adbc489f6e154d10225d399`.
Initial working tree clean; `git fetch origin` and `git pull --ff-only`
reported "Already up to date".

## Resume here

**State:** Gate 0 in progress. Nothing in the Lean or Rust code has been
changed in Phase 9 so far.

**Next actions, in order:**

1. Finish the Gate 0 source reading listed under "Outstanding checks" and
   write `research/phase9-prior-art.md` (claim-to-source matrix).
2. Gate A: read the Lean chain from `Word.lean` (`RealizesWord`) to
   `UniversalEqualWeight.lean` and write `research/phase9-referee-report.md`.
3. Gate B/D: write the independent proof and the manuscript in `paper/`.

**Highest-risk open issue:** whether a published *p*-adic Mahler-method
theorem (transcendence or irrationality of values of order-one Mahler
functions at rational points of a *p*-adic disc) already contains the
headline statement. See "Gate 0 working notes" below.

## Gate checklist

| Gate | Status |
|---|---|
| 0 — López–Stoll / prior-art red flag | in progress; preliminary reading complete, verdict not yet recorded as final |
| A — adversarial mathematical and Lean review | not started |
| B — independent proof reconstruction | not started |
| C — literature review and novelty verdict | not started (overlaps Gate 0) |
| D — manuscript | not started; blocked on 0, A, C |

## Environment (checked 2026-11-14)

- Lean toolchain file: `leanprover/lean4:v4.18.0`; `lake`, `lean` in `~/.elan/bin`.
- Rust toolchain in `~/.cargo/bin`.
- Python 3 with `pypdf`; no `sympy`.
- No TeX distribution found on `PATH` (`tex`, `pdflatex`, `xelatex`,
  `lualatex`, `tectonic`, `latexmk` all absent). A manuscript can be
  written but not compiled here unless a TeX engine is installed.
- Network access to arXiv and author pages works.

## Source inventory

"Read" means the theorem statement and its proof were read in the primary
source during Phase 9, not taken from a summary.

| Source | Version obtained | Status |
|---|---|---|
| J. López, P. Stoll, *The 3x+1 Periodicity Conjeture in R*, arXiv:2101.12747v1 (29 Jan 2021; arXiv lists only v1; 51 pp.) | arXiv TeX source and PDF | Read: Introduction I–II, Sections "Basic facts", "Auxiliary results", "Proof of Theorem 1", bibliography |
| K. G. Monks, J. Yazinski, *The autoconjugacy of the 3x+1 function*, Discrete Math. 275 (2004) 219–236 | author PDF `AutoConjV13.pdf` (14 pp.) | Read: Theorem 2.7, Lemmas 3.2, 3.4, 4.1–4.3 and the proof of Theorem 2.7 |
| J. López, P. Stoll, *The 3x+1 conjugacy map over a Sturmian word*, Integers 9 (2009) A13, 141–162 | journal PDF | Abstract and introduction read (text extraction is poor); it computes a 2-adic continued fraction and says its examples "suggest" aperiodicity; no rational-exclusion theorem located yet |

## Gate 0 working notes (preliminary; to be finalised in `phase9-prior-art.md`)

Notation: `alpha = log 2 / log 3`; for a parity word `v`, `h(l)` is the
number of ones among the first `l` symbols.

1. **Monks–Yazinski Theorem 2.7(b)** (source checked). For a rational
   2-adic integer whose orbit is infinite ("divergent" in their
   terminology means the orbit is not finite), `liminf h(l)/l >= alpha`.
   The proof (Lemmas 4.1–4.3) is elementary and I found no gap: positive
   orbits are compared with `x -> (3+1/m)x/2`, strictly negative orbits
   with `x -> 3x/2`, and mixed orbits become positive.
   **Consequence (mathematical deduction):** if `r/L < alpha`, i.e.
   `3^r < 2^L`, the equal-weight fixed point has density `r/L < alpha`,
   so no rational seed realises it or any shift of it. The *subcritical*
   half of the headline theorem is therefore a short corollary of a 2004
   theorem plus aperiodicity of the word.

2. **López–Stoll Theorem 1** (source checked). Statement: a rational
   2-adic integer with infinite orbit has `liminf h(l)/l = alpha`. The
   `<` direction is quoted from Monks–Yazinski. The `>` direction is
   their own and would cover the *supercritical* case `3^r > 2^L`.
   Their proof of the `>` direction shows that the **real** sum
   `Phi_R(v) = -sum 2^{d_i}/3^{i+1}` exists and that the real
   pseudo-orbit has an accumulation point, and then passes to the
   **2-adic** value `Phi(v)` through Section 2, equations labelled
   `IL`/`IL2`, where the 2-adic limit of the partial sums is described
   as "the 2-adic expansion" of the real limit. No argument is given
   that a rational 2-adic limit must equal the real limit. For a
   rational seed `zeta` with parity word `v` the exact identity
   `T^l(zeta) = (3^h/2^l)(zeta - Phi_R(u_l))` shows that
   `zeta != Phi_R(v)` is exactly the case of an orbit escaping to
   infinity at rate `3^h/2^l`, which the argument does not address. If
   the transfer were valid it would also show that no positive integer
   has a divergent orbit with `liminf h/l > alpha`, although then
   `Phi_R(v) < -1 < 0 < zeta`.
   **Preliminary assessment:** the supercritical half is *claimed* in
   this unrefereed preprint but its proof has a gap at the real/2-adic
   transfer; it cannot be cited as establishing the headline theorem.
   The same conclusion was reached independently in Phase 3
   (`infinite-itineraries.md` §2.2), which I read only after forming
   the assessment above.

3. **Mahler-method literature** (not yet checked in Phase 9). The seed
   is an affine function of the value at `2^L/3^r` of the generating
   function of the fixed point, which satisfies an order-one Mahler
   equation. A published *p*-adic transcendence or irrationality theorem
   for such values might contain the headline statement outright.

## Outstanding checks

- [ ] Publication status of arXiv:2101.12747 (journal version, later
      revision, citing or correcting papers).
- [ ] *p*-adic Mahler method: locate and read primary statements
      (candidates to verify, none yet confirmed: work of Loxton–van der
      Poorten, Nishioka, Becker, Bundschuh–Väänänen, T.-Q. Wang,
      Bugeaud–Yao, Adamczewski–Faverjon).
- [ ] Current state of the upstream project `msharpe248/collatz`
      (its `paper/rung1.tex` reportedly describes the equal-weight class
      as a programme).
- [ ] Bernstein–Lagarias 1996 and Lagarias 1985/1990 primary statements.
- [ ] Baseline re-verification on this checkout (Lean build, axiom
      audit, Rust, Python checkers).

## Checkpoint log

- 2026-11-14: journal created at `d6df8a2`; Gate 0 reading of
  López–Stoll and Monks–Yazinski done; preliminary notes above.
