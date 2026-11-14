# Phase 9 research journal — issue #15

Independent theorem audit, priority literature comparison and manuscript.
Work directly on `main`; no branches, worktrees, PRs or force pushes.

Starting HEAD (2026-11-14 UTC): `d6df8a2e498725e43adbc489f6e154d10225d399`.
Initial working tree clean; `git fetch origin` and `git pull --ff-only`
reported "Already up to date".

## Resume here

**State:** all five gates have a written deliverable. Gates 0, A, C:
`phase9-prior-art.md`, `phase9-referee-report.md`. Gates B, D:
`paper/main.tex` (complete written proof and manuscript),
`paper/references.bib`, `paper/README.md`, `paper/check_tex.py`.
No Lean or Rust source has been changed in Phase 9. CI gained three
steps (independent checker, manuscript static check, Lean name check).

**Gate 0 verdict** (`phase9-prior-art.md` §0): the headline irrationality
statement is **not new** — it follows from S. M. Molchanov's 1983 *p*-adic
Mahler theorem, which even gives transcendence. López–Stoll Theorem 1
has a gap (real limit identified with 2-adic limit). The subcritical
half is a short corollary of Monks–Yazinski 2.7(b).

**Gate A verdict** (`phase9-referee-report.md` §1): no correctness
defect; findings F1 (framing), F2 (formal statement covers only the
fixed point starting with `1`), F3 (degree six is interface-specific),
F4 (conjugacy-map phrasing needs a cited bijection), F5 (stale memos).

**Framing used in the paper:** elementary, integer-arithmetic,
machine-checked proof of a known consequence of the *p*-adic Mahler
method, with an explicit uniform certificate. No "new theorem" claim.

**What is still open (in order of value):**

1. **The PDF has never been built.** No TeX engine is installed, and an
   attempt to download a standalone engine into the scratch directory
   was refused by the session's permission policy. `paper/check_tex.py`
   is a static substitute only. First action for anyone with TeX:
   `cd paper && latexmk -pdf main.tex`, fix what it reports.
2. The author line in `paper/main.tex` is a placeholder (`\paperauthor`).
3. Finding F2: the Lean theorem covers the fixed point beginning with
   `1`; the paper proves the other fixed point on paper only. A Lean
   generalisation is optional work.
4. Sources not obtained: Wang 2006, Wang–Xu 2006, Loxton–van der
   Poorten 1982, full text of Dejesus 2026. Molchanov's proof was read
   in outline only.
5. Issue #15 must stay open until the owner has reviewed the manuscript;
   no submission or publicity.

**Highest-risk open issue:** the manuscript's written proofs have had no
independent human reader, and the "known" verdict rests on the published
statement of Molchanov's theorem.

**Working-copy note.** At 10:50:45 UTC a concurrent Codex session
switched the shared checkout `/home/user/DEV/collatz-lab` to its own
branch `codex/unequal-weight-contraction`. One Phase 9 commit landed on
that branch by accident; it was re-applied to `main` (`2ee7681`) and
removed from that branch with a compare-and-swap ref update, leaving
the other session's branch and files as they were. Since then Phase 9
commits are made from a separate plain clone of `origin` on `main`
(no branch, worktree or PR). When resuming, check
`git rev-parse --abbrev-ref HEAD` before committing.

## Gate checklist

| Gate | Status |
|---|---|
| 0 — López–Stoll / prior-art red flag | **resolved**: `phase9-prior-art.md` §0 |
| A — adversarial mathematical and Lean review | **complete**: `phase9-referee-report.md` |
| B — independent proof reconstruction | **written**: `paper/main.tex` §§2–4 (2-adic presentation; exponents agree with the Lean integer proof); numerically cross-checked by `research/phase9/verify_independent.py` |
| C — literature review and novelty verdict | **written**: `phase9-prior-art.md` §§5a–7; open items in its §7 |
| D — manuscript | **written, not compiled**: `paper/`; static checks pass |

## CI record

| Commit | Content | Run |
|---|---|---|
| `d2a71fa` | journal started | <https://github.com/hipotures/collatz-lab/actions/runs/43587089247> success |
| `2ee7681` | Gate 0 | <https://github.com/hipotures/collatz-lab/actions/runs/43587705634> success |
| `da4f5b0` | Gate A | <https://github.com/hipotures/collatz-lab/actions/runs/43589026117> success |

## Environment (checked 2026-11-14)

- Lean toolchain file: `leanprover/lean4:v4.18.0`; `lake`, `lean` in `~/.elan/bin`.
- Rust toolchain in `~/.cargo/bin`.
- Python 3 with `pypdf`; no `sympy`.
- No TeX distribution found on `PATH` (`tex`, `pdflatex`, `xelatex`,
  `lualatex`, `tectonic`, `latexmk` all absent). A manuscript can be
  written but not compiled here unless a TeX engine is installed.
- Network access to arXiv and author pages works. Crossref API works
  (used to verify every bibliography entry). SSRN and Springer refuse
  automated access; zbMATH Open API returned a proxy error.
- Downloading a standalone TeX engine (Tectonic) into the scratch
  directory was refused by the session's permission policy; not retried.

## Source inventory

"Read" means the theorem statement and its proof were read in the primary
source during Phase 9, not taken from a summary.

| Source | Version obtained | Status |
|---|---|---|
| J. López, P. Stoll, *The 3x+1 Periodicity Conjeture in R*, arXiv:2101.12747v1 (29 Jan 2021; arXiv lists only v1; 51 pp.) | arXiv TeX source and PDF | Read: Introduction I–II, Sections "Basic facts", "Auxiliary results", "Proof of Theorem 1", bibliography |
| K. G. Monks, J. Yazinski, *The autoconjugacy of the 3x+1 function*, Discrete Math. 275 (2004) 219–236 | author PDF `AutoConjV13.pdf` (14 pp.) | Read: Theorem 2.7, Lemmas 3.2, 3.4, 4.1–4.3 and the proof of Theorem 2.7 |
| J. López, P. Stoll, *The 3x+1 conjugacy map over a Sturmian word*, Integers 9 (2009) A13, 141–162 | journal PDF | Abstract and introduction read (text extraction is poor); it computes a 2-adic continued fraction and says its examples "suggest" aperiodicity; no rational-exclusion theorem located |
| S. M. Molchanov, Vestnik Moskov. Univ. Ser. I Mat. Mekh. 1983, no. 2, 31–37 (Russian) | Math-Net.Ru scan (`vmumm3467`) | Read: theorem statement from page images; proof in outline |
| Y. Bugeaud, J.-Y. Yao, Ann. Mat. Pura Appl. 196 (2017) 929–946 | author PDF `p-adic18.pdf` | Read: introduction, Theorem 3.1 and the first part of its proof, bibliography |
| D. J. Bernstein, J. C. Lagarias, *The 3x+1 conjugacy map*, Canad. J. Math. 48 (1996) 1154–1169 | Lagarias's PDF (dated 1996-02-15) | Read: introduction, formulas (1.5)–(1.6), statement that `Phi` preserves `Q ∩ Z_2` |
| `msharpe248/collatz` | commit `ec8174b5` (2026-09-06), still default-branch head | Read: `paper/rung1.tex` introduction, §"Relation to Mahler's method", bibliography |
| T. Q. Wang (2006); T.-Q. Wang, G.-S. Xu (2006) | — | **Not obtained** (login/captcha); known only through Bugeaud–Yao's citation |
| E. Dejesus, *Transcendence of the 3x+1 conjugacy map on Sturmian words*, SSRN preprint, DOI 10.2139/ssrn.7584439 (2026) | Crossref record only | Abstract read; full text **not obtained** |
| O. Rozier, arXiv:1805.00133; J. Yazinski, arXiv:1102.5547 | arXiv abstract pages | Abstracts read; not relevant to the rational-exclusion statement |
| Bibliographic metadata of all 20 entries of `paper/references.bib` | Crossref / arXiv / Math-Net.Ru records | Checked 2026-11-14; entries not read are marked in the `note` field |

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

- [x] Publication status of arXiv:2101.12747: arXiv API lists v1 only,
      no journal reference (2026-11-14).
- [x] *p*-adic Mahler method: Molchanov 1983 located and read.
- [x] Upstream project state: unchanged since `ec8174b5`.
- [x] Bernstein–Lagarias 1996 formula checked.
- [x] Numerical check of the seed identity used in the prior-art
      derivation: 574 admissible morphisms with `2 <= L <= 6`, modulus
      `2^200`, first 40 parities (scratch script, not committed).
- [ ] Wang 2006, Wang–Xu 2006, Loxton–van der Poorten 1982 statements.
- [x] Baseline re-verification on a fresh clone: Lean build, 306-entry
      axiom audit, proof-escape scan, `cargo fmt/clippy/test` (94 tests),
      both Python checkers — all pass (referee report §2, §7).

## Checkpoint log

- 2026-11-14: journal created at `d6df8a2`; Gate 0 reading of
  López–Stoll and Monks–Yazinski done; preliminary notes above.
- 2026-11-14: Gate 0 resolved; `phase9-prior-art.md` written.
- 2026-11-14: Gate A complete; `phase9-referee-report.md` and
  `research/phase9/verify_independent.py` added.
- 2026-11-14: Gates B and D written: `paper/` (manuscript, verified
  bibliography, README, static checker); `verify_independent.py`
  extended with T7 (lower-bound example) and T8 (explicit Thue–Morse
  pair); CI extended; second Gate C pass recorded one adjacent preprint
  (Dejesus 2026, abstract only).
