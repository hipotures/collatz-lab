# Manuscript

`main.tex` — *Equal-weight substitution words are not parity sequences of
rational 3x+1 trajectories: an elementary, formally verified proof.*

This is the Phase 9 manuscript (issue #15, Gates B and D). It is a draft
prepared for the repository owner's review. **It has not been submitted,
posted or announced anywhere.**

## What the paper claims, and what it does not

- The irrationality statement (Theorem 1.2) is **not presented as a new
  theorem**. It follows, in the stronger form of transcendence, from a 1983
  theorem of Molchanov on the *p*-adic Mahler method; the case
  `3^r < 2^L` also follows from Monks–Yazinski (2004). See Section 6 of the
  paper and `research/phase9-prior-art.md`.
- The contributions claimed are: an elementary proof using integer
  arithmetic and one linear form; a uniform certificate (degree six, order
  at least thirteen, no parity assumption on the leading remainder
  coefficient); an explicit 2-adic irrationality measure with exponent
  `2L/(2-theta)`, `theta = max(1, (r/L) log2 3)` (paper only, not
  formalized); and a Lean 4 formalization of the case in which the fixed
  point begins with `1`.
- Section 7.4 of the paper lists what is **not** formalized. Section 8
  lists limitations.

## Files

| File | Content |
|---|---|
| `main.tex` | the manuscript (`amsart`, standard packages only, ASCII source) |
| `references.bib` | bibliography; every entry checked against a primary record, with a note where an item was not read |
| `check_tex.py` | static consistency checker (not a TeX engine); also emits the Lean name check |

## Before circulating

1. **Author line.** `main.tex` defines `\paperauthor` as a placeholder.
   Replace it; no name, affiliation or e-mail address was inserted
   automatically.
2. **Compile it.** No TeX engine was available in the environment where
   the manuscript was written, so **the PDF has never been built**. The
   source passes the static checker below, which does not replace a
   compilation. Expect to fix overfull boxes in Table 1.
3. Read the "Acknowledgements and disclosure" paragraph and adapt it to
   the venue's policy on AI assistance.

## Build

With a TeX Live installation:

```text
cd paper
latexmk -pdf main.tex
```

or, by hand, `pdflatex main && bibtex main && pdflatex main && pdflatex main`.
With Tectonic: `tectonic paper/main.tex`.

Required packages: `amsart`, `amsmath`, `amssymb`, `amsthm`, `fontenc`,
`inputenc`, `booktabs`, `hyperref` (which loads `url`), and the
`amsplain` bibliography style.

## Checks that do run (also in CI)

```text
python3 paper/check_tex.py
python3 paper/check_tex.py --lean-names > /tmp/NameCheck.lean
lake env lean /tmp/NameCheck.lean
python3 research/phase9/verify_independent.py
```

- `check_tex.py`: balanced braces and environments, `$` parity per
  paragraph, every `\ref`/`\eqref` has a `\label`, every `\cite` key exists
  and every bibliography entry is cited, ASCII-only sources.
- The generated `NameCheck.lean` elaborates `#check` for each Lean
  declaration named in the paper (Table 1), so the table cannot refer to a
  declaration that does not exist.
- `verify_independent.py`: exact-arithmetic tests of the identities,
  examples and inequalities stated in the paper (finite tests; not part of
  any proof).

## Proof status of each statement

| Statement in the paper | Status |
|---|---|
| Lemmas 2.1–2.4, 3.1, 4.2–4.6, Corollary 4.4, Propositions 4.7, 4.8 | proved in the paper; formalized (integer form, start letter `1`) |
| Theorem 1.2 for the fixed point beginning with `1` | proved in the paper; formalized |
| Theorem 1.2 for a fixed point beginning with `0`; Remark 4.9 | proved in the paper only |
| Proposition 3.2, Theorem 3.4 (2-adic formulation) | proved in the paper only; the formal theorem is the seed form |
| Propositions 5.1, 5.2 | formalized; proof of 5.1 given in the paper, 5.2 stated with the formal constants |
| Remark 5.3 (Cramer bound) | paper only |
| Theorem 5.5, Corollary 5.6 (explicit irrationality measure, exponent `2L/(2-theta)`) | paper only; identities and bounds of Theorem 5.5(1) tested numerically (`verify_independent.py`, T9) |
| Proposition 6.1 | paper; depends on the cited theorem of Monks–Yazinski (statement and proof read) |
| Theorem 6.2 (Molchanov) | quoted; statement read in the original, proof read in outline only |
| Corollary 6.3 (transcendence) | deduction from Theorem 6.2 and two classical facts; not formalized |

Theorem and lemma numbers are those the current source is expected to
produce; they have not been confirmed against a compiled PDF.
