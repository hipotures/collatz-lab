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

Table 2 of the paper (Section 7.4, "Proof status") gives the status of
every result: written proof, Lean kernel check, cited theorem, or finite
computation. In short: the main theorem for the fixed point beginning
with `1` is written and kernel-checked; the other fixed point, the 2-adic
formulation, the irrationality measure (Theorem 5.5, Corollary 5.6) and
the literature-dependent statements of Section 6 are written or cited
only. Table and theorem numbers are those the source is expected to
produce; they have not been confirmed against a compiled PDF.
