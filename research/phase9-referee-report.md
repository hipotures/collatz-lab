# Phase 9 referee report (Gate A)

Subject: the universal equal-weight theorem of Phase 8,
`CollatzLab.no_rational_seed_realizes_all_equal_weight`, its tail
corollaries, and the supporting claims in `phase8-findings.md`.
Reviewed at commit `d6df8a2` (code) on 2026-11-14.

This is an adversarial review. It was written from the Lean sources and
from an independent derivation, not from the Phase 8 reports; where the
two agree this is stated as agreement, not as a premise.

## 1. Verdict

- **Correctness of the formal statement:** no defect found. The Lean
  proposition says what the project says it says (§3), it is proved
  from the three standard axioms only (§2), and an independent written
  derivation reproduces every exponent and constant in the argument
  (§5).
- **Critical findings:** none.
- **Major finding (framing, not correctness):** the mathematical
  statement is a corollary of a published 1983 theorem; see F1 and
  `phase9-prior-art.md`.
- **Minor findings:** F2 (start-letter restriction of the formal
  statement), F3 (meaning of "degree six"), F4 (an external fact needed
  to phrase the result with the conjugacy map), F5 (stale remarks in
  older memos).

A manuscript may proceed under the editorial gate of issue #15,
provided it is framed as in F1.

## 2. Trust base and reproduction

Run on a fresh clone (no `.lake` directory), Lean 4.18.0
(`leanprover/lean4:v4.18.0`, commit `11ccbced7964`), no dependencies
beyond the Lean core library (`lake-manifest.json` has an empty package
list; Mathlib is not used).

| Check | Command | Result |
|---|---|---|
| Build from scratch | `lake build` on a fresh clone | success, 55 jobs, 43 s wall |
| Axiom audit | `lake env lean research/lean-audit/FamilyAudit.lean \| python3 research/lean-audit/check_axioms.py --expected-count 306` | 306 declarations; axioms used are only `propext`, `Classical.choice`, `Quot.sound`; 63 declarations use none |
| Audit parser self-test | `python3 research/lean-audit/check_axioms.py --self-test` | 2 valid and 8 adversarial cases pass |
| Proof-escape scan | CI `grep` for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `extern` in `CollatzLab/` | no match |
| Metaprogramming scan | `grep` for `macro`, `elab`, `syntax`, `initialize`, `run_cmd`, `#eval`, attributes | one tactic macro (`family_ring` = `simp only [...]` then `omega`), `set_option maxRecDepth/maxHeartbeats` in check files, one `Decidable` instance in `SmallCertificates.lean`; nothing that can add an axiom or bypass the kernel |
| Rust | `cargo fmt --check`; `cargo clippy --locked --all-targets --all-features -- -D warnings`; `cargo test --locked --all-targets` | clean; no warnings; 94 tests pass (§7) |
| Phase 7/8 Python checkers | `python3 research/mahler-uncovered/verify_uncovered.py --check`; `python3 research/phase8/verify_polynomial.py` | both pass (§7) |
| Independent Phase 9 checker | `python3 research/phase9/verify_independent.py` | all pass (§6) |

`#print axioms` for the four headline theorems
(`no_rational_seed_realizes_all_equal_weight`, its shifted and
eventual-match forms, and the integer-seed form) each report exactly
`[propext, Classical.choice, Quot.sound]`. Since `#print axioms` is
transitive, this covers the whole dependency chain. No
`Lean.ofReduceBool` or `Lean.trustCompiler` appears, so every `decide`
is evaluated by the kernel.

What this establishes: the displayed Lean propositions are theorems of
Lean 4's type theory with those axioms, as checked by the Lean 4.18.0
kernel. It does not establish that the propositions mean what a reader
expects; that is §3.

## 3. Semantic audit of the statement

### 3.1 Rational seeds

```lean
def numStep (q p : Int) : Int := if p % 2 = 0 then p / 2 else (3 * p + q) / 2
def numIter (q p : Int) : Nat → Int | 0 => p | j + 1 => numStep q (numIter q p j)
def seedParity (q p : Int) (j : Nat) : Int := (numIter q p j) % 2
def RealizesWord (p q : Int) (v : Nat → Int) : Prop :=
  q > 0 ∧ q % 2 = 1 ∧ ∀ j : Nat, seedParity q p j = v j
```

- For odd `q`, the 2-adic parity of `p/q` is `p mod 2`, and
  `T(p/q) = (p/2)/q` or `((3p+q)/2)/q`. Both divisions are exact, so the
  rounding convention of integer division is irrelevant
  (`numStep_eq` proves `2 * numStep q p = p` resp. `= 3p+q`).
  Hence `numIter q p j / q = T^j(p/q)`.
- `Int` remainder by 2 takes values in `{0,1}` for negative arguments,
  so negative numerators are handled.
- No reducedness assumption: `numIter_equiv` proves that equivalent
  fractions with odd denominators have equal parities at every step.
  Denominators divisible by 3 are allowed.
- Every element of `Q ∩ Z_2` is `p/q` with `q > 0` odd, so the predicate
  ranges over all rational 2-adic integers. Rationals with even
  denominator are not 2-adic integers and are correctly outside the
  domain.
- The predicate is not vacuous: `UnequalControl.lean` proves
  `RealizesWord 1 1 (10)^∞`, and the check files exhibit finite-prefix
  realisations of the words under study.

Attempts to break it: `q = 3` (allowed, fine), `p = 0` (parity word
`0^∞`, periodic, irrelevant), `p = -1`, `q = 1` (word `1^∞`), unreduced
`p = 2, q = 2` (rejected by oddness, as it must be since the reduced
form is covered). No discrepancy with the 2-adic map.

### 3.2 The word

```lean
structure Images (L : Nat) where zero : Fin L → Bool; one : Fin L → Bool
def image M b j := if h : j < L then (if b then M.one ⟨j,h⟩ else M.zero ⟨j,h⟩) else false
def aux M : Nat → Nat → Bool | 0, _ => true | _+1, 0 => true | f+1, n => image M (aux M f (n / L)) (n % L)
def word M n := aux M n n
def parityWord M n : Int := if word M n then 1 else 0
```

For `L ≥ 2` and H1, `word_rec` gives
`word n = image (word (n / L)) (n % L)` for all `n`, `word 0 = true`,
and `word_unique` shows this is the only sequence starting with `1` and
satisfying the block rule. So `parityWord M` is the fixed point of the
substitution `0 ↦ M.zero`, `1 ↦ M.one` that starts with `1`.
`literal_block` states the block rule as an equality of lists.

Hypotheses of the theorem:

- H1 `image M true 0 = true`: the image of `1` starts with `1`.
- H2 `weight (image M false) L = weight (image M true) L`: equal number
  of ones.
- H3 `M.zero ≠ M.one`.
- `2 ≤ L`.

They are jointly satisfiable (144 instances for `2 ≤ L ≤ 5`, 574 for
`2 ≤ L ≤ 6` by independent enumeration; for `L = 2` the only instance is
Thue–Morse `10/01`). H2 and H3 imply `1 ≤ r ≤ L-1` for the common
weight `r` (`weight_positive`, `weight_lt_length`). No hypothesis
compares `2^L` with `3^r`.

### 3.3 Conclusions and quantifiers

- Main: `∀ p q : Int, ¬ RealizesWord p q (parityWord M)`.
- Shifts: `∀ t p q, ¬ RealizesWord p q (shiftWord (parityWord M) t)`
  with `shiftWord v t n = v (t + n)`. The proof descends through the
  actual inverse branches `x ↦ 2x` and `x ↦ (2x-1)/3`
  (`invBranchNum`, `invBranchDen`: `(2p, q)` and `(2p-q, 3q)`), which
  keep the denominator positive and odd.
- Eventual agreement: for all `s, t, p, q` with `q > 0` odd,
  `¬ ∀ j, seedParity q p (s+j) = parityWord M (t+j)`.

The quantifier order is the strong one (for every shift and every seed).
There is no truncation of the parity sequence anywhere.

## 4. Findings

### F1 — The statement is known (major for framing; no effect on correctness)

The seed of the word is an affine function, with nonzero rational
coefficients, of the 2-adic value at `2^L/3^r` of the generating
function `V` of the word, and `V` satisfies an order-one Mahler
equation. Transcendence of such values in `Q_p` at algebraic points
with `0 < |α|_p < 1` is a published theorem (Molchanov 1983; see
`phase9-prior-art.md` §3–4 for the statement, what was and was not
verified, and the line-by-line reduction). The subcritical half also
follows from Monks–Yazinski 2004. López–Stoll 2021 claim a statement
covering the supercritical half, with a gap in the proof.

Consequence: any text describing the irrationality statement as a new
theorem would be wrong. The Phase 8 documents make no such claim; the
manuscript must keep it that way. What can be claimed is in
`phase9-prior-art.md` §6.

### F2 — The formal statement fixes the starting letter (minor, scope)

H1 and the definition of `word` restrict the Lean theorem to the fixed
point that starts with `1`. If the image of `0` starts with `0`, the
substitution has a second fixed point starting with `0` (for example
the complement of the Thue–Morse word for `10/01`), which is in general
not a shift of the first one. The written proof applies verbatim to it:
only the block rule and the equal weights are used. The Lean theorem
does not cover it. The manuscript must state the formalised case
exactly and mark the other fixed point as proved on paper only.

Reproduce: there is no term of type
`¬ RealizesWord p q (complement of thueMorse word)` in the library.

### F3 — "Degree six" is a property of a crude estimate (minor, wording)

`MinimalCertificate.universal_certificate_degree_iff` is a correct
theorem about the predicate `UniversalCertificateDegree`, which
quantifies over pairs satisfying `PolynomialPair.Gap`. `Gap` uses the
height exponent `d(L-1)+L+e` obtained by bounding each tower step by
`2L · m^{(L+e)L^k}`; this discards the division by `a_k^s` in the
recursion and replaces `e-s` by `e` in the denominator. A sharper height
recurrence would give a different "minimum degree". The lower-bound
example (`L = 1000`) and the numerical example (`L = 101`,
`r = e = 100`) are worst cases for that estimate, not for the
irrationality problem: the same `L = 101` word has a degree-two
certificate. Phase 8 says this; the manuscript should present the
result as an optimality statement about one explicit inequality and
keep it out of the abstract's main claim.

### F4 — Phrasing with the conjugacy map needs an external fact (minor)

The Lean theorem is about seeds and parity sequences. The sentence
"`Φ(v)` is irrational" additionally uses the theorem of
Lagarias/Bernstein–Lagarias that every parity sequence is realised by
exactly one 2-adic integer. That bijection is not formalised here and
must be cited, or the result must be stated in the seed form.

### F5 — Stale statements in earlier memos (minor, documentation)

`infinite-itineraries.md` §2.3 describes the upstream `Rung1.lean` as
containing two `sorry` and misattributes the 4-uniform substitution;
`mahler-generalization.md` §10 already records the correction. The
latter also says that searches for *p*-adic Mahler results "returned
the general references"; Phase 9 located a specific source (F1). The
old memos are left unchanged as historical records; the Phase 9 files
supersede them.

## 5. The ten audit items of issue #15

Each item lists what was tried and the outcome. "Derivation" refers to
the independent proof written for the manuscript (`paper/main.tex`).

1. **Faithfulness of `RealizesWord`.** §3.1. No hidden restriction.
2. **Morphism semantics.** §3.2. Existence, uniqueness and the block
   rule are proved for `L ≥ 2` under H1 only. Non-eventual periodicity
   (`Morphism.not_eventually_periodic`) uses H1–H3; my derivation
   proves it by a different route (the least eventual period is coprime
   to `L`, then prefix weights of the two images agree at every length)
   and agrees. Zero/one convention: `true ↦ 1`. Not vacuous.
3. **Integer kernel vector.** `FiniteLinear.integer_null_vector`:
   `∀ m, ∀ A : Nat → Nat → Int, ∃ x, (∃ j < m+1, x j ≠ 0) ∧ ∀ i < m, dot (A i) x (m+1) = 0`.
   No rank or nonvanishing hypothesis; `m = 0` returns `x = 1`. The
   statement is the standard fact that `m` homogeneous equations in
   `m+1` unknowns over `Z` have a nonzero solution. Independent check:
   rational elimination on every instance tested in §6.
4. **Polynomial pair.** `polynomial_pair_exists d v` holds for every
   integer sequence `v` and every `d`: `P.degree = d`, some
   `P.p1 j ≠ 0` with `j ≤ d`, residual zero below `2d+1`. `degree` is an
   upper bound for the degree; the top coefficient may vanish and a
   common power of `z` is allowed, which the later argument tolerates.
   `residual` is the coefficient of `z^n` in `P0 + P1·V` (only indices
   `≤ degree` of `p0, p1` are read).
5. **Rational series ⇒ eventually periodic.**
   `rational_binary_eventually_periodic` needs only binary symbols, a
   nonzero `p1` and vanishing residuals. The proof pivots on the first
   nonzero coefficient of `p1`, so leading zeros are handled; the
   determination step is an equality `c·x = c·y` with `c ≠ 0`, no
   division. Negative coefficients are unrestricted.
6. **Tower in integer arithmetic.** With `a_k = 2^{L^{k+1}}`,
   `b_k = 3^{rL^k}`: `D_{k+1} = D_k · Γ*(a_k,b_k) · (b_k^L - a_k^L)`,
   `u_{k+1} = b_k^e · δ_k / a_k^s`, `δ_k = (b_k^L - a_k^L) u_k - D_k b_k Q_0(a_k,b_k)`.
   My derivation obtains the same recursion from
   `V(z) = p_0(z)/(1-z^L) + Γ(z) V(z^L)` and `Γ(z) = a^s Γ*(a,b)/b^e`.
   Signs: `b^L - a^L` and `B - A` may be negative; the height uses
   absolute values and oddness of `D_k` gives `D_k ≠ 0` in both
   regimes. Exact divisibility by `a_k^s` is proved from congruences,
   not assumed. No real-variable series appears anywhere in the Lean
   chain.
7. **Non-unit leading coefficient.** `PolynomialPair.valuation` assumes
   `R_N = 2^v · c` with `c` odd and `v < L^{k+1}` and proves the exact
   valuation `N·L^{k+1} + v`. The main proof factors `R_N`
   (`int_two_power_factorization`), chooses `k_0` with `v < L^{k+1}` for
   `k ≥ k_0`, and uses only those levels. The Thue–Morse degree-six
   pair has `R_13` of valuation 3 (confirmed independently in §6).
8. **Height recurrence and closing inequality.**
   `H_{k+1} ≤ 2L · m^{(L+e)L^k} · H_k` and
   `|E_k| ≤ (d+1)‖P‖ · m^{dL^k} · H_k` give
   `|E_k|^{L-1} ≤ K · (2L)^{(L-1)k} · m^{(d(L-1)+L+e)L^k}`; with
   `2^{N L^{k+1}} ≤ |E_k|` this contradicts `Gap`. The final step
   `no_eventual_doubly_exponential_bound` is a statement about integers.
   My derivation gives the same exponent `d(L-1)+L+e`.
9. **Minimum degree six.** F3. The Lean statement is correct and
   interface-specific.
10. **Tail corollaries.** §3.3.

## 6. Independent experiments

`research/phase9/verify_independent.py` (new in Phase 9; exact integer
and rational arithmetic; shares no code with earlier checkers; about 13
seconds):

- all 144 admissible substitutions with `2 ≤ L ≤ 5`: Bernstein's series
  for the seed modulo `2^900` equals the block formula and reproduces
  60 parities; the factored Mahler recursion holds modulo `2^900` at
  three tower levels; a degree-six pair found by rational elimination
  has residual order `N ≥ 13` (largest observed: 30) and satisfies the
  strict gap; the 2-adic valuation of `P_0(z_k)+P_1(z_k)V(z_k)` equals
  `N L^{k+1} + v_2(R_N)` whenever `L^{k+1} > v_2(R_N)`; no eventual
  period `≤ 120` from index 60 in the first 1500 symbols;
- Thue–Morse: `N = 13`, leading valuation 3;
- the worst-case ledger closes for degree six for `2 ≤ L ≤ 400` and
  first fails for degrees `0,…,5` at `L = 2, 2, 2, 7, 16, 101`;
- the unequal-weight control `101/010` is periodic and realised by the
  seed 1.

A separate scratch run checked the seed identity on all 574 admissible
substitutions with `2 ≤ L ≤ 6`.

These are finite checks. They found no discrepancy and they are not
part of any proof.

## 7. Baseline validation results

Run on the fresh clone at the reviewed commit, 2026-11-14:

- `cargo fmt --check`: clean.
- `cargo clippy --locked --all-targets --all-features -- -D warnings`:
  no warnings.
- `cargo test --locked --all-targets`: 94 tests passed, 0 failed.
- `python3 research/mahler-uncovered/verify_uncovered.py --check`:
  "48 exact Pade rows; 8 checkpoints; 32800 signed candidates; 144
  control certificates; all checks passed".
- `python3 research/phase8/verify_polynomial.py`: passes (686 exact
  convolution identities; coefficient-8 valuations `[29, 55]`;
  coefficient-24 premature valuation 68 instead of 66).
- Lean build, audit and scans: §2.

These reproduce the Phase 8 figures (306 audited declarations, 94 Rust
tests).

## 8. Remaining uncertainties

- Molchanov's proof was read in outline only; F1 depends on the
  correctness of a published theorem that I did not verify line by
  line. The Lean result does not depend on it.
- Wang (2006), Wang–Xu (2006) and Loxton–van der Poorten (1982) were not
  obtained.
- The review is by a single reviewer in a single session. It is
  independent of the Phase 8 report but not of the Lean kernel: a kernel
  bug or a compromised toolchain would not be detected.
- The written proof in the manuscript has been checked against the Lean
  statements for exponents and constants, and numerically at small
  parameters; it has not been refereed by a human.
