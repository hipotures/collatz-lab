# Phase 9 prior-art report (Gates 0 and C)

Scope: the Phase 8 *universal equal-weight theorem*
(`CollatzLab.no_rational_seed_realizes_all_equal_weight` and its tail
corollaries). All sources below were consulted on 2026-11-14 (UTC).
Evidence labels used throughout:

- **source checked** — I read the statement (and, where said, the proof)
  in the primary source during Phase 9;
- **mathematical deduction** — my own argument from checked statements;
- **plausible** — expected to be true, not verified in a primary source;
- **unresolved** — could not be decided with the sources available.

Nothing here is a claim of priority. "I did not find it" is recorded as
exactly that.

## 0. Summary verdict

1. **The headline irrationality statement is not new mathematics.** It is
   a corollary of the *p*-adic form of Mahler's method. The earliest
   primary statement I located and read is S. M. Molchanov's 1983
   theorem (§3). With Bernstein's series for the conjugacy map and a
   one-line block computation it gives more than the Lean theorem: the
   2-adic seed of every equal-weight substitution word is
   **transcendental**, not merely irrational (§4). Status of this
   implication: *mathematical deduction from a source-checked statement;
   the 1983 proof itself was read in outline only.*
2. **López–Stoll Theorem 1 does not establish the theorem.** Its
   statement would imply the supercritical half, but the proof contains
   a gap at the passage from a real limit to a 2-adic limit (§2). It
   should be cited as a claim with a defective proof, not as a theorem
   we rely on, and not as a result we "reprove".
3. **The subcritical half (`3^r < 2^L`) is a two-line corollary of
   Monks–Yazinski (2004), Theorem 2.7(b)** (§1). This part of the proposed
   "frequency corollary" in issue #15 is sound.
4. Relation in the terms of issue #15: for the López–Stoll route the
   answer is **(b)** — partial overlap: valid for `3^r < 2^L` through
   Monks–Yazinski alone; not valid for `3^r > 2^L` because the only
   source for that direction has an unproved step. Independently of that
   route the answer is **(a)** — a prior theorem (Molchanov 1983) implies
   the full statement.
5. **Publication framing that the evidence supports:** an elementary,
   self-contained, division-free and machine-checked proof of a known
   consequence of the *p*-adic Mahler method, with an explicit uniform
   certificate (degree six, explicit constants) and a faithful statement
   in Collatz terms. The words "new theorem" must not be attached to the
   irrationality statement.

## 1. Monks–Yazinski (2004)

**Source.** K. G. Monks and J. Yazinski, *The autoconjugacy of the 3x+1
function*, Discrete Mathematics 275 (2004), 219–236. Read in the
authors' PDF (`AutoConjV13.pdf`, 14 pages, from
`monks.scranton.edu/files/pubs/`). Page numbers below are those of that
PDF.

**Definitions (source checked, p. 1 and p. 6).** `T(x)=x/2` for even and
`(3x+1)/2` for odd 2-adic integers. `Q_odd` is the ring of rationals with
odd denominator. An orbit is *eventually cyclic* if it is a finite set
and *divergent* otherwise. `kappa_n(x)` is the number of ones among the
first `n` digits of the parity vector of `x`.

**Theorem 2.7(b) (source checked, p. 6; proof pp. 8–11).** If
`x in Q_odd` has a divergent orbit, then
`log 2 / log 3 <= liminf kappa_n(x)/n`.

**Proof audit (source checked).** Lemma 3.2: an orbit in `Q_odd` meets
every bounded real interval in finitely many points (the orbit stays in
`(1/h)Z` for the denominator `h`). Lemma 3.4: an orbit is strictly
positive, strictly negative, or eventually nonnegative. Lemma 4.1: the
liminf is unchanged by passing to an iterate. Lemma 4.2 (positive orbit
bounded below by `m`): comparison with `x -> (3+1/m)x/2` gives
`m <= T^n(x) <= (3+1/m)^kappa 2^{-n} x`. Lemma 4.3 (strictly negative
orbit, hence `<= -1`): comparison with `x -> 3x/2` gives
`-1 >= T^n(x) >= 3^kappa 2^{-n} x`. For a divergent positive orbit `m`
may be taken arbitrarily large by Lemma 3.2. I found no gap. The
argument covers negative rationals and makes no reducedness assumption
beyond an odd denominator.

**Consequence for our theorem (mathematical deduction).** Let `v` be the
fixed point of a length-`L` substitution whose two images both have
weight `r`, or any shift of it. Every aligned block has exactly `r`
ones, so the number `h(l)` of ones in the prefix of length `l` satisfies
`|h(l) - r l / L| <= L`; hence `lim h(l)/l = r/L`, also for every shift.
If `v` is not eventually periodic, a rational seed realising it has an
infinite orbit. If moreover `3^r < 2^L`, then `r/L < log 2/log 3`,
contradicting Theorem 2.7(b). **The subcritical case of the headline
theorem is therefore a known direct corollary (given aperiodicity).**
The argument says nothing when `3^r > 2^L`.

## 2. López–Stoll (2021)

**Source.** J. López and P. Stoll, *The 3x+1 Periodicity Conjeture in R*
(the misspelling is in the arXiv title), arXiv:2101.12747v1, submitted
29 January 2021, 51 pages. The arXiv API lists only version 1 and no
journal reference. I read the TeX source. Section names are used because
the source numbers lemmas with a single counter.

**Statement (source checked, Theorem 1, "Introduction Part (I)").** If
the trajectory of some `zeta in Q_odd` is divergent (infinite orbit),
then `liminf h/l = log 2/log 3`, with `h` the number of ones in the
first `l` digits of the parity vector.

**Structure of the proof (source checked, section "Proof of Theorem
1").**

- `liminf < log 2/log 3`: quoted from Monks–Yazinski Theorem 2.7(b).
- `liminf > log 2/log 3`: (i) the real series
  `Phi_R(v) = - sum_i 2^{d_i}/3^{i+1}` converges (their lemma labelled
  `limarriba`); (ii) the real orbit of `Phi_R(v)` under the maps
  prescribed by `v` contains infinitely many distinct points in a
  bounded interval, hence has an accumulation point (label
  `orbitarriba`); (iii) therefore `Phi_R(v)` is not in `Q_odd`;
  (iv) "From (IL) and (IL2) it follows that the 2-adic `Phi(v)` is
  aperiodic."

**The gap (mathematical deduction).** Step (iv) refers to "Introduction
Part (II)", where the 2-adic integer
`(Phi_R(u^(l)) mod 2^l)_{l>=1}` — the 2-adic limit of the rational
partial sums — is called the "inverse limit of `Phi_R(v)`", and it is
asserted that when the real number `Phi_R(v)` is irrational this 2-adic
integer is aperiodic "because the irrational `Phi_R(v)` does not admit
an eventually periodic 2-adic expansion". A sequence of rationals has a
real limit and a 2-adic limit that are unrelated in general; the text
gives no argument that a *rational* 2-adic limit would have to coincide
with the real limit. The exact relation is their own Lemma labelled
`out`: for a 2-adic integer `zeta` with parity vector `v` and prefix `u`
of length `l` and height `h`,

```text
T^l(zeta) = (phi(u) + 3^h zeta) / 2^l,   i.e.   zeta - Phi_R(u) = (2^l/3^h) T^l(zeta).
```

For rational `zeta` this is an identity between rational numbers. Taking
real limits when `2^l/3^h -> 0`:

```text
T^l(zeta) = (3^h/2^l) (zeta - Phi_R(u))  ~  (3^h/2^l) (zeta - Phi_R(v)).
```

So there are exactly two possibilities. Either `zeta = Phi_R(v)`, the
orbit is bounded, and Lemma 3.2 of Monks–Yazinski gives a finite orbit;
this is the only case the López–Stoll argument treats. Or
`zeta != Phi_R(v)` and `|T^l(zeta)|` grows like `3^h/2^l`: a genuinely
escaping rational orbit. The second case is precisely a divergent
trajectory in the classical sense, and nothing in the paper excludes it.
A concrete test: for a positive integer `n` with a hypothetical
divergent orbit of density above `log 2/log 3`, one has
`Phi_R(v) < -1 < 0 < n`, so the real and 2-adic values certainly differ;
if step (iv) were valid it would prove that no such integer exists,
which is an open part of the 3x+1 problem.

**What the gap does and does not show.** It shows that the proof is
incomplete; it does not show that the statement of Theorem 1 is false
(no counterexample is known, and one would be a divergent rational
trajectory). The periodic case is consistent: for eventually periodic
`v` with `2^l < 3^h` on the period, the geometric series has the same
rational sum in both completions.

**Earlier paper.** J. López and P. Stoll, *The 3x+1 conjugacy map over a
Sturmian word*, Integers 9 (2009), A13, 141–162 (journal PDF read:
abstract and introduction). It gives a 2-adically convergent generalised
continued fraction for `-1/Phi(v)` for mechanical words and states that
the examples "suggest" that `Phi` maps Sturmian words to words of full
complexity. I located no rational-exclusion theorem in it.

**Agreement with the earlier repository audit.** Phase 3
(`infinite-itineraries.md` §2.2) reached the same conclusion. I formed
the assessment above from the source before reading that memo.

**Citation practice for the manuscript.** Cite López–Stoll for the
statement and say plainly that the argument for the direction
`liminf > log 2/log 3` identifies a real limit with a 2-adic one without
proof, so the statement is treated as unproved. Do not describe our
theorem as a corollary of theirs.

## 3. The *p*-adic Mahler method: Molchanov (1983)

**Source.** S. M. Molchanov, *On the p-adic transcendence measure of the
values of functions satisfying some functional equations* (Russian),
Vestnik Moskov. Univ. Ser. I Mat. Mekh. 1983, no. 2, 31–37; received
15 January 1982; Math-Net.Ru record `vmumm3467`
(<https://www.mathnet.ru/eng/vmumm3467>), full-text scan read. The
theorem statement was read from the page images (pp. 31–32), not only
from the OCR layer.

**Theorem (source checked; my translation and notation).** Let `Omega`
be an `s x s` matrix of nonnegative integers whose characteristic
polynomial is irreducible over `Q` and has a root `rho > 1` strictly
larger than the absolute values of its other roots; `Omega` acts on
`T_p^s` by monomials (`T_p` is the completion of the algebraic closure
of `Q_p`). Let `f(z_1,...,z_s)` be transcendental over
`T_p(z_1,...,z_s)`, be given in a neighbourhood `U` of `0` by a Taylor
series with coefficients in a number field `K`, and satisfy

```text
f(Omega z) = A_1(z, f(z)) / A_2(z, f(z)),   A_i(z,y) = a_{i1}(z) y + a_{i2}(z) in K[z,y].
```

Let `alpha = (alpha_1,...,alpha_s) in U` have algebraic coordinates with
`0 < |alpha_i|_p < 1`, and suppose
`A_2(Omega^k alpha, f(Omega^k alpha)) != 0` for all `k >= 0`. Then for
every `d >= 1` there are `H_0 > 0` and `gamma = gamma(Omega) > 0` such
that every `P in Z[x]` of degree `d` and height `H > H_0` satisfies

```text
|P(f(alpha))|_p > H^(-gamma kappa_0^(2s) (b d / c)^(2s-1)),
```

with explicit `kappa_0, b, c` depending on `K` and `alpha`. In
particular `f(alpha)` is transcendental. The paper remarks at the end of
the proof that the irreducibility hypothesis is inessential.

**What I verified.** The hypotheses and conclusion as displayed. The
proof (pp. 32–36) follows Galochkin's archimedean method (reference [4]
there: A. I. Galochkin, Mat. Zametki 27 (1980), no. 2, 175–186): an
auxiliary polynomial `R_0(z,y)` with high vanishing order of
`R_0(z,f(z))`, transport along `Omega^k alpha` by the functional
equation, an ultrametric upper bound, and a Liouville-type lower bound.
I read it in outline and did **not** check it line by line. The only
condition on the point is `0 < |alpha_i|_p < 1` with algebraic
coordinates: no condition on archimedean absolute values, and no
restriction to integers or powers of `p`.

**Related sources not obtained (unresolved).**

- T.-Q. Wang and G.-S. Xu, *p-adic transcendence measures for the values
  of functions satisfying algebraic functional equation of Mahler type*,
  Adv. Math. (China) 35 (2006), 463–475, and T. Q. Wang, *p-adic
  transcendence and p-adic transcendence measures for the values of
  Mahler type functions*, Acta Math. Sin. (Engl. Ser.) 22 (2006),
  187–194, DOI 10.1007/s10114-005-0534-4. The publisher pages require a
  login or a captcha; I did not read either paper. Their existence and
  role are **source checked only through Bugeaud–Yao**, who cite the
  first one (p. 464) for exactly the deduction "transcendental function
  with an order-one Mahler equation and non-vanishing coefficients
  implies transcendental *p*-adic value".
- J. H. Loxton and A. J. van der Poorten, J. Reine Angew. Math. 330
  (1982), 159–172, and the Bundschuh–Väänänen papers named (without
  precise references) by the upstream project. Not obtained.

**Bugeaud–Yao (source checked).** Y. Bugeaud and J.-Y. Yao, *Hankel
determinants, Padé approximations, and irrationality exponents for
p-adic numbers*, Ann. Mat. Pura Appl. 196 (2017), 929–946; author PDF
`p-adic18.pdf`. Theorem 3.1 (PDF p. 6): for `f in Z[[z]]` with
`f(z) = A(z)/B(z) + (C(z)/D(z)) f(z^d)`, non-vanishing of `B C D` along
`b^{d^m}`, `b = p^w`, and infinitely many nonzero Hankel determinants,
`f(b)` is transcendental with an explicit bound for its irrationality
exponent. The first sentence of the proof obtains transcendence of
`f(b)` from: non-rationality (Kronecker), transcendence over `Q(z)`
(Fatou), transcendence over `C_p(z)` (Sharif–Woodcock), and the cited
Wang–Xu result. Their points are powers of `p`; our point `2^L/3^r` is
not, so Theorem 3.1 as displayed does not apply, but the cited general
*p*-adic transcendence theorem is the same kind of statement as
Molchanov's.

**Adamczewski–Faverjon (source checked in Phase 8, not re-read).**
Proc. London Math. Soc. 115 (2017), 55–90, arXiv:1508.07158: complex
points with `0 < |alpha| < 1`. Not applicable to a 2-adic evaluation,
and some of our points have real absolute value above 1.

## 4. Line-by-line derivation of the headline statement from §3

Notation. `mu(0), mu(1)` are binary words of length `L >= 2`, both with
exactly `r` ones, `mu(0) != mu(1)`, and `mu(1)` begins with `1`;
`v = mu(v)` is the fixed point beginning with `1`. Write
`p_a(z) = sum_{t<L} mu(a)_t z^t` and `V(z) = sum_j v_j z^j`.

1. **Mahler equation (deduction).** From `v_{Lj+t} = mu(v_j)_t`:
   `V(z) = p_0(z)/(1-z^L) + (p_1(z)-p_0(z)) V(z^L)`. Equivalently
   `V(z^L) = ((1-z^L) V(z) - p_0(z)) / ((1-z^L)(p_1(z)-p_0(z)))`, which
   is Molchanov's shape with `s=1`, `Omega=(L)`, `rho=L`, `a_{21}=0`,
   `A_2 = (1-z^L)(p_1-p_0)`.
2. **Seed formula (Bernstein 1994; Bernstein–Lagarias 1996, eq. (1.6),
   source checked).** The unique 2-adic integer with parity vector `v`
   is `x(v) = - sum_{i>=0} 2^{d_i}/3^{i+1}`, `d_i` the position of the
   `i`-th one. Because every block has `r` ones, the ones of block `j`
   have indices `rj+t` and positions `Lj + e_{v_j,t}`; hence, with
   `z_0 = 2^L/3^r` and `c_a = sum_{t<r} 2^{e_{a,t}}/3^{t+1}`,
   `x(v) = - c_0/(1-z_0) - (c_1-c_0) V(z_0)` in `Q_2`.
3. **`c_1 != c_0` (deduction).** At the first position `j` where the
   images differ, the two sums agree on earlier terms, exactly one has a
   term of 2-adic valuation `j`, and all later terms have valuation
   above `j`.
4. **Hypotheses of the theorem (deduction).** `0 < |z_0|_2 = 2^{-L} < 1`.
   `1 - z_0^{L^{k+1}}` is a 2-adic unit. `p_1 - p_0` is a nonzero
   polynomial with coefficients in `{-1,0,1}`; its lowest-order
   coefficient is `±1`, so its value at `z_0^{L^k}` has the valuation of
   that lowest term and is nonzero.
5. **Transcendence of `V` over `T_2(z)` (plausible; standard).** `V` is
   not rational because `v` is not eventually periodic (rational series
   with bounded integer coefficients are eventually periodic; this is
   also proved in the repository). Non-rational implies transcendental
   over `Q(z)` (Fatou's lemma for integer series of radius 1, or the
   rational-or-transcendental dichotomy for Mahler functions) and then
   over `C_p(z)`; this is the chain used by Bugeaud–Yao. I did not
   re-derive these classical facts.
6. **Conclusion (deduction).** By §3, `V(z_0)` is transcendental in
   `Q_2`; by steps 2–3 so is `x(v)`. In particular `x(v)` is not
   rational. Shifts: `T` and its two inverse branches preserve
   rationality, so no shift of `v`, and no word that eventually agrees
   with a shift of `v`, has a rational seed.
7. **Aperiodicity of `v`.** Needed in step 5. For binary uniform
   substitutions this follows from the known classification of
   eventually periodic fixed points (plausible; Séébold's work on the
   binary D0L periodicity problem — not obtained), and it is proved
   directly in the repository (`Morphism.not_eventually_periodic`).

Dependence summary: steps 1–4 and 6 are elementary; step 5 uses
classical theorems I did not re-verify; §3 is a published theorem whose
proof I read only in outline. The Lean development depends on none of
this.

## 5. The upstream project

`msharpe248/collatz`, read at commit
`ec8174b567d5cab4960024782210b5f5db02bd3a` (2026-09-06; still the head
of the default branch on 2026-11-14). `paper/rung1.tex`:

- proves in Lean and on paper the exclusion of the fixed point of
  `1 -> 110, 0 -> 011` and its shifts for natural-number seeds;
- states explicitly that irrationality of *p*-adic Mahler values at
  rational points of the unit disc "is a known type of result", says no
  statement covering its value verbatim was located, and makes no
  priority claim for the irrationality;
- describes the extension to *every* constant-length substitution with
  equal block weights as a programme whose input is a Padé certificate
  per word "with odd leading coefficient (or leading coefficient of
  known 2-adic size)", and notes that subcritical words are "already
  excluded by the density corridor".

So the class, the method, and the remark about the subcritical half are
all anticipated there. What the present repository adds relative to
that text is listed in §6.

## 6. Claim-to-source matrix

| # | Claimed contribution | Closest prior source | Applicability | Originality status |
|---|---|---|---|---|
| 1 | No rational 2-adic integer realises the fixed point of an equal-weight uniform binary substitution (H1–H3, `L>=2`) | Molchanov 1983 (§3–4) | Applies to all cases, gives transcendence | **Known by a related theorem** (stronger form). Not new. |
| 1a | Same, subcritical case `3^r<2^L` | Monks–Yazinski 2004, Thm 2.7(b) | Direct, given aperiodicity | **Known direct corollary** |
| 1b | Same, supercritical case `3^r>2^L` | López–Stoll 2021, Thm 1 | Statement applies; proof has a gap (§2) | Claimed earlier with a defective proof; established by 1 |
| 2 | Frequency-based short proof | Monks–Yazinski | Only `3^r<2^L` | **Known direct corollary** for that half; no valid frequency proof for the other half is known to me |
| 3 | Special cases (`mu_L` family, Thue–Morse `10/01`, `110/011`) | Upstream `rung1.tex` (one word); Molchanov | Covered | **Known by a related theorem**; the Thue–Morse-type 2-adic values at `p^w` are in Bugeaud–Yao, our point differs |
| 4 | Degree-six polynomial pair exists for every sequence and closes the height ledger uniformly in `L, r` | Standard Padé/Siegel-lemma linear algebra; upstream certificate-per-word programme | The uniform closing degree is not stated in the sources read | **Possibly new quantitative refinement** of a known method (unresolved: not searched exhaustively) |
| 5 | Proof needs only a linear form `P_0 + P_1 F` and integer arithmetic; non-unit leading coefficient handled by an explicit finite start | Upstream `rung1.tex` observes the degree-one phenomenon for odd leading coefficient | Non-unit case and uniformity are additions | **Possibly new proof** (elementary variant of a known method) |
| 6 | Lean 4 kernel-checked formalisation with semantic audit | Upstream `Rung1.lean` (one word, natural seeds) | Earlier formalisation of one instance exists | **Formalization contribution** |
| 7 | Degree six is least for the implemented certificate interface | none found | Interface-specific | **Possibly new**, of limited scope; says nothing about other methods |
| 8 | Uniform starting level 6 and coefficient bound `720*2^57` | none found | Interface-specific | **Possibly new quantitative refinement**, of limited scope |
| 9 | Rational series with bounded integer coefficients are eventually periodic (and converse) | Classical (Fatou; standard texts) | Same statement | **Known**; formalisation only |
| 10 | Fixed point is not eventually periodic under H1–H3 | Classification of periodic binary D0L words (not obtained) | Expected to cover it | **Known by a related theorem (plausible)**; direct proof is elementary |

## 7. Open items

- Wang 2006 and Wang–Xu 2006 were not read; if obtained, check whether
  their hypotheses on the point match Molchanov's.
- Loxton–van der Poorten 1982 and the Bundschuh–Väänänen papers were
  not read.
- Molchanov's proof was not verified line by line.
- No search of MathSciNet or zbMATH was possible (zbMATH Open API
  returned a proxy error on 2026-11-14); novelty labels "possibly new"
  mean only "not found in the sources listed here".
