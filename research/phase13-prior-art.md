# Phase 13: primary-source and concept audit

Issue [#28](https://github.com/hipotures/collatz-lab/issues/28). Source inspection
started 15 November 2026, before implementing the reconstruction engine.
This is AI-assisted research, not independent human peer review. No priority
claim follows from this search.

Let `x=Phi(w)`, where Phi is the inverse Collatz parity map, and let
`A_N=x mod 2^N`. Height always means `max(|p|,q)`, with `q>0` odd and the
fraction reduced. The ordinary binary digits of **x**, rather than the parity
letters **w**, are the input to the classical 2-adic complexity algorithms.

## Theorem-level comparison

| Original / version | Definition, assumptions, quantifiers and conclusion | Passages actually inspected; reduction to this project | Classification |
|---|---|---|---|
| B. M. M. de Weger, *Approximation lattices of p-adic numbers*, J. Number Theory **24** (1986), 70–88, [DOI](https://doi.org/10.1016/0022-314X(86)90059-4); [author PDF](https://math.deweger.net/papers/%5B1%5DdW-ApprLatt-JNumTh%5B1986%5D.pdf) | For alpha in Z_p, Gamma_m consists of all integer `(P,Q)` with `|P-Q alpha|_p<=p^-m`. Lemma 2.1 gives its basis, determinant and nesting. Theorem 4.1 gives infinitely many norm-controlled approximations to every irrational alpha; Theorem 4.2 gives a sufficient best-approximation criterion. | Original pp. 71–78, 80, 82–83 read, including the local proofs. Square norm has lattice constants Delta=1 and c=2. These are whole-lattice assertions, without the odd-Q restriction. Section 3's reduction is known; Theorem 2.1 concerns linear periodicity of the entire lattice sequence, not substitution-power recurrences. The quadratic converse proof pp. 74–76 was read in outline only. | **Known foundations**; no all-orders square-root bound for the constrained problem follows. |
| P. S. Wang, M. J. T. Guy, J. H. Davenport, *P-adic reconstruction of rational numbers*, SIGSAM Bulletin **16**(2) (1982), 2–3, [DOI](https://doi.org/10.1145/1089292.1089293), [author text](https://www.cecm.sfu.ca/personal/mmonagan/teaching/TopicsinCA13/GuyDavenWang.pdf) | RATCONVERT recovers a bounded fraction **if it exists**. Euclidean convergents cover the balanced reconstruction region. | Entire two-page text and continued-fraction argument read. The original explicitly supplies empty reconstruction regions. The cross-product uniqueness argument gives uniqueness when `2 P Q<M`; it cannot guarantee existence for every residue. | **Known reconstruction / uniqueness**. |
| FLINT, [reference](https://flintlib.org/doc/fmpq/reconstruct.html), [algorithm documentation](https://flintlib.org/doc/algorithms/number-theory/rational-reconstruction.html), `src/fmpq/reconstruct_fmpz_2.c`, fetched 2026-11-15 | Given bounds N,D, returns success only for a fraction satisfying numerator/denominator bounds, congruence and coprimality. | Reference and source success/failure branches, final gcd and denominator checks inspected. Source master is mutable; fetched content hash is recorded. This is a bounded existence test, not an unconditional minimax solver. No FLINT dependency is added. | **Known implementation**; scope limitation confirmed. |
| A. Klapper and M. Goresky, *Feedback Shift Registers, 2-Adic Span, and Combiners with Memory*, J. Cryptology **10** (1997), 111–147, [DOI](https://doi.org/10.1007/s001459900024), [author manuscript](https://www.cs.engr.uky.edu/~klapper/pdf/fcsr.pdf) | Complexity of a finite binary expansion is `log2 min max(|p|,|q|)` over odd q. Theorem 10.1 minimizes this norm exactly; Lemmas 10.3–10.4 prove the adaptive odd-denominator lattice algorithm. | Author manuscript pp. 24–29, Figure 4, exact statements and full optimality induction read. Journal landing metadata checked; journal PDF download returned 403. Sign normalization and removing common odd factors identify this minimum exactly with `log2 H_N` for the **digits of Phi(w)**. | **Exact prior coverage of general invariant and engine**. Implementing it is replication, not a new algorithm. |
| A. Klapper, *The asymptotic behavior of N-adic complexity*, Adv. Math. Commun. **1**(3) (2007), 307–319, [DOI](https://doi.org/10.3934/amc.2007.1.307), [author text](https://www.cs.uky.edu/~klapper/pdf/asymptotic.pdf) | For a non-eventually-periodic base-2 digit sequence, normalized log-height has accumulation set `[B,1-B]`, `0<=B<=1/2` (Corollary 3.4). Lemma 2.1 bounds a height jump between `2^(n-1)/H_n` and `H_n+2^n/H_n`. | Definitions, Lemma 2.1, Theorems 3.2–3.3 and Corollary 3.4 with proofs read in author version. Its base parameter N must not be confused with our prefix length. Rational seeds are the excluded eventually-periodic **digit** case. | **Known asymptotic constraint**; a limit must be 1/2. Determining B for this Collatz seed remains unaddressed by the checked statements. |
| G. Romeo, *Continued fractions in the field of p-adic numbers*, Bull. Amer. Math. Soc. **61** (2024), [DOI](https://doi.org/10.1090/bull/1819); [arXiv:2306.14837v1](https://arxiv.org/abs/2306.14837v1), 26 June 2023 | Survey of distinct algorithms and their convergence, periodicity and approximation properties. | Original author version introduction and Section 7 pp. 19–21 read. Mahler/de Weger norm minimization differs from generic Browkin/Ruban convergents. Publisher PDF returned 403; no claim to have compared later textual changes. | **Known context**, not a completeness theorem for an arbitrary convergent scan. |
| B. Ward, *Counting rational points close to p-adic integers and applications in Diophantine approximation*, [2026 DOI](https://doi.org/10.1017/S0017089526100950); [arXiv:2102.09070v2](https://arxiv.org/abs/2102.09070v2), 26 March 2021 | Counts integer vectors with bounded coordinates and small linear-form error. Theorem 1.2 assumes Diophantine exponent n+1; Lemma 1.3 gives lower counts under strict exponent inequalities. | Original v2 definitions and statements pp. 1–3 read; proofs are not independently audited. Publisher original inaccessible. Counts allow p-divisible denominators and nonprimitive vectors. Assuming exponent 2 for our seed would assume the desired conclusion. | **Known related counting**, no exact H_N or candidate exponent supplied. |
| D. J. Bernstein, *A non-iterative 2-adic statement of the 3N+1 conjecture*, Proc. AMS **121** (1994), 405–408, [DOI](https://doi.org/10.1090/S0002-9939-1994-1186982-9) | `Phi(sum 2^d_i)=-sum 2^d_i/3^(i+1)` is bijective; finite truncations have the same precision. | Owner-supplied original PDF `/home/user/S0002-9939-1994-1186982-9.pdf`, pp. 405–408 read. Its C uses the unsqueezed odd branch; the series is the same inverse map for our accelerated T. | **Known parity inversion**. |
| Bernstein–Lagarias, *The 3x+1 conjugacy map*, Canad. J. Math. **48** (1996), 1154–1169, [DOI](https://doi.org/10.4153/CJM-1996-060-x), [publisher original](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/6975BB4A8C46CF6842217043AAF9EC13/S0008414X0004606Xa.pdf/3x_1_conjugacy_map.pdf) | The inverse parity map is a solenoidal isometry; reduction modulo 2^n is a permutation. | Equations (1.5)–(1.6), Appendix A and Appendix B local lifting argument read. These imply the finite cylinder equivalence for signed odd-denominator fractions. They do not identify digit complexity of Phi(w) with complexity of w. | **Known bridge; new repository formalization planned**. |
| S. M. Molchanov (1983), [primary record](https://www.mathnet.ru/eng/vmumm3467); Monks–Yazinski, Discrete Math. **275** (2004), 219–236, [author original](https://monks.scranton.edu/files/pubs/AutoConjV13.pdf); López–Stoll, [arXiv:2101.12747v1](https://arxiv.org/abs/2101.12747v1) | Respectively: Mahler value measures with analytic functional-equation hypotheses; rational-orbit lower density; a claimed density equality for divergent rational orbits. | Phase 9 source audit and Phase 11/12 independent reports read. Monks–Yazinski original Theorem 2.7(b) and proof revisited. Molchanov full proof not re-obtained; López–Stoll's real/2-adic limit gap persists. Unequal weights do not supply the scalar equal-weight equation needed for that Mahler specialization. | **Known / unresolved applicability**, not an effective measure for frontierSix. |
| Allikvere, [Zenodo 21543841](https://doi.org/10.5281/zenodo.21543841), original deposited TeX; Cassidy, [pinned note](https://github.com/eliottcassidy2000/math/blob/6b805eed1613edaedd87965e2b1986390fa84f0e/05-knowledge/results/collatz_procgen_20260922_transversality_foundry.md), 22 September 2026; Dubickas, Glasgow Math. J. **51** (2009), [DOI](https://doi.org/10.1017/S0017089508004655) | Periodic shadows, matching precision versus shadow height, and distinct numerator states versus factor complexity. | Fresh originals match Phase 12 hashes. Allikvere sharp and density-sensitive shadow statements/proofs, Cassidy Lemma G/Theorem R, Dubickas Theorem 5/proof Section 5 read. These exclude rationality under checked structural premises; they do not determine this H_N exponent. Stronger transcendence chains are not certified here. | **Known methods**, including their finite height mechanisms. |
| E. De Jesús, *A drift-sensitive complexity bound for rational points of the 3x+1 conjugacy map*, [Zenodo 23071770](https://doi.org/10.5281/zenodo.23071770), revision 1, 30 September 2026 | Signed rational orbit; finite numerator confinement via upward drift; aperiodicity makes all states distinct. Theorem 9/Corollary 15 give frequency-sensitive complexity bounds. | Fresh original pp. 2–5, Lemmas 2–8, Theorem 9 and Proposition 10 with elementary proofs read. Directly covers known irrationality of the Phase 12 word. Extending the finite confinement argument to finite rational shadows requires a **finite distinct-state proof**, not just infinite aperiodicity. | **Known mechanism**; any finite-height specialization must be attributed as a deduction. |

## Gate decision and revised analytic target

The general minimum and an efficient odd-denominator algorithm are already
published. Even the complementary liminf/limsup relation is known. The task
is well posed, but neither of these can be a new headline. Implement two
independent exact routes with explicit certificates, then investigate:

1. Bounds for `B=liminf log2(H_N)/N` for the actual frontierSix seed, rather
   than an unrestricted residue or the parity word's ordinary digit value.
2. Exact substitution-induced affine products and finite-height consequences
   of the known drift argument, retaining finite agreement and state heights.

Fresh searches also included rational reconstruction, odd cosets, 2-adic
complexity profiles, Collatz irrationality measures and lattice dynamics.
The 2026 survey search led to the important 1997 and 2007 originals above.
An initially guessed arXiv identifier `2306.14823` was unrelated and discarded;
the correct Romeo original is `2306.14837`. The first guessed AMS suffix was
wrong; the owner-supplied Bernstein original resolves it. These corrections
are recorded to prevent accidental reuse of unrelated cached texts.

No source found in this bounded search determines B for the selected seed.
This is **unresolved under checked hypotheses**, not proof of originality.
Third-party originals stay outside the repository; hashes and access errors
are recorded in `phase13/sources.json`.

## Post-experiment claim audit

The substituted shadows `mu^k(100) mu^k(1)^infinity` give the explicit
candidate bound `B<=(25/98)*log2(3)` and a nonconvergence proof in the theory
report. Its ingredients reduce to Bernstein inverse branches, Allikvere's
preperiodic-shadow height mechanism and the classical cross-product bound.
Klapper already supplies the complementary accumulation relation. Therefore
this is classified as an **explicit known-method quantitative specialization**,
with priority for the exact constant unverified. It is neither an original
general criterion nor a newly discovered irrationality result.

A fresh search on the exact two images and approximation-height terminology,
and on Collatz morphic shadows/irrationality exponents, did not find this
specific constant. That search is not a novelty certificate. Real automatic
digit approximation results (for example Bugeaud–Krieger–Shallit, Acta Arith.
149 (2011), 181–199, [DOI](https://doi.org/10.4064/aa149-2-7)) concern different
numbers and norms; their introduction was screened, but their full proofs
were not audited and they are not used to derive a theorem here. The
finite drift alternative is explicitly attributed to the earlier De Jesús
confinement mechanism, with its additional finite-state distinctness premise
proved separately.

The final deeper pass derives exact reduced-shadow minima on an infinite
subsequence by the **known strict uniqueness criterion**, and finds a raw
gcd counterexample plus periodic congruence certificates modulo 347 and
347^2. These use classical rational reconstruction and finite affine-map
arithmetic. They are classified as explicit candidate specializations /
certificates with priority unverified, not new general approximation or
automatic-word theorems. The full finite integer shadow inequalities are now
formalized; real-limit and modular-cycle deductions have separate written
proofs and do not acquire kernel status from their supporting finite tests.

## Additional late search hits and explicit access limits

- [*On the Nth 2-adic complexity of binary sequences identified with algebraic
  2-adic integers*](https://www.sciencedirect.com/science/article/pii/S0166218X2500263X),
  publisher PII S0166218X2500263X (2025): the publisher-indexed introduction
  explicitly defines the same positive-odd-denominator minimum, without
  reducedness, and announces bounds under algebraicity of the ordinary digit
  value. Direct original access returned 403; the numbered bounds and proofs
  were **not obtained**. No algebraicity hypothesis for Phi(w) is established
  or imported here. This reinforces known status of the invariant; applicability
  of uninspected finer bounds is unresolved.
- Chen–Obrovsky–Winterhof, *Maximum-order Complexity and 2-Adic Complexity*,
  IEEE Trans. Information Theory **70**(8) (2024), 6060–6067,
  [DOI](https://doi.org/10.1109/TIT.2024.3405946): author-institution metadata
  and abstract inspected. It relates ordinary digit maximum-order complexity
  to 2-adic complexity. The full numbered theorem/proof was not obtained, and
  no maximum-order complexity premise for the **digits of Phi(w)** is supplied.
  It is not a theorem about w merely because w is automatic.
- [*If a machine did it, it is probably transcendental (even p-adically)*](https://doi.org/10.1007/s00209-026-04096-3)
  (2026): publisher search passage discusses low-complexity words of p-adic
  continued-fraction partial quotients. The original proof chain was not
  audited and no such continued-fraction description is given for our seed.
  This is an unresolved adjacent source, not an exclusion or exponent theorem
  used in the present development.

Fresh exact-image / constant / divisor searches also found no source for the
particular 347 cycle or 25/98 specialization. They provide no proof of priority.
