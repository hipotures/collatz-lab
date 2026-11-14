# Phase 12 prior-art gate — issue #24

Gate opened 14 November 2026 (UTC), before proof implementation. The initial
matrix was checkpointed at `a873a82` (use the journal for the full SHA). The
source-triage pass is complete: the candidate is covered by an earlier
density-sensitive criterion, and the minimum determinant proposal is
combinatorially automatic. Detailed independent reductions are in
`phase12-findings.md`. Missing access or failure
to find a theorem never establishes novelty.

Candidate: the selected fixed word of `1 -> 100111`, `0 -> 111110`.
Notation: `W(a,n)` is the number of ones in `[a,a+n)`, `P(n)` is **global**
factor complexity, `delta=5/7`, and `m(delta)=max(1,delta*log2(3))`.

| Primary theorem and version | Exact premises and domain | Proof inspection / candidate implication | Classification |
|---|---|---|---|
| Allikvere, Zenodo 21543841, July 2026, Lemma 2.1, Theorem 2.3, Corollary 3.2 | A nonperiodic parity word; periodic shadow of length s, weight h, matching length L; unbounded `L-s-h*log2(3/2)` excludes any signed rational seed. Squares suffice. | Original deposited TeX read in this pass: elementary sharp height and nonzero argument checked. Initial `10` only defeats the initial-double shortcut. The global return bound and absence of all initial squares are independently proved in the findings. | **Known earlier preprint**; sharp weight-only bound is too weak for the actual returns; no initial squares (proved independently). |
| Allikvere, same original, §5 Theorem 5.3 and Corollary 5.7 (first repetitions and complexity) | Not eventually periodic; uniform upper density delta; `liminf P(n)/n < 1/(m(delta)-1)` suffices. General shadow condition is `L>(1+epsilon)*m(delta)*(preperiod+period)`. Both seed signs; stronger conclusion transcendence. | Statement and main proof read; the rational subcase is independently checked using only collision/growth. Generic binary length-L fixed words have `P(L^k)<=4L^k`, while here `m(5/7)<5/4`. This establishes **direct coverage**, despite the finite ratios in the issue. Full transcendence proof is not assumed. | **Follows** from checked elementary rational subcase and structural bounds; not a novelty opportunity for irrationality. |
| Cassidy, pinned 6b805eed1613edaedd87965e2b1986390fa84f0e, 22 September 2026, §4.3 Lemma G / Theorem R | Any affine binary 2-adic shift map with odd slopes; not eventually periodic; unbounded common-prefix length minus log height of eventually periodic approximants. Signed rationals, odd denominator. | Original note's statements and short proofs read. Allows nonempty preperiod: scanning only returns of the initial prefix is insufficient triage. | **Known earlier preprint framework**; density-sensitive shadows give coverage (findings §3). |
| Dubickas, Glasgow Math. J. 51 (2009), Theorem 5, proof §5 | Positive integer orbit tending to infinity; `liminf P(n)/n >= log(2)/log(3/2)`. | Original Theorem 5 and full proof §5 read in this pass (pp. 246, 249–250). Signed-rational extension is the separately derived Phase 11 referee §2.4, not the literal journal statement. Finite lower counts above 1.7095 cannot prove its sufficient criterion inapplicable. | **Published theorem / derived extension**; candidate worst-case applicability unresolved. |
| De Jesús, Zenodo 23108370, deposited v3, §9 Lemma 9.1 / Proposition 9.2 / Corollary 9.3 and §10 | Signed rational odd-denominator states; non-eventual-periodicity; lower global complexity ratio below `1/log2(3/2)`; separately, initial squares. | Original PDF text §9 read; exact signed extension agrees with Phase 11 deduction. Read §10 and its proofs as well: its mechanical-word premise does not describe this rational-frequency fixed point. The drift-sensitive reference points back to Pham/Allikvere. | **Known earlier preprint**; no new criterion from renaming counting. |
| Monks–Yazinski, Discrete Math. 275 (2004), Theorem 2.7(b) | Infinite rational odd-denominator orbit, either sign: lower odd density at least `log(2)/log(3)`. | Original Theorem 2.7(b), Lemmas 3.2/3.4 and complete relevant proof §4.1 re-read; candidate 5/7 exceeds this lower bound. | **Published theorem**, no contradiction from this premise. |
| Molchanov, Vestnik Moskov. Univ. (1983), no. 2, pp. 31–37 | Transcendental analytic function, fractional-linear p-adic Mahler equation, contracting algebraic point and orbit nonvanishing; monomial matrix hypotheses. | Original metadata and abstract obtained. A PDF response appeared once in the web tool, but subsequent page/image retrieval redirected to metadata; no independently readable complete proof was obtained in this pass. Detailed theorem hypotheses here are the earlier Phase 9 source transcription, not a new complete proof audit. Unequal weights do not give the equal-weight scalar seed formula. Ordinary automaticity alone is insufficient. | **Published theorem**, candidate specialization unresolved. |
| lyapunov_weaver, rStation paper 16 v3, 27 October 2026, Theorems 1, 1c, 1d | Claimed eventual periodicity of automatic/primitive parity of a **positive** rational seed; more nonprimitive variants. | Original v3 statements, §§4–5, 8, 10 and 14 inspected. The critical assertion is Proposition 3/6 value lifting and the transport of rational relations across completions; that long analytic chain has not been independently certified here. Theorem 1b alone fails its irreducible-polynomial premise, but Theorems 1/1c/1d claim coverage. Uniform binary word is automatic and its incidence is primitive; claimed positive-seed coverage must be recorded. Platform acceptance is not journal peer review. | **Unresolved stronger claimed overlap**, not silently dismissed or assumed. |
| Bernstein–Lagarias, Canad. J. Math. 48 (1996), equations (1.5)–(1.6), Appendix A | Parity map is a bijective 2-adic isometry; finite binary cylinders admit rational/integer witnesses. | Original Appendix A Lemmas A.1–A.2 / Corollary A.3 and Appendix B finite-lifting construction inspected through the author PDF in the web tool (direct download returned 403). Finite compatibility makes the proposed determinant congruence independent of infinite rationality. | **Published foundation**; elementary no-go formalized independently, no priority claim. |

No entry labels a result new. Structural proof, global bounds, finite checks,
external statements and kernel verification are separately identified.


## Additional applicable originals

| Primary theorem and version | Exact premises and domain | Proof inspection / candidate implication | Classification |
|---|---|---|---|
| Pham, pinned d4134391aef1fe53634bbd30d67fd1d9a12d0d7a, 22 July 2026, Part IV Theorem 3, Part V Corollary 7 | Signed rational realization; finite pressure bound on all initial orbit states; equal length-k factors force congruent states; bounded uniform upper discrepancy gives a complexity restriction. Corollary 7 literally uses **limsup**. | Original finite collision proof and pressure bound read. The candidate's logarithmic discrepancy can be bounded by `epsilon*n+C_epsilon`, uniformly over windows using power blocks. Do not replace this source's limsup with liminf. The direct finite collision argument in findings §3 avoids that ambiguity. | **Known earlier preprint mechanism**, not a new density-aware obstruction. |


| De Jesús, *A drift-sensitive complexity bound for rational points of the 3x+1 conjugacy map*, revision 1, 30 September 2026, [Zenodo 23071770](https://doi.org/10.5281/zenodo.23071770), Lemmas 7–8, Theorem 9, Corollary 15 | Not eventually periodic, existing one-frequency d; signed rational seed forces lower complexity ratio at least `1/(d*log2(3)-1)` when supercritical. The finite theorem uses actual maximal upward drift. | Fresh original PDF obtained; numerator/collision lemmas, frequency/drift proof, main theorem and tradeoff proof read and independently checked. Here `C=liminf P(n)/n<=4` and `d=5/7 < (5/4)/log2(3)`, so it directly excludes this candidate. | **Follows from earlier preprint**; decisive further coverage, not a new refined counting theorem. |
| lyapunov_weaver, *Finite approximation bounds for mechanical Collatz itineraries*, [rStation 84 v1](https://rstation.ai/problems/collatz/papers/84), 2 November 2026, §10.1 / Theorem 9 | Critical characteristic Sturmian word; two standard periodic approximants form an exact parity lattice basis. A positive supplied integer source, signs of the basis coordinates and an external S-unit inequality are retained. | Original §10.1 determinant/basis/source equations read and algebra inspected; the full Evertse-based exponent proof is not independently certified. The candidate has rational frequency and is not this Sturmian word. Shows why a seed-free determinant no-go does not refute multi-approximant height methods. | **Known earlier platform-preprint framework**, no direct candidate application under the checked premises. |
| lyapunov_weaver, *Additive structure and integer rigidity of Collatz orbit sets*, [rStation 31 v1](https://rstation.ai/problems/collatz/papers/31/v1), 24 October 2026, §4 Lemma 4 | Actual positive integer states returning to one progression of step d; short return maps force determinant divisible by d. A strict size bound forces a common fixed point. | Original lemma and full local return-word proof read; global additive-combinatorial theorem not independently audited. No such progression-return premise is supplied for this word. The algebraic determinant tactic itself predates this phase. | **Known earlier platform-preprint mechanism**, not an exclusion for arbitrary matching parity prefixes. |

## Primary provenance and limits

Allikvere's metadata, PDF and TeX were freshly downloaded through
`https://zenodo.org/api/records/21543841`. Created 25 July, last updated
13 August 2026. De Jesús's record 23108370 was created 2 October, updated
8 November 2026; the deposited PDF is `sturmian_irrationality_v3.pdf`.
The record's later status note points to Allikvere and other subsequent work;
that metadata is not silently substituted for a theorem in the deposited PDF.
The exact source URLs and SHA-256 hashes are in `phase12/sources.json`.
Third-party full texts are not redistributed. Cached Phase 11 originals were
read initially; fresh downloads of Allikvere, De Jesús, Cassidy and rStation
match their previously recorded hashes. Monks–Yazinski's fresh author PDF has
a different byte hash; its theorem and relevant proof were actually re-read.

Primary links:

- [Allikvere deposited record](https://doi.org/10.5281/zenodo.21543841)
- [Cassidy pinned note](https://github.com/eliottcassidy2000/math/blob/6b805eed1613edaedd87965e2b1986390fa84f0e/05-knowledge/results/collatz_procgen_20260922_transversality_foundry.md)
- [Dubickas publisher original](https://doi.org/10.1017/S0017089508004655)
- [De Jesús deposited v3](https://doi.org/10.5281/zenodo.23108370)
- [Monks–Yazinski author original](https://monks.scranton.edu/files/pubs/AutoConjV13.pdf)
- [Molchanov primary record](https://www.mathnet.ru/eng/vmumm3467)
- [rStation exact v3 Markdown](https://rstation.ai/api/v1/papers/collatz_16/versions/3/download)
- [Bernstein–Lagarias author original](https://websites.umich.edu/~lagarias/doc/bernstein.pdf)
- [Pham pinned original](https://github.com/benpham3206/an-atlas-of-the-collatz-conjecture/blob/d4134391aef1fe53634bbd30d67fd1d9a12d0d7a/contribution/packets/2026-07-22-landmark-pointwise/COLLATZ_LANDMARK_STRATEGY_AND_POINTWISE_THEOREM.md)

Allikvere's stronger §5 also states transcendence. Only its elementary rational
subcase is independently established here. Its complete Subspace Theorem
application is not imported into Lean or advertised as independently certified.
For the exact threshold, `3^20 < 2^35` implies
`(5/7)*log2(3) < 5/4`, hence `4 < 1/(m(5/7)-1)`.
The global bound `P(6^k)<=4*6^k` supplies an upper bound on the liminf;
finite counts 724 and 2676 are not used for this implication.

López–Stoll 2021 is not used: the real/2-adic limit transfer identified in the
existing prior-art reports remains unproved. The ordinary automatic generating
series is not the Collatz inverse-parity series. No scalar Mahler
specialization for the latter is assumed. The rStation positive-rational
claim is recorded in full relevant scope without treating platform acceptance
as human peer review; both seed signs are instead covered by the elementary
known-method reduction in the findings.

Searches combined rational Collatz parity, automatic/morphic/S-adic words,
factor complexity, pressure, periodic shadows, and two-return determinants.
The directly relevant additional multi-approximant sources and their limits
are recorded in the additional-originals table. No completeness of a
MathSciNet/zbMATH search or absence of earlier results is claimed.


## Final gate decision

The candidate is **covered**, with all required structural premises independently
proved. Two elementary written reductions and the later direct drift-sensitive
source confirm the same conclusion. Do not spend a further cycle on its known
irrationality. Gate B instead targets the precise structural limitation of
seed-free two-return elimination; Gate C investigates the return recursion
and finite global languages. Neither produces a new exclusion theorem.

No claim is made that the 2009 worst-case complexity criterion fails globally:
its smaller sufficient premise was not established. No claimed automatic-word
theorem is needed for the signed conclusion. The remaining quantitative
approximation question is stated explicitly in the findings, with novelty and
source scope still open for human review.
