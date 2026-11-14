import CollatzLab.Word
import CollatzLab.Prefix
import CollatzLab.Tower
import CollatzLab.Pade
import CollatzLab.Shifted
import CollatzLab.Family
import CollatzLab.FamilyChecks
import CollatzLab.FamilySemanticChecks
import CollatzLab.MorphismOffset
import CollatzLab.MorphismTower
import CollatzLab.MorphismApprox
import CollatzLab.EqualWeightChecks
import CollatzLab.Secondary
import CollatzLab.SmallCertificates
import CollatzLab.ThueMorse

/-!
# CollatzLab: Lean 4 Formalization of the 4-Automatic Mahler Parity Word

Root module exporting the Lean 4 formalization of the paper
`research/infinite-itineraries.md` (formalizing its finite integer-arithmetic core):
* `CollatzLab.Word`: 4-automatic word `w`, Lemma 3.1, Theorem 3.1 (prefix survival),
  Theorem 3.2 (aperiodicity), and rational 2-adic itinerary definitions.
* `CollatzLab.Prefix`: Finite prefix sums `S_k`, Lemma 4.2, Theorem 6.2(1) base
  identity, and 4-block Mahler functional step.
* `CollatzLab.Tower`: Proposition 6.1 (refutation of uncancelled `Odd D_k`),
  cancelled denominator tower `D_k`, Bézout coprimality of `(a_k, b_k)`, and
  Theorem 6.2(2)–(3) (`a_k^2 ∣ Δ_k` and exact tower step).
* `CollatzLab.Pade`: Theorem 7.1(1)–(3) (degree-4 Padé polynomial identity,
  exact 2-adic valuation `v_2(E_k) = 56 * 4^k`, Archimedean height bound
  `|E_k| < 3 * H_0 * 3^(19 * 4^k)`, and impossibility of rational 2-adic seeds
  realizing `w`).
* `CollatzLab.Shifted`: Lemma 7.2 and Corollary 7.3 (backward preimage closure
  and impossibility of rational 2-adic seeds realizing any shifted word `w^{(t)}`).
* `CollatzLab.Family`: Theorem 4.1 and Corollary 9.1 of
  `research/mahler-generalization.md`, uniformly for every block length `L >= 4`:
  exact finite Mahler congruences, cancelled integer towers, the periodic
  approximant's exact valuation, and the archimedean height contradiction.
* `CollatzLab.FamilyChecks`: literal block semantics, first disagreement with
  the periodic approximant, and positive finite-prefix realization witnesses.
* `CollatzLab.EqualWeight`: generic Theorem 8.1 under exactly H1--H3 and (C),
  arbitrary rational seeds, shifts and eventual matches; signed cancellation,
  positive denominator conversion, exact valuation and general height bounds.
* `CollatzLab.ThueMorse`: rational exclusion of the `10/01` word and its tails
  by a separate subcritical block contraction and aperiodicity proof.
-/
