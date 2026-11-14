import CollatzLab.PolynomialCertificate
import CollatzLab.RationalSeries
import CollatzLab.MorphismAperiodic
import CollatzLab.DegreeSix

/-! Universal rational exclusion for all admissible equal-weight binary uniform morphisms. -/
namespace CollatzLab
namespace Morphism

/-- A finite polynomial certificate exists for every admissible pair of images. -/
theorem universal_degree_six_certificate {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) :
    ∃ P : PolynomialPair, ∃ N : Nat, P.degree = 6 ∧ 13 ≤ N ∧
      (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧
      P.First (parityWord M) N ∧ P.Gap M N := by
  rcases PolynomialPair.degree_six_pair_exists (parityWord M) with ⟨P, hdeg, hp, hzeros⟩
  have hp' : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0 := by rw [hdeg]; exact hp
  rcases RationalSeries.nonzero_residual (parityWord M) (parity_binary M)
    (not_eventually_periodic hL M h1 hw hd) P hp' with ⟨n, hn⟩
  rcases RationalSeries.first_nonzero_coefficient (P.residual (parityWord M)) n
    ⟨n, Nat.le_refl _, hn⟩ with ⟨N, _, hlead, hbefore⟩
  have hN : 13 ≤ N := by
    by_cases h : N < 13
    · have hh := hzeros N h
      contradiction
    · omega
  refine ⟨P, N, hdeg, hN, hp', ⟨hbefore, hlead⟩, ?_⟩
  have hgap := degree_six_ledger hL M hw hd
  have hmono := Family.pow_mono_exp (x := (2 : Int)) (by decide)
    (Nat.mul_le_mul_left (L * (L - 1)) hN)
  unfold PolynomialPair.Gap
  rw [hdeg]
  exact Int.lt_of_lt_of_le hgap hmono

end Morphism

/-- H1--H3 and `L>=2` are the only morphism hypotheses. -/
theorem no_rational_seed_realizes_all_equal_weight {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord M) := by
  rcases Morphism.universal_degree_six_certificate hL M h1 hw hd with ⟨P, N, hdeg, hN, _, hfirst, hgap⟩
  exact no_rational_seed_with_polynomial_pair hL M h1 hw hd P N (by omega) hfirst hgap p q

theorem no_rational_seed_realizes_shifted_all_equal_weight {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) :
    ∀ (t : Nat) (p q : Int), ¬ RealizesWord p q (shiftWord (Morphism.parityWord M) t)
  | 0, p, q, hr => by
    apply no_rational_seed_realizes_all_equal_weight hL M h1 hw hd p q
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro j
    simpa [shiftWord] using hr.2.2 j
  | t + 1, p, q, hr =>
    no_rational_seed_realizes_shifted_all_equal_weight hL M h1 hw hd t
      (invBranchNum (Morphism.parityWord M t) p q) (invBranchDen (Morphism.parityWord M t) q)
      (realizes_shiftWord_pred (Morphism.parity_binary M t) hr)

theorem no_eventually_shifted_all_equal_weight_itinerary {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = Morphism.parityWord M (t + j)) := by
  intro ht
  apply no_rational_seed_realizes_shifted_all_equal_weight hL M h1 hw hd t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

theorem no_integer_seed_realizes_all_equal_weight {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (p : Int) :
    ¬ RealizesWord p 1 (Morphism.parityWord M) :=
  no_rational_seed_realizes_all_equal_weight hL M h1 hw hd p 1

end CollatzLab
