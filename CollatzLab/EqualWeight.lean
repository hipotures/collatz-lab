import CollatzLab.MorphismHeight
import CollatzLab.ExponentialGap

/-! Theorem 8.1 for every admissible equal-weight binary morphism under (C). -/
namespace CollatzLab

/-- The mathematical hypotheses are exactly H1--H3 and (C), at any length `L>=2`. -/
theorem no_rational_seed_realizes_equal_weight {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hC : Morphism.Criterion M) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord M) := by
  intro hr
  let AA := (2 : Int) ^ (L * (L - 1) * Morphism.N M)
  let BB := Morphism.m M ^ (L * L + Morphism.e M)
  let K := (L : Int) ^ (L - 1) * Morphism.H M p q 0 ^ (L - 1)
  let Dbase := (2 * (L : Int)) ^ (L - 1)
  have hm : 1 ≤ Morphism.m M := (Morphism.ab_le_mk hL M 0).1
  have hBB : 1 ≤ BB := Family.pow_ge_one hm _
  have hAB : BB < AA := hC
  have hH := Morphism.height_positive hL M hw hd hr 0
  have hK : 1 ≤ K := by
    have h0 := Family.pow_ge_one (x := (L : Int)) (by omega) (L - 1)
    have h1 := Family.pow_ge_one hH (L - 1)
    have hh := Int.mul_le_mul h0 h1 (by decide : (0 : Int) ≤ 1)
      (pow_nonneg_of_nonneg (show 0 ≤ (L : Int) by omega) (L - 1))
    simpa [K] using hh
  have hD : 1 ≤ Dbase := Family.pow_ge_one (by omega) _
  apply no_doubly_exponential_bound L hL AA BB K Dbase hBB hAB hK hD
  intro k
  have hv := (Morphism.valuation hL M h1 hw hd hr k).2.2.2
  have hpow := pow_le_pow_of_le
    (pow_nonneg_of_nonneg (x := 2) (by decide) (Morphism.N M * L ^ (k + 1))) hv (L - 1)
  rw [int_pow_mul] at hpow
  have hexp : (Morphism.N M * L ^ (k + 1)) * (L - 1) =
      (L * (L - 1) * Morphism.N M) * L ^ k := by rw [Nat.pow_succ]; ac_rfl
  rw [hexp] at hpow
  have haid : AA ^ (L ^ k) = (2 : Int) ^ ((L * (L - 1) * Morphism.N M) * L ^ k) :=
    int_pow_mul _ _ _
  have hlo : AA ^ (L ^ k) ≤ absInt (Morphism.E M p q k) ^ (L - 1) := by rw [haid]; exact hpow
  have hbid : BB ^ (L ^ k) = Morphism.m M ^ ((L * L + Morphism.e M) * L ^ k) :=
    int_pow_mul _ _ _
  have hhi : absInt (Morphism.E M p q k) ^ (L - 1) ≤ K * Dbase ^ k * BB ^ (L ^ k) := by
    rw [hbid]
    exact Morphism.form_power_bound hL M h1 hw hd hr k
  exact Int.le_trans hlo hhi

theorem no_rational_seed_realizes_shifted_equal_weight {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hC : Morphism.Criterion M) :
    ∀ (t : Nat) (p q : Int), ¬ RealizesWord p q (shiftWord (Morphism.parityWord M) t)
  | 0, p, q, hr => by
    apply no_rational_seed_realizes_equal_weight hL M h1 hw hd hC p q
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro j
    simpa [shiftWord] using hr.2.2 j
  | t + 1, p, q, hr =>
    no_rational_seed_realizes_shifted_equal_weight hL M h1 hw hd hC t
      (invBranchNum (Morphism.parityWord M t) p q) (invBranchDen (Morphism.parityWord M t) q)
      (realizes_shiftWord_pred (Morphism.parity_binary M t) hr)

theorem no_eventually_shifted_equal_weight_itinerary {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hC : Morphism.Criterion M) (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = Morphism.parityWord M (t + j)) := by
  intro ht
  apply no_rational_seed_realizes_shifted_equal_weight hL M h1 hw hd hC t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

/-- A non-original length-three instance, checked separately from the family. -/
theorem no_rational_seed_realizes_sigma (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.sigma) :=
  no_rational_seed_realizes_equal_weight (by decide) Morphism.sigma
    Morphism.sigma_admissible.1 Morphism.sigma_admissible.2.1
    Morphism.sigma_admissible.2.2 Morphism.sigma_criterion p q

end CollatzLab
