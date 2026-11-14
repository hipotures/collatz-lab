import CollatzLab.PolynomialHeight

/-! Conditional general polynomial certificates, with no unit-coefficient assumption. -/
namespace CollatzLab
open Family

/-- Every premise is a finite coefficient condition or an exact integer base gap. -/
theorem no_rational_seed_with_polynomial_pair {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (P : PolynomialPair) (N : Nat) (hN : P.degree ≤ N)
    (hfirst : P.First (Morphism.parityWord M) N) (hgap : P.Gap M N) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord M) := by
  intro hr
  rcases int_two_power_factorization _ hfirst.2 with ⟨v, c, hc, hlead⟩
  rcases finite_start_for_leading_coefficient L hL v with ⟨k0, hk0⟩
  let AA := (2 : Int) ^ (L * (L - 1) * N)
  let BB := Morphism.m M ^ (P.degree * (L - 1) + L + Morphism.e M)
  let K := P.heightConstant ^ (L - 1) * Morphism.H M p q 0 ^ (L - 1)
  let Dbase := (2 * (L : Int)) ^ (L - 1)
  have hm : 1 ≤ Morphism.m M := (Morphism.ab_le_mk hL M 0).1
  have hBB : 1 ≤ BB := pow_ge_one hm _
  have hAB : BB < AA := hgap
  have hH := Morphism.height_positive hL M hw hd hr 0
  have hK : 1 ≤ K := by
    have h0 := pow_ge_one P.heightConstant_positive (L - 1)
    have h1 := pow_ge_one hH (L - 1)
    have hh := Int.mul_le_mul h0 h1 (by decide : (0 : Int) ≤ 1)
      (pow_nonneg_of_nonneg (show 0 ≤ P.heightConstant by have := P.heightConstant_positive; omega) (L - 1))
    exact hh
  have hD : 1 ≤ Dbase := pow_ge_one (by omega) _
  apply no_eventual_doubly_exponential_bound L hL AA BB K Dbase hBB hAB hK hD k0
  intro k hk
  have hv := (PolynomialPair.valuation hL M h1 hw hd P N v hN hfirst.1 c hc hlead hr k (hk0 k hk)).2.2.2
  have hdrop := pow_mono_exp (x := (2 : Int)) (by decide) (show N * L ^ (k + 1) ≤ N * L ^ (k + 1) + v by omega)
  have hlo0 := Int.le_trans hdrop hv
  have hpow := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := 2) (by decide) (N * L ^ (k + 1))) hlo0 (L - 1)
  rw [int_pow_mul] at hpow
  have hexp : (N * L ^ (k + 1)) * (L - 1) = (L * (L - 1) * N) * L ^ k := by
    rw [Nat.pow_succ]; ac_rfl
  rw [hexp] at hpow
  have haid : AA ^ (L ^ k) = (2 : Int) ^ ((L * (L - 1) * N) * L ^ k) := int_pow_mul _ _ _
  have hlo : AA ^ (L ^ k) ≤ absInt (PolynomialPair.E M P p q k) ^ (L - 1) := by rw [haid]; exact hpow
  have hbid : BB ^ (L ^ k) = Morphism.m M ^ ((P.degree * (L - 1) + L + Morphism.e M) * L ^ k) := int_pow_mul _ _ _
  have hhi : absInt (PolynomialPair.E M P p q k) ^ (L - 1) ≤ K * Dbase ^ k * BB ^ (L ^ k) := by
    rw [hbid]
    exact PolynomialPair.form_power_bound hL M h1 hw hd P hr k
  exact Int.le_trans hlo hhi

theorem no_rational_seed_with_shifted_polynomial_pair {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (P : PolynomialPair) (N : Nat) (hN : P.degree ≤ N)
    (hfirst : P.First (Morphism.parityWord M) N) (hgap : P.Gap M N) :
    ∀ (t : Nat) (p q : Int), ¬ RealizesWord p q (shiftWord (Morphism.parityWord M) t)
  | 0, p, q, hr => by
    apply no_rational_seed_with_polynomial_pair hL M h1 hw hd P N hN hfirst hgap p q
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro j
    simpa [shiftWord] using hr.2.2 j
  | t + 1, p, q, hr =>
    no_rational_seed_with_shifted_polynomial_pair hL M h1 hw hd P N hN hfirst hgap t
      (invBranchNum (Morphism.parityWord M t) p q) (invBranchDen (Morphism.parityWord M t) q)
      (realizes_shiftWord_pred (Morphism.parity_binary M t) hr)

theorem no_eventually_shifted_polynomial_pair_itinerary {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (P : PolynomialPair) (N : Nat) (hN : P.degree ≤ N)
    (hfirst : P.First (Morphism.parityWord M) N) (hgap : P.Gap M N)
    (s t : Nat) (p q : Int) (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = Morphism.parityWord M (t + j)) := by
  intro ht
  apply no_rational_seed_with_shifted_polynomial_pair hL M h1 hw hd P N hN hfirst hgap t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

end CollatzLab
