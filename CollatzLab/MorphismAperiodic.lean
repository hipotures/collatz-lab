import CollatzLab.Subcritical
import Init.Data.Nat.Gcd

/-! Distinct equal-weight images force aperiodicity of their fixed point. -/
namespace CollatzLab.Morphism

theorem image_injective {L : Nat} (M : Images L) (hd : M.zero ≠ M.one) (b c : Bool)
    (he : ∀ j, j < L → image M b j = image M c j) : b = c := by
  cases b <;> cases c
  · rfl
  · apply False.elim; apply hd; funext j
    simpa [image, j.isLt] using he j.val j.isLt
  · apply False.elim; apply hd; funext j
    have hh : M.one j = M.zero j := by simpa [image, j.isLt] using he j.val j.isLt
    exact hh.symm
  · rfl

theorem period_multiple {L : Nat} (M : Images L) (p start : Nat)
    (hper : ∀ n, start ≤ n → word M (n + p) = word M n) :
    ∀ t n, start ≤ n → word M (n + p * t) = word M n
  | 0, n, _ => by simp
  | t + 1, n, hn => by
    have he : n + p * (t + 1) = (n + p * t) + p := by rw [Nat.mul_succ]; omega
    rw [he, hper _ (by omega), period_multiple M p start hper t n hn]

theorem period_weight_repeat {L : Nat} (M : Images L) (p start : Nat)
    (hper : ∀ n, start ≤ n → word M (n + p) = word M n) (a : Nat) (ha : start ≤ a) :
    ∀ t, weight (fun j => word M (a + j)) (p * t) = t * weight (fun j => word M (a + j)) p
  | 0 => by simp [weight]
  | t + 1 => by
    rw [Nat.mul_succ, weight_segment, period_weight_repeat M p start hper a ha t]
    have hh : weight (fun j => word M (a + (p * t + j))) p = weight (fun j => word M (a + j)) p := by
      apply (common_prefix _ _ p ?_).1
      intro j _
      have hp := period_multiple M p start hper t (a + j) (by omega)
      rw [show a + j + p * t = a + (p * t + j) by omega] at hp
      exact hp
    rw [hh, Nat.succ_mul]

theorem word_weight_blocks {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L) : ∀ n,
    weight (word M) (L * n) = n * weight (image M true) L
  | 0 => by simp [weight]
  | n + 1 => by
    rw [Nat.mul_succ, weight_segment, word_weight_blocks hL M h1 hw n]
    have hh : weight (fun j => word M (L * n + j)) L = weight (image M (word M n)) L := by
      exact (common_prefix _ _ L (fun j hj => word_block hL M h1 n j hj)).1
    rw [hh]
    cases hb : word M n
    · rw [hw, Nat.succ_mul]
    · rw [Nat.succ_mul]

theorem period_balance {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L) (p start : Nat)
    (hper : ∀ n, start ≤ n → word M (n + p) = word M n) :
    ∃ c, p * weight (image M true) L = L * c := by
  have hstart : start ≤ L * start := by
    have hh := Nat.mul_le_mul_right start (show 1 ≤ L by omega)
    simpa using hh
  have hr := period_weight_repeat M p start hper (L * start) hstart L
  have hs := weight_segment (word M) (L * start) (L * p)
  rw [show L * start + L * p = L * (start + p) by rw [Nat.mul_add],
    word_weight_blocks hL M h1 hw, word_weight_blocks hL M h1 hw] at hs
  rw [Nat.mul_comm p L] at hr
  refine ⟨weight (fun j => word M (L * start + j)) p, ?_⟩
  rw [Nat.add_mul] at hs
  omega

theorem period_gcd_descent {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hd : M.zero ≠ M.one) (p start : Nat)
    (hper : ∀ n, start ≤ n → word M (n + p) = word M n) :
    ∀ n, start ≤ n → word M (n + p / Nat.gcd L p) = word M n := by
  let g := Nat.gcd L p
  let a := L / g
  let q := p / g
  have hLdiv : g * a = L := Nat.mul_div_cancel' (Nat.gcd_dvd_left L p)
  have hpdiv : g * q = p := Nat.mul_div_cancel' (Nat.gcd_dvd_right L p)
  have hshift : L * q = p * a := by rw [← hLdiv, ← hpdiv]; ac_rfl
  intro n hn
  apply image_injective M hd
  intro j hj
  have hstart : start ≤ L * n + j := by
    have hh := Nat.mul_le_mul_right n (show 1 ≤ L by omega)
    simp only [Nat.one_mul] at hh
    omega
  have hh := period_multiple M p start hper a (L * n + j) hstart
  have he : L * n + j + p * a = L * (n + q) + j := by rw [Nat.mul_add, hshift]; omega
  rw [he, word_block hL M h1 _ _ hj, word_block hL M h1 _ _ hj] at hh
  exact hh

theorem not_periodic_from {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → word M (n + p) = word M n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    by_cases hg : Nat.gcd L p = 1
    · rcases period_balance hL M h1 hw p start hper with ⟨c, hc⟩
      have hdiv : L ∣ weight (image M true) L * p := by
        refine ⟨c, ?_⟩
        rw [Nat.mul_comm]
        exact hc
      have hG := Nat.gcd_mul_dvd_mul_gcd L (weight (image M true) L) p
      rw [Nat.gcd_eq_left hdiv, hg, Nat.mul_one] at hG
      have hwr : L ∣ weight (image M true) L := Nat.dvd_trans hG (Nat.gcd_dvd_right L _)
      have hrpos := weight_positive hL M h1
      have hrlt := weight_lt_length M hw hd
      have hh := Nat.le_of_dvd (by omega : 0 < weight (image M true) L) hwr
      omega
    · have hgpos : 0 < Nat.gcd L p := Nat.gcd_pos_of_pos_left p (by omega)
      have hqpos : 1 ≤ p / Nat.gcd L p := Nat.div_gcd_pos_of_pos_right L (by omega)
      have hqlt : p / Nat.gcd L p < p := Nat.div_lt_self (by omega) (by omega)
      exact ih _ hqlt start hqpos (period_gcd_descent hL M h1 hd p start hper)

theorem not_eventually_periodic {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) : ¬ EventuallyPeriodic (parityWord M) := by
  rintro ⟨start, p, hp, hper⟩
  apply not_periodic_from hL M h1 hw hd p start hp
  intro n hn
  have hh := hper n hn
  unfold parityWord bit at hh
  cases h0 : word M (n + p) <;> cases h1 : word M n <;> simp [h0, h1] at hh ⊢

end CollatzLab.Morphism

namespace CollatzLab

/-- Subcritical exclusion for all admissible equal-weight images, with no aperiodicity premise. -/
theorem no_rational_seed_realizes_subcritical_equal_weight {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hBA : Morphism.B M < Morphism.A L) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord M) :=
  Morphism.no_rational_seed_subcritical hL M h1 hw hBA
    (Morphism.not_eventually_periodic hL M h1 hw hd) p q

theorem no_rational_seed_realizes_shifted_subcritical_equal_weight {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hBA : Morphism.B M < Morphism.A L) :
    ∀ (t : Nat) (p q : Int), ¬ RealizesWord p q (shiftWord (Morphism.parityWord M) t)
  | 0, p, q, hr => by
    apply no_rational_seed_realizes_subcritical_equal_weight hL M h1 hw hd hBA p q
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro j
    simpa [shiftWord] using hr.2.2 j
  | t + 1, p, q, hr =>
    no_rational_seed_realizes_shifted_subcritical_equal_weight hL M h1 hw hd hBA t
      (invBranchNum (Morphism.parityWord M t) p q) (invBranchDen (Morphism.parityWord M t) q)
      (realizes_shiftWord_pred (Morphism.parity_binary M t) hr)

theorem no_eventually_shifted_subcritical_equal_weight_itinerary {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (hBA : Morphism.B M < Morphism.A L) (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = Morphism.parityWord M (t + j)) := by
  intro ht
  apply no_rational_seed_realizes_shifted_subcritical_equal_weight hL M h1 hw hd hBA t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

end CollatzLab
