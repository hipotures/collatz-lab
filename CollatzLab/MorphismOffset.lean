import CollatzLab.MorphismParameters

/-! Exact first-disagreement valuation of equal-weight Collatz offsets. -/
namespace CollatzLab.Morphism

theorem weight_segment (v : Nat → Bool) (m : Nat) : ∀ n,
    weight v (m + n) = weight v m + weight (fun j => v (m + j)) n
  | 0 => by simp [weight]
  | n + 1 => by rw [Nat.add_succ, weight, weight_segment, weight]; omega

theorem offset_segment (v : Nat → Bool) (m : Nat) : ∀ n,
    offset v (m + n) = (3 : Int) ^ (weight (fun j => v (m + j)) n) * offset v m +
      (2 : Int) ^ m * offset (fun j => v (m + j)) n
  | 0 => by simp [offset, weight, Int.pow_zero]
  | n + 1 => by
    rw [Nat.add_succ, offset, offset_segment]
    cases hb : v (m + n) <;> simp only [offset, weight, hb, Bool.false_eq_true,
      if_false, if_true, Nat.add_zero]
    rw [Int.pow_succ, int_pow_add]
    family_ring

theorem common_prefix (v w : Nat → Bool) : ∀ n,
    (∀ j, j < n → v j = w j) → weight v n = weight w n ∧ offset v n = offset w n
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, he => by
    rcases common_prefix v w n (fun j hj => he j (by omega)) with ⟨hw, hc⟩
    simp [weight, offset, hw, hc, he n (by omega)]

theorem offset_parity (v : Nat → Bool) : ∀ n, 1 ≤ n → offset v n % 2 = bit (v 0)
  | 0, hn => by omega
  | 1, _ => by cases hb : v 0 <;> simp [offset, bit, hb]
  | n + 2, _ => by
    have hi := offset_parity v (n + 1) (by omega)
    cases hb : v (n + 1)
    · rw [offset, if_neg (by simp [hb])]
      exact hi
    · rw [offset, if_pos hb, Int.add_emod, Int.mul_emod, hi, Int.pow_succ, Int.mul_emod]
      cases hv : v 0 <;> simp [bit, hv]

/-- An explicit odd integer quotient, valid for both signs of the offset difference. -/
theorem offset_difference (v w : Nat → Bool) (L s : Nat) (hs : s < L)
    (hp : ∀ j, j < s → v j = w j) (hd : v s ≠ w s)
    (hw : weight v L = weight w L) :
    ∃ kappa : Int, kappa % 2 = 1 ∧ offset v L - offset w L = (2 : Int) ^ s * kappa := by
  let v' := fun j => v (s + j)
  let w' := fun j => w (s + j)
  rcases common_prefix v w s hp with ⟨hweight, hoffset⟩
  have hvw := weight_segment v s (L - s)
  have hww := weight_segment w s (L - s)
  rw [Nat.add_sub_of_le (by omega)] at hvw hww
  have htail : weight v' (L - s) = weight w' (L - s) := by
    dsimp [v', w']; omega
  have hv := offset_segment v s (L - s)
  have hw' := offset_segment w s (L - s)
  rw [Nat.add_sub_of_le (by omega)] at hv hw'
  change offset v L = (3 : Int) ^ weight v' (L - s) * offset v s +
    (2 : Int) ^ s * offset v' (L - s) at hv
  change offset w L = (3 : Int) ^ weight w' (L - s) * offset w s +
    (2 : Int) ^ s * offset w' (L - s) at hw'
  refine ⟨offset v' (L - s) - offset w' (L - s), ?_, ?_⟩
  · have h0 := offset_parity v' (L - s) (by omega)
    have h1 := offset_parity w' (L - s) (by omega)
    change offset v' (L - s) % 2 = bit (v s) at h0
    change offset w' (L - s) % 2 = bit (w s) at h1
    cases hv : v s <;> cases hw : w s <;> simp [hv, hw] at hd
    all_goals simp [bit, hv, hw] at h0 h1; omega
  · rw [hv, hw', htail, hoffset]
    family_ring

theorem disagreement_exists {L : Nat} (M : Images L) (hd : M.zero ≠ M.one) :
    ∃ j, j < L ∧ (image M false j != image M true j) = true := by
  classical
  by_cases he : ∃ j, j < L ∧ (image M false j != image M true j) = true
  · exact he
  · apply False.elim
    apply hd
    funext j
    have hh : image M false j.val = image M true j.val := by
      by_cases h : image M false j.val = image M true j.val
      · exact h
      · have hn : (image M false j.val != image M true j.val) = true := by simp [h]
        exact False.elim (he ⟨j.val, j.isLt, hn⟩)
    simpa [image, j.isLt] using hh

/-- The paper's exact `v2(c0-c1)=s` as an odd-multiple certificate. -/
theorem offsets_odd_multiple {L : Nat} (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) :
    ∃ kappa : Int, kappa % 2 = 1 ∧ c M false - c M true = (2 : Int) ^ s M * kappa := by
  have hex := disagreement_exists M hd
  have hs : s M < L := firstIndex_lt _ _ hex
  have hsval := firstIndex_hit (fun j => image M false j != image M true j) L hs
  change (image M false (s M) != image M true (s M)) = true at hsval
  apply offset_difference _ _ L (s M) hs
  · intro j hj
    have hh := before_firstIndex (fun j => image M false j != image M true j) L j hj
    cases h0 : image M false j <;> cases h1 : image M true j <;> simp [h0, h1] at hh ⊢
  · cases h0 : image M false (s M) <;> cases h1 : image M true (s M) <;>
      simp [h0, h1] at hsval ⊢
  · exact hw

/-- The periodic image of `1` first disagrees at exactly `L*t+s`. -/
theorem first_disagreement {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) :
    (∀ n, n < N M → word M n = image M true (n % L)) ∧
      word M (N M) ≠ image M true (N M % L) := by
  have ht := (t_bounds hL M h1 hw hd).2
  have hs : s M < L := firstIndex_lt _ _ (disagreement_exists M hd)
  have htz : word M (t M) = false := by
    rw [word_first_block hL M h1 _ ht]
    have hh := firstIndex_hit (fun j => !(image M true j)) L ht
    change (!(image M true (t M))) = true at hh
    cases he : image M true (t M) <;> simp [he] at hh ⊢
  have hbefore : ∀ j, j < t M → word M j = true := by
    intro j hj
    rw [word_first_block hL M h1 j (by omega)]
    have hh := before_firstIndex (fun j => !(image M true j)) L j hj
    cases he : image M true j <;> simp [he] at hh ⊢
  constructor
  · intro n hn
    have hq : n / L < t M + 1 := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      dsimp [N] at hn
      rw [Nat.mul_comm (t M + 1) L, Nat.mul_succ]
      omega
    rw [word_rec hL M h1]
    by_cases hlt : n / L < t M
    · rw [hbefore _ hlt]
    · have heq : n / L = t M := by omega
      have hm : n % L < s M := by
        have hh := Nat.mod_add_div n L
        rw [heq] at hh
        dsimp [N] at hn
        omega
      rw [heq, htz]
      have hh := before_firstIndex (fun j => image M false j != image M true j) L (n % L) hm
      cases h0 : image M false (n % L) <;> cases h1 : image M true (n % L) <;>
        simp [h0, h1] at hh ⊢
  · have hn : N M = L * t M + s M := rfl
    rw [hn, word_block hL M h1 _ _ hs, htz]
    have hm : (L * t M + s M) % L = s M := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
    rw [hm]
    have hh := firstIndex_hit (fun j => image M false j != image M true j) L hs
    change (image M false (s M) != image M true (s M)) = true at hh
    cases h0 : image M false (s M) <;> cases h1 : image M true (s M) <;>
      simp [h0, h1] at hh ⊢

end CollatzLab.Morphism
