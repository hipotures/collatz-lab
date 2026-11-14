import CollatzLab.MorphismTransport

/-! Factoring the generic Mahler multiplier and proving its odd unit. -/
namespace CollatzLab.Morphism
open CollatzLab.Family

def coeff {L : Nat} (M : Images L) (j : Nat) := bit (image M true j) - bit (image M false j)
def GammaStar {L : Nat} (M : Images L) (a b : Int) :=
  sum (fun j => coeff M (s M + j)) a b (e M - s M + 1)

theorem se_bounds {L : Nat} (M : Images L) (hd : M.zero ≠ M.one) :
    s M ≤ e M ∧ e M < L := by
  have hx := disagreement_exists M hd
  have hs : s M < L := firstIndex_lt _ _ hx
  have hh := firstIndex_hit (fun j => image M false j != image M true j) L hs
  have hl := lastIndex_spec (fun j => image M false j != image M true j) L hx
  exact ⟨hl.2.2 _ hs hh, hl.1⟩

theorem coeff_before {L : Nat} (M : Images L) (j : Nat) (hj : j < s M) : coeff M j = 0 := by
  have hh := before_firstIndex (fun j => image M false j != image M true j) L j hj
  cases h0 : image M false j <;> cases h1 : image M true j <;> simp [coeff, bit, h0, h1] at hh ⊢

theorem coeff_after {L : Nat} (M : Images L) (hd : M.zero ≠ M.one)
    (j : Nat) (hj : e M < j) (hL : j < L) : coeff M j = 0 := by
  have hl := lastIndex_spec (fun j => image M false j != image M true j) L (disagreement_exists M hd)
  by_cases he : image M false j = image M true j
  · simp [coeff, he]
  · have hh : (image M false j != image M true j) = true := by simp [he]
    have hh' : j ≤ e M := hl.2.2 j hL hh
    omega

theorem coeff_first_odd {L : Nat} (M : Images L) (hd : M.zero ≠ M.one) :
    coeff M (s M) % 2 = 1 := by
  have hs : s M < L := firstIndex_lt _ _ (disagreement_exists M hd)
  have hh := firstIndex_hit (fun j => image M false j != image M true j) L hs
  change (image M false (s M) != image M true (s M)) = true at hh
  cases h0 : image M false (s M) <;> cases h1 : image M true (s M) <;>
    simp [coeff, bit, h0, h1] at hh ⊢

theorem sum_support_factor (v : Nat → Int) (a b : Int) (L s e : Nat)
    (hs : s ≤ e) (he : e < L)
    (hlo : ∀ j, j < s → v j = 0)
    (hhi : ∀ j, e < j → j < L → v j = 0) :
    sum v a b L = a ^ s * b ^ (L - 1 - e) *
      sum (fun j => v (s + j)) a b (e - s + 1) := by
  have hlow : sum v a b s = 0 := by
    rw [sum_ext v (fun _ => 0) a b s hlo, sum_zero]
  have hhigh : sum (fun j => v (e + 1 + j)) a b (L - (e + 1)) = 0 := by
    rw [sum_ext _ (fun _ => 0) a b _ (by intro j hj; exact hhi _ (by omega) (by omega)), sum_zero]
  have hsplit := prefix_segment v a b (e + 1) (L - (e + 1))
  rw [Nat.add_sub_of_le (by omega), hhigh, Int.mul_zero, Int.add_zero] at hsplit
  have hmiddle := prefix_segment v a b s (e - s + 1)
  rw [show s + (e - s + 1) = e + 1 by omega, hlow, Int.mul_zero, Int.zero_add] at hmiddle
  rw [hsplit, hmiddle, show L - (e + 1) = L - 1 - e by omega]
  ac_rfl

theorem gamma_factor {L : Nat} (M : Images L) (hd : M.zero ≠ M.one) (a b : Int) :
    Gamma M a b = a ^ s M * b ^ (L - 1 - e M) * GammaStar M a b := by
  have hg : Gamma M a b = sum (coeff M) a b L := by
    exact (sum_sub (fun j => bit (image M true j)) (fun j => bit (image M false j)) a b L).symm
  rw [hg]
  exact sum_support_factor (coeff M) a b L (s M) (e M) (se_bounds M hd).1
    (se_bounds M hd).2 (coeff_before M) (coeff_after M hd)

theorem sum_odd (v : Nat → Int) (a b : Int) (ha : a % 2 = 0) (hb : b % 2 = 1)
    (hv : v 0 % 2 = 1) : ∀ n, 1 ≤ n → sum v a b n % 2 = 1
  | 0, hn => by omega
  | 1, _ => by simpa [sum, Int.pow_zero] using hv
  | n + 2, _ => by
    have hi := sum_odd v a b ha hb hv (n + 1) (by omega)
    have hp : (v (n + 1) * a ^ (n + 1)) % 2 = 0 := by
      rw [Int.mul_emod, even_pow ha (by omega)]; simp
    rw [sum, Int.add_emod, hp, Int.mul_emod, hi, hb]
    decide

theorem gammaStar_odd {L : Nat} (M : Images L) (hd : M.zero ≠ M.one)
    (a b : Int) (ha : a % 2 = 0) (hb : b % 2 = 1) :
    GammaStar M a b % 2 = 1 ∧ GammaStar M a b ≠ 0 := by
  have hh : GammaStar M a b % 2 = 1 :=
    sum_odd _ a b ha hb (by simpa using coeff_first_odd M hd) _ (by omega)
  exact ⟨hh, by omega⟩

theorem one_pow_int : ∀ n : Nat, (1 : Int) ^ n = 1
  | 0 => rfl
  | n + 1 => by rw [Int.pow_succ, one_pow_int]; rfl

theorem weight_sum (v : Nat → Bool) : ∀ n,
    sum (fun j => bit (v j)) 1 1 n = (weight v n : Int)
  | 0 => rfl
  | n + 1 => by
    rw [sum, weight_sum]
    cases hb : v n <;> simp [weight, bit, hb, Int.ofNat_add, one_pow_int]

theorem s_lt_e {L : Nat} (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) : s M < e M := by
  have hs := (se_bounds M hd).1
  by_cases he : s M = e M
  · have hh := gamma_factor M hd 1 1
    have hz : Gamma M 1 1 = 0 := by unfold Gamma Q; rw [weight_sum, weight_sum, hw]; omega
    have hodd := coeff_first_odd M hd
    rw [hz] at hh
    simp [GammaStar, ← he, sum, Int.pow_zero, one_pow_int] at hh
    omega
  · omega

end CollatzLab.Morphism
