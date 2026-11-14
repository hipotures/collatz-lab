import CollatzLab.EqualWeight

/-! A uniform numerical ledger for a hypothetical degree-six, order-thirteen pair. -/
namespace CollatzLab
open Family

theorem pow_two_strict_exponent {n m : Nat} (hnm : n < m) : (2 : Int) ^ n < (2 : Int) ^ m := by
  have hp := pow_pos_of_pos (x := 2) (by decide) n
  have hm := pow_mono_exp (x := 2) (by decide) (show n + 1 ≤ m by omega)
  have hs : (2 : Int) ^ n < (2 : Int) ^ (n + 1) := by rw [Int.pow_succ]; omega
  exact Int.lt_of_lt_of_le hs hm

/-- This proves a height comparison only, not the existence of an approximant. -/
theorem degree_six_numerical_gap (L r e : Nat) (hL : 2 ≤ L) (hr : r < L) (he : e < L) :
    (max ((2 : Int) ^ L) ((3 : Int) ^ r)) ^ (6 * (L - 1) + L + e) <
      (2 : Int) ^ (13 * L * (L - 1)) := by
  let cost := 6 * (L - 1) + L + e
  let gain := 13 * L * (L - 1)
  have hcost : cost ≤ 8 * L := by dsimp [cost]; omega
  have hprod := Nat.mul_le_mul (show r ≤ L - 1 by omega) hcost
  have hm := Nat.mul_le_mul_left 8 hprod
  have heq : 8 * ((L - 1) * (8 * L)) = 64 * (L * (L - 1)) := by
    calc
      _ = (8 * 8) * (L * (L - 1)) := by ac_rfl
      _ = _ := rfl
  rw [heq] at hm
  have hgain : 5 * gain = 65 * (L * (L - 1)) := by
    dsimp [gain]
    calc
      _ = (5 * 13) * (L * (L - 1)) := by ac_rfl
      _ = _ := rfl
  have hpos : 0 < L * (L - 1) := Nat.mul_pos (by omega) (by omega)
  have hexp : 8 * (r * cost) < 5 * gain := by rw [hgain]; omega
  by_cases hAB : (2 : Int) ^ L ≤ (3 : Int) ^ r
  · rw [Int.max_def, if_pos hAB]
    let x := (2 : Int) ^ gain
    let y := ((3 : Int) ^ r) ^ cost
    have h3 := pow_le_pow_of_le (x := (3 : Int) ^ 5) (y := (2 : Int) ^ 8)
      (by decide) (by decide) (r * cost)
    rw [int_pow_mul, int_pow_mul] at h3
    have h2 := pow_two_strict_exponent hexp
    have hy : y ^ 5 = (3 : Int) ^ (5 * (r * cost)) := by
      dsimp [y]; rw [int_pow_mul, int_pow_mul]; congr 1; ac_rfl
    have hx : x ^ 5 = (2 : Int) ^ (5 * gain) := by
      dsimp [x]; rw [int_pow_mul, Nat.mul_comm]
    have hxy : y ^ 5 < x ^ 5 := by rw [hy, hx]; exact Int.lt_of_le_of_lt h3 h2
    have hxp : 0 ≤ x := pow_nonneg_of_nonneg (by decide) _
    have hresult : y < x := by
      by_cases hh : y < x
      · exact hh
      · have hm := pow_le_pow_of_le hxp (show x ≤ y by omega) 5
        omega
    exact hresult
  · rw [Int.max_def, if_neg hAB, int_pow_mul]
    have hc : cost < 13 * (L - 1) := by dsimp [cost]; omega
    have hh := Nat.mul_lt_mul_of_pos_left hc (show 0 < L by omega)
    have hid : L * (13 * (L - 1)) = gain := by dsimp [gain]; ac_rfl
    rw [hid] at hh
    exact pow_two_strict_exponent hh

namespace Morphism

theorem degree_six_ledger {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L) (hd : M.zero ≠ M.one) :
    m M ^ (6 * (L - 1) + L + e M) < (2 : Int) ^ (L * (L - 1) * 13) := by
  have hh := degree_six_numerical_gap L (weight (image M true) L) (e M) hL
    (weight_lt_length M hw hd) (se_bounds M hd).2
  have hid : 13 * L * (L - 1) = L * (L - 1) * 13 := by ac_rfl
  rw [hid] at hh
  exact hh

end Morphism
end CollatzLab
