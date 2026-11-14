import CollatzLab.FamilyApprox

/-! Non-unit residual coefficients become dominant after a finite tower level. -/
namespace CollatzLab
open Family

theorem nonunit_leading_valuation (v m : Nat) (hvm : v < m) (c t : Int) (hc : c % 2 = 1) :
    let E := (2 : Int) ^ v * c + (2 : Int) ^ m * t
    E ≠ 0 ∧ (2 : Int) ^ v ∣ E ∧ ¬ (2 : Int) ^ (v + 1) ∣ E ∧ (2 : Int) ^ v ≤ absInt E := by
  apply odd_multiple_bounds
  have heven := even_pow (x := 2) (by decide) (n := m - v) (by omega)
  have hprod := even_mul heven t
  refine ⟨c + (2 : Int) ^ (m - v) * t, by omega, ?_⟩
  have hm : (2 : Int) ^ m = (2 : Int) ^ v * (2 : Int) ^ (m - v) := by
    rw [← int_pow_add, Nat.add_sub_of_le (by omega)]
  rw [hm]
  family_ring

theorem finite_start_for_leading_coefficient (L : Nat) (hL : 2 ≤ L) (v : Nat) :
    ∃ k0 : Nat, ∀ k, k0 ≤ k → v < L ^ (k + 1) := by
  refine ⟨v, ?_⟩
  intro k hk
  have hh := nat_lt_pow2 (k + 1)
  have hm := Nat.pow_le_pow_left hL (k + 1)
  omega

/-- Every positive natural coefficient has a finite exact power-of-two factor. -/
theorem nat_two_power_factorization (n : Nat) : n ≠ 0 →
    ∃ v : Nat, ∃ c : Int, c % 2 = 1 ∧ (n : Int) = (2 : Int) ^ v * c := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases ho : n % 2 = 1
    · exact ⟨0, (n : Int), by omega, by simp [Int.pow_zero]⟩
    · have hsmall : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      have hnonzero : n / 2 ≠ 0 := by omega
      rcases ih (n / 2) hsmall hnonzero with ⟨v, c, hc, he⟩
      have hcast : (n : Int) = 2 * ((n / 2 : Nat) : Int) := by omega
      refine ⟨v + 1, c, hc, ?_⟩
      rw [hcast, he, Int.pow_succ]
      ac_rfl

/-- This applies to negative coefficients as well as positive ones. -/
theorem int_two_power_factorization (x : Int) (hx : x ≠ 0) :
    ∃ v : Nat, ∃ c : Int, c % 2 = 1 ∧ x = (2 : Int) ^ v * c := by
  have hpos := absInt_pos_of_ne_zero hx
  let n := (absInt x).toNat
  have hcast : (n : Int) = absInt x := Int.toNat_of_nonneg (by omega)
  have hn : n ≠ 0 := by omega
  rcases nat_two_power_factorization n hn with ⟨v, c, hc, he⟩
  rw [hcast] at he
  by_cases hs : 0 ≤ x
  · rw [absInt_of_nonneg hs] at he
    exact ⟨v, c, hc, he⟩
  · refine ⟨v, -c, by omega, ?_⟩
    simp only [absInt, hs, if_false] at he
    rw [Int.mul_neg]
    omega

/-- The strict domination condition cannot be dropped even for the coefficient 8. -/
theorem premature_valuation_counterexample : (8 : Int) + (2 : Int) ^ 2 * (-2) = 0 := by decide

end CollatzLab
