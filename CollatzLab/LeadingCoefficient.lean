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

/-- The strict domination condition cannot be dropped even for the coefficient 8. -/
theorem premature_valuation_counterexample : (8 : Int) + (2 : Int) ^ 2 * (-2) = 0 := by decide

end CollatzLab
