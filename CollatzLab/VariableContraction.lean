import CollatzLab.MorphismOffset

/-! Exact signed integer bounds for recurrences with variable multipliers. -/
namespace CollatzLab

/-- A uniformly contracting variable multiplier and bounded signed forcing keep
all integer states inside the explicit interval of radius `absInt (y 0) + C`. -/
theorem variable_contracting_recurrence_bounded (A Bmax C : Int)
    (hBA : Bmax < A) (hC : 0 ≤ C) (B y d : Nat → Int)
    (hB : ∀ n, 0 ≤ B n ∧ B n ≤ Bmax)
    (hd : ∀ n, -C ≤ d n ∧ d n ≤ C)
    (hr : ∀ n, A * y (n + 1) = B n * y n + d n) :
    ∀ n, -(absInt (y 0) + C) ≤ y n ∧ y n ≤ absInt (y 0) + C := by
  let K := absInt (y 0) + C
  have hK : 0 ≤ K := by have := absInt_nonneg (y 0); dsimp [K]; omega
  intro n
  induction n with
  | zero => unfold absInt; split <;> omega
  | succ n ih =>
    change -K ≤ y n ∧ y n ≤ K at ih
    have hBn := hB n
    have hg := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ A - B n by omega) hK
    have hgap : C ≤ (A - B n) * K := by
      dsimp [K] at *
      have := absInt_nonneg (y 0)
      omega
    have hlo := Int.mul_le_mul_of_nonneg_left ih.1 hBn.1
    have hhi := Int.mul_le_mul_of_nonneg_left ih.2 hBn.1
    have hh := hr n
    have hd' := hd n
    have hu : A * y (n + 1) ≤ A * K := by
      simp only [Int.sub_mul] at hgap
      omega
    have hl : A * (-K) ≤ A * y (n + 1) := by
      simp only [Int.sub_mul] at hgap
      rw [Int.mul_neg] at hlo ⊢
      omega
    exact ⟨Int.le_of_mul_le_mul_left hl (by omega),
      Int.le_of_mul_le_mul_left hu (by omega)⟩

end CollatzLab
