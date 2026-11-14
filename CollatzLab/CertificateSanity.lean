import CollatzLab.PolynomialCertificate

/-! The finite coefficient and strict-gap inputs force the advertised polynomial nonzero conditions. -/
namespace CollatzLab.PolynomialPair
open CollatzLab.Family

theorem convolution_zero_coefficients (p v : Nat → Int) : ∀ count,
    (∀ j, j < count → p j = 0) → ∀ n, convolution p v count n = 0
  | 0, _, _ => rfl
  | count + 1, hp, n => by
    rw [convolution, convolution_zero_coefficients p v count (by intro j hj; exact hp j (by omega)),
      hp count (by omega), Int.zero_mul, Int.add_zero]

theorem residual_of_zero_denominator (P : PolynomialPair) (v : Nat → Int)
    (hp : ∀ j, j ≤ P.degree → P.p1 j = 0) (n : Nat) :
    P.residual v n = cutoff P.degree P.p0 n := by
  unfold residual
  rw [convolution_zero_coefficients P.p1 v (P.degree + 1)
    (by intro j hj; exact hp j (by omega)) n, Int.add_zero]

/-- The finite first-residual condition by itself already excludes the zero polynomial pair. -/
theorem first_pair_nonzero (P : PolynomialPair) (v : Nat → Int) (N : Nat) (hf : P.First v N) :
    (∃ j, j ≤ P.degree ∧ P.p0 j ≠ 0) ∨ (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) := by
  classical
  by_cases h0 : ∃ j, j ≤ P.degree ∧ P.p0 j ≠ 0
  · exact Or.inl h0
  · by_cases h1 : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0
    · exact Or.inr h1
    · have hz1 : ∀ j, j ≤ P.degree → P.p1 j = 0 := by
        intro j hj
        by_cases h : P.p1 j = 0
        · exact h
        · exact False.elim (h1 ⟨j, hj, h⟩)
      have hz0 : ∀ j, j ≤ P.degree → P.p0 j = 0 := by
        intro j hj
        by_cases h : P.p0 j = 0
        · exact h
        · exact False.elim (h0 ⟨j, hj, h⟩)
      have hr := residual_of_zero_denominator P v hz1 N
      have hn : P.residual v N = 0 := by
        rw [hr]
        unfold cutoff
        split
        · exact hz0 N (by assumption)
        · rfl
      exact False.elim (hf.2 hn)

theorem first_zero_denominator_order (P : PolynomialPair) (v : Nat → Int) (N : Nat)
    (hf : P.First v N) (hp : ∀ j, j ≤ P.degree → P.p1 j = 0) : N ≤ P.degree := by
  by_cases hn : N ≤ P.degree
  · exact hn
  · have hr := residual_of_zero_denominator P v hp N
    rw [cutoff, if_neg hn] at hr
    exact False.elim (hf.2 hr)

/-- No irrationality or realization hypothesis is used to derive the nonzero denominator. -/
theorem first_gap_denominator_nonzero {L : Nat} (M : Morphism.Images L)
    (P : PolynomialPair) (v : Nat → Int) (N : Nat) (hf : P.First v N) (hg : P.Gap M N) :
    ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro hn
  have hz : ∀ j, j ≤ P.degree → P.p1 j = 0 := by
    intro j hj
    by_cases h : P.p1 j = 0
    · exact h
    · exact False.elim (hn ⟨j, hj, h⟩)
  have hN := first_zero_denominator_order P v N hf hz
  let cost := P.degree * (L - 1) + L + Morphism.e M
  have hbase : (2 : Int) ^ L ≤ Morphism.m M := Int.le_max_left _ _
  have hp := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := 2) (by decide) L) hbase cost
  rw [int_pow_mul] at hp
  have hc : N * (L - 1) ≤ cost := by
    have hm := Nat.mul_le_mul_right (L - 1) hN
    dsimp [cost]
    omega
  have he : L * (L - 1) * N ≤ L * cost := by
    have hm := Nat.mul_le_mul_left L hc
    have hr : L * (N * (L - 1)) = L * (L - 1) * N := by ac_rfl
    rw [hr] at hm
    exact hm
  have hm := pow_mono_exp (x := (2 : Int)) (by decide) he
  have hlo := Int.le_trans hm hp
  change Morphism.m M ^ cost < (2 : Int) ^ (L * (L - 1) * N) at hg
  omega

end CollatzLab.PolynomialPair
