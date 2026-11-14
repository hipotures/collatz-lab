import CollatzLab.FiniteLinear
import CollatzLab.PolynomialHeight

/-! Explicit coefficient bounds for division-free integer null vectors. -/
namespace CollatzLab.FiniteLinear
open CollatzLab.Family

def nullBound : Nat → Int → Int
  | 0, _ => 1
  | m + 1, H => ((m : Int) + 1) * H * nullBound m (2 * H * H)

theorem absInt_neg_eq (x : Int) : absInt (-x) = absInt x := by
  unfold absInt
  split <;> split <;> omega

theorem elimination_bound_positive (H : Int) (hH : 1 ≤ H) : 1 ≤ 2 * H * H := by
  have hh := Int.mul_le_mul hH hH (by decide : (0 : Int) ≤ 1) (by omega : 0 ≤ H)
  family_ring

theorem nullBound_positive : ∀ m : Nat, ∀ H : Int, 1 ≤ H → 1 ≤ nullBound m H
  | 0, _, _ => Int.le_refl _
  | m + 1, H, hH => by
    have hi := nullBound_positive m (2 * H * H) (elimination_bound_positive H hH)
    have hc := Int.mul_le_mul (show (1 : Int) ≤ (m : Int) + 1 by omega) hH
      (by decide : (0 : Int) ≤ 1) (by omega : 0 ≤ (m : Int) + 1)
    have hp := Int.mul_le_mul hc hi (by decide : (0 : Int) ≤ 1) (by omega : 0 ≤ ((m : Int) + 1) * H)
    exact hp

theorem dot_abs_bound (f x : Nat → Int) (H X : Int) (hH : 0 ≤ H) (hX : 0 ≤ X) :
    ∀ n, (∀ j, j < n → absInt (f j) ≤ H) → (∀ j, j < n → absInt (x j) ≤ X) →
      absInt (dot f x n) ≤ (n : Int) * H * X
  | 0, _, _ => by simp [dot, total, absInt]
  | n + 1, hf, hx => by
    have hi := dot_abs_bound f x H X hH hX n
      (by intro j hj; exact hf j (by omega)) (by intro j hj; exact hx j (by omega))
    have ht := Int.mul_le_mul (hf n (by omega)) (hx n (by omega)) (absInt_nonneg _) hH
    have hh := absInt_add_le (dot f x n) (f n * x n)
    rw [absInt_mul] at hh
    change absInt (dot f x n + f n * x n) ≤ _
    simp only [Int.ofNat_add, Int.ofNat_one]
    family_ring

theorem elimination_entry_bound (H a b c d : Int) (hH : 0 ≤ H)
    (ha : absInt a ≤ H) (hb : absInt b ≤ H) (hc : absInt c ≤ H) (hd : absInt d ≤ H) :
    absInt (a * b - c * d) ≤ 2 * H * H := by
  have h0 := Int.mul_le_mul ha hb (absInt_nonneg _) hH
  have h1 := Int.mul_le_mul hc hd (absInt_nonneg _) hH
  have hh := absInt_sub_le (a * b) (c * d)
  rw [absInt_mul, absInt_mul] at hh
  family_ring

/-- A quantitative version of the independent integer null-vector theorem. -/
theorem integer_null_vector_bounded : ∀ m : Nat, ∀ H : Int, 1 ≤ H →
    ∀ A : Nat → Nat → Int,
    (∀ i, i < m → ∀ j, j < m + 1 → absInt (A i j) ≤ H) →
    ∃ x : Nat → Int, (∃ j, j < m + 1 ∧ x j ≠ 0) ∧
      (∀ i, i < m → dot (A i) x (m + 1) = 0) ∧
      (∀ j, j < m + 1 → absInt (x j) ≤ nullBound m H)
  | 0, H, hH, _, _ => by
    refine ⟨fun _ => 1, ⟨0, by omega, by decide⟩, by intro i hi; omega, ?_⟩
    intro j hj
    change absInt 1 ≤ 1
    decide
  | m + 1, H, hH, A, hA => by
    classical
    by_cases hp : ∃ pivot, pivot < m + 1 ∧ A pivot 0 ≠ 0
    · rcases hp with ⟨pivot, hpivot, ha⟩
      let B := fun i j => A pivot 0 * A (skip pivot i) (j + 1) - A (skip pivot i) 0 * A pivot (j + 1)
      have hB : ∀ i, i < m → ∀ j, j < m + 1 → absInt (B i j) ≤ 2 * H * H := by
        intro i hi j hj
        have hskip : skip pivot i < m + 1 := by unfold skip; split <;> omega
        exact elimination_entry_bound H _ _ _ _ (by omega)
          (hA pivot hpivot 0 (by omega)) (hA _ hskip _ (by omega))
          (hA _ hskip 0 (by omega)) (hA pivot hpivot _ (by omega))
      rcases integer_null_vector_bounded m (2 * H * H) (elimination_bound_positive H hH) B hB with
        ⟨y, ⟨j, hj, hyj⟩, hy, hybound⟩
      let X := nullBound m (2 * H * H)
      have hX : 1 ≤ X := nullBound_positive m _ (elimination_bound_positive H hH)
      let t := dot (fun j => A pivot (j + 1)) y (m + 1)
      let x : Nat → Int := fun j => match j with
        | 0 => -t
        | j + 1 => A pivot 0 * y j
      refine ⟨x, ⟨j + 1, by omega, Int.mul_ne_zero ha hyj⟩, ?_, ?_⟩
      · intro i hi
        have hx : dot (A i) x (m + 1 + 1) = - A i 0 * t +
            A pivot 0 * dot (fun j => A i (j + 1)) y (m + 1) := by
          unfold dot
          rw [total_head]
          change A i 0 * (-t) + total (fun j => A i (j + 1) * (A pivot 0 * y j)) (m + 1) = _
          have hs := dot_right_scale (fun j => A i (j + 1)) y (A pivot 0) (m + 1)
          change total (fun j => A i (j + 1) * (A pivot 0 * y j)) (m + 1) =
            A pivot 0 * total (fun j => A i (j + 1) * y j) (m + 1) at hs
          rw [hs]
          family_ring
        rw [hx]
        by_cases he : i = pivot
        · subst i; dsimp [t]; family_ring
        · rcases skip_surjective m pivot i hpivot hi he with ⟨r, hr, her⟩
          have hh := hy r hr
          dsimp [B] at hh
          rw [her, dot_scaled_sub] at hh
          dsimp [t]
          family_ring
      · intro i hi
        cases i with
        | zero =>
          change absInt (-t) ≤ ((m : Int) + 1) * H * X
          rw [absInt_neg_eq]
          have ht := dot_abs_bound (fun j => A pivot (j + 1)) y H X (by omega) (by omega)
            (m + 1) (by intro j hj; exact hA pivot hpivot _ (by omega)) hybound
          exact ht
        | succ i =>
          change absInt (A pivot 0 * y i) ≤ ((m : Int) + 1) * H * X
          rw [absInt_mul]
          have hm := Int.mul_le_mul (hA pivot hpivot 0 (by omega)) (hybound i (by omega))
            (absInt_nonneg _) (by omega : 0 ≤ H)
          have hscale := Int.mul_le_mul_of_nonneg_right
            (show (1 : Int) ≤ (m : Int) + 1 by omega) (Int.mul_nonneg (by omega : 0 ≤ H) (by omega : 0 ≤ X))
          dsimp [X] at *
          family_ring
    · refine ⟨fun j => if j = 0 then 1 else 0, ⟨0, by omega, by decide⟩, ?_, ?_⟩
      · intro i hi
        have hz : A i 0 = 0 := by
          by_cases h : A i 0 = 0
          · exact h
          · exact False.elim (hp ⟨i, hi, h⟩)
        unfold dot
        rw [total_ext _ (fun _ => 0) _ (by
          intro j _
          by_cases hj : j = 0
          · subst j; simp [hz]
          · simp [hj]), total_zero]
      · intro j hj
        have hb := nullBound_positive (m + 1) H hH
        by_cases hz : j = 0
        · simp [hz, absInt]; exact hb
        · simp [hz, absInt]; omega

end CollatzLab.FiniteLinear
