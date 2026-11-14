import CollatzLab.FamilyPrefix

/-! Finite integer linear algebra without division or additional dependencies. -/
namespace CollatzLab.FiniteLinear
open CollatzLab.Family

def total (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => total f n + f n

def dot (a x : Nat → Int) (n : Nat) : Int := total (fun j => a j * x j) n

theorem total_ext (f g : Nat → Int) : ∀ n,
    (∀ j, j < n → f j = g j) → total f n = total g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [total, total, total_ext f g n (by intro j hj; exact h j (by omega)), h n (by omega)]

theorem total_zero : ∀ n, total (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [total, total_zero]; rfl

theorem total_head (f : Nat → Int) : ∀ n,
    total f (n + 1) = f 0 + total (fun j => f (j + 1)) n
  | 0 => by simp [total]
  | n + 1 => by rw [total, total_head f n, total]; omega

theorem total_scaled_sub (f g : Nat → Int) (a b : Int) : ∀ n,
    total (fun j => a * f j - b * g j) n = a * total f n - b * total g n
  | 0 => by simp [total]
  | n + 1 => by rw [total, total_scaled_sub, total, total]; family_ring

theorem dot_scaled_sub (f g x : Nat → Int) (a b : Int) (n : Nat) :
    dot (fun j => a * f j - b * g j) x n = a * dot f x n - b * dot g x n := by
  have he : (fun j => (a * f j - b * g j) * x j) =
      (fun j => a * (f j * x j) - b * (g j * x j)) := by
    funext j; family_ring
  unfold dot
  rw [he, total_scaled_sub]

theorem dot_right_scale (f x : Nat → Int) (a : Int) (n : Nat) :
    dot f (fun j => a * x j) n = a * dot f x n := by
  have hh := total_scaled_sub (fun j => f j * x j) (fun _ => 0) a 0 n
  simp only [Int.zero_mul, Int.sub_zero] at hh
  unfold dot
  rw [← hh]
  apply total_ext
  intro j _; dsimp only; ac_rfl

def skip (pivot i : Nat) : Nat := if i < pivot then i else i + 1

theorem skip_surjective (m pivot i : Nat) (hp : pivot < m + 1)
    (hi : i < m + 1) (hne : i ≠ pivot) : ∃ j, j < m ∧ skip pivot j = i := by
  by_cases h : i < pivot
  · exact ⟨i, by omega, by simp [skip, h]⟩
  · exact ⟨i - 1, by omega, by simp [skip, show ¬ i - 1 < pivot by omega]; omega⟩

/-- Every integer matrix with `m` rows and `m+1` columns has a nonzero integer kernel vector. -/
theorem integer_null_vector : ∀ m : Nat, ∀ A : Nat → Nat → Int,
    ∃ x : Nat → Int, (∃ j, j < m + 1 ∧ x j ≠ 0) ∧
      (∀ i, i < m → dot (A i) x (m + 1) = 0)
  | 0, _ => ⟨fun _ => 1, ⟨0, by omega, by decide⟩, by intro i hi; omega⟩
  | m + 1, A => by
    classical
    by_cases hp : ∃ pivot, pivot < m + 1 ∧ A pivot 0 ≠ 0
    · rcases hp with ⟨pivot, hpivot, ha⟩
      let B := fun i j => A pivot 0 * A (skip pivot i) (j + 1) - A (skip pivot i) 0 * A pivot (j + 1)
      rcases integer_null_vector m B with ⟨y, ⟨j, hj, hyj⟩, hy⟩
      let t := dot (fun j => A pivot (j + 1)) y (m + 1)
      let x : Nat → Int := fun j => match j with
        | 0 => -t
        | j + 1 => A pivot 0 * y j
      refine ⟨x, ⟨j + 1, by omega, ?_⟩, ?_⟩
      · change A pivot 0 * y j ≠ 0
        exact Int.mul_ne_zero ha hyj
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
    · refine ⟨fun j => if j = 0 then 1 else 0, ⟨0, by omega, by decide⟩, ?_⟩
      intro i hi
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

end CollatzLab.FiniteLinear
