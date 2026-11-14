import CollatzLab.MorphismWord

/-! An explicit rational periodic fixed point when equal weights are dropped. -/
namespace CollatzLab.Morphism

def unequalAlternating : Images 3 where
  zero := fun j => decide (j.val = 1)
  one := fun j => decide (j.val ≠ 1)

theorem unequalAlternating_prolongable_distinct : image unequalAlternating true 0 = true ∧
    unequalAlternating.zero ≠ unequalAlternating.one := by
  refine ⟨by decide, ?_⟩
  intro he
  have hh := congrArg (fun f : Fin 3 → Bool => f ⟨0, by decide⟩) he
  change false = true at hh
  contradiction

theorem unequalAlternating_word : parityWord unequalAlternating =
    fun n => if n % 2 = 0 then 1 else 0 := by
  let v := fun n => decide (n % 2 = 0)
  have hrec : ∀ n j, j < 3 → v (3 * n + j) = image unequalAlternating (v n) j := by
    intro n j hj
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hn | hn
    all_goals rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    all_goals simp [v, image, unequalAlternating, Nat.add_mod, Nat.mul_mod, hn]
  have hv := word_unique (by decide) unequalAlternating (by decide) v rfl hrec
  funext n
  unfold parityWord bit
  rw [← hv]
  by_cases hn : n % 2 = 0 <;> simp [v, hn]

theorem unequalAlternating_weights :
    weight (image unequalAlternating false) 3 = 1 ∧
    weight (image unequalAlternating true) 3 = 2 := by decide

theorem unequalAlternating_realized : RealizesWord 1 1 (parityWord unequalAlternating) := by
  have hi : ∀ n, numIter 1 1 n = if n % 2 = 0 then 1 else 2 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change numStep 1 (numIter 1 1 n) = _
      rw [ih]
      rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hn | hn
      · have hs : (n + 1) % 2 = 1 := by omega
        simp [hn, hs, numStep]
      · have hs : (n + 1) % 2 = 0 := by omega
        simp [hn, hs, numStep]
  refine ⟨by decide, by decide, ?_⟩
  intro n
  rw [unequalAlternating_word]
  unfold seedParity
  rw [hi]
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hn | hn <;> simp [hn]

end CollatzLab.Morphism
