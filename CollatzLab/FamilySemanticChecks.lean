import CollatzLab.FamilyChecks

/-! Independent literal substitutions and signed rational witnesses for Phase 7. -/
namespace CollatzLab.Phase7Audit

def literalImage (L : Nat) (b : Int) : List Int :=
  if b = 1 then List.replicate (L - 1) 1 ++ [0]
  else List.replicate (L - 2) 1 ++ [0, 1]

def literalIter (L : Nat) : Nat → List Int
  | 0 => [1]
  | n + 1 => (literalIter L n).flatMap (literalImage L)

theorem literal_four : (List.range 16).map (familyWord 4) = literalIter 4 2 := by decide
theorem literal_five : (List.range 25).map (familyWord 5) = literalIter 5 2 := by decide
theorem literal_six : (List.range 36).map (familyWord 6) = literalIter 6 2 := by decide

set_option maxRecDepth 100000 in
theorem signed_prefix_witnesses :
    (List.range 16).map (seedParity 5 (-201085)) = literalIter 4 2 ∧
    (List.range 25).map (seedParity 5 (-38519125)) = literalIter 5 2 ∧
    (List.range 36).map (seedParity 5 (-325841652965)) = literalIter 6 2 ∧
    (List.range 36).map (seedParity 15 (-977524958895)) = literalIter 6 2 := by decide

set_option maxRecDepth 100000 in
theorem positive_prefix_witnesses :
    (List.range 16).map (seedParity 1 25319) = literalIter 4 2 ∧
    (List.range 25).map (seedParity 1 25850607) = literalIter 5 2 ∧
    (List.range 36).map (seedParity 1 3551146143) = literalIter 6 2 := by decide

theorem signed_branch_checks :
    numStep 3 (-5) = -6 ∧ numStep 3 (-4) = -2 ∧
    numStep 9 (-15) = -18 ∧ seedParity 3 (-5) 0 = 1 := by decide

/-- The infinite predicate is satisfiable with a negative unreduced numerator. -/
theorem negative_realization : RealizesWord (-5) 5 (fun _ => 1) := by
  refine ⟨by decide, by decide, ?_⟩
  have hi : ∀ n, numIter 5 (-5) n = -5 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change numStep 5 (numIter 5 (-5) n) = -5; rw [ih]; rfl
  intro n
  simp [seedParity, hi]

/-- Concrete controls detect the first difference, including its zero-based index. -/
theorem disagreement_controls :
    familyWord 4 14 = 0 ∧ familyWord 5 23 = 0 ∧ familyWord 6 34 = 0 ∧
    14 % 4 ≠ 3 ∧ 23 % 5 ≠ 4 ∧ 34 % 6 ≠ 5 := by decide

end CollatzLab.Phase7Audit
