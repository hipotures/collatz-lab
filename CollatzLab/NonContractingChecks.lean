import CollatzLab.NonContracting110111
import CollatzLab.UnequalControl

/-! Independent literal evaluation and preserved rational controls. -/
namespace CollatzLab.NonContractingChecks
open Morphism

def literalStep (xs : List Int) : List Int :=
  xs.flatMap (fun b => if b = 1 then [1, 1, 0] else [1, 1, 1])

def literalIter : Nat → List Int
  | 0 => [1]
  | k + 1 => literalStep (literalIter k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem literal_semantics :
    literalIter 2 = [1,1,0,1,1,0,1,1,1] ∧
    (List.range 3).map (parityWord nonContracting110111) = literalIter 1 ∧
    (List.range 9).map (parityWord nonContracting110111) = literalIter 2 ∧
    (List.range 27).map (parityWord nonContracting110111) = literalIter 3 ∧
    (List.range 81).map (parityWord nonContracting110111) = literalIter 4 := by decide

theorem rational_control_preserved : RealizesWord 1 1 (parityWord unequalAlternating) :=
  unequalAlternating_realized

end CollatzLab.NonContractingChecks

namespace CollatzLab.NonContractingChecks
open Morphism

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem signed_finite_semantics :
    (List.range 81).map (seedParity 1 721013141537229946329339) = literalIter 4 ∧
    numIter 1 721013141537229946329339 81 = 37923644741691456159576389081 ∧
    (List.range 81).map (seedParity 5 (-1230637570772366967178009)) = literalIter 4 ∧
    numIter 5 (-1230637570772366967178009) 81 = -64728725942839940287884653801 ∧
    (List.range 81).map (seedParity 15 (-3691912712317100901534027)) = literalIter 4 := by decide

end CollatzLab.NonContractingChecks

namespace CollatzLab.NonContractingChecks

/-- A supercritical word with arbitrarily long squares can have a rational seed:
independent aperiodicity cannot be removed from the new theorem. -/
theorem all_one_rational_control : RealizesWord (-1) 1 (fun _ => 1) ∧
    EventuallyPeriodic (fun _ => 1) := by
  have hi : ∀ n, numIter 1 (-1) n = -1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change numStep 1 (numIter 1 (-1) n) = -1; rw [ih]; rfl
  constructor
  · refine ⟨by decide, by decide, ?_⟩
    intro n
    simp [seedParity, hi]
  · exact ⟨0, 1, by decide, by intro _ _; rfl⟩

end CollatzLab.NonContractingChecks
