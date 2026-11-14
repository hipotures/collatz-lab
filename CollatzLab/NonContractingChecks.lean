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
