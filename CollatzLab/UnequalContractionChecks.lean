import CollatzLab.Unequal100110
import CollatzLab.UnequalControl

/-! Independent literal substitutions and finite signed rational regressions. -/
namespace CollatzLab.UnequalContractionChecks
open Morphism

/-- Literal list substitution, independent of the indexed fixed-point evaluator. -/
def literalStep (xs : List Int) : List Int :=
  xs.flatMap (fun b => if b = 1 then [1, 0, 0] else [1, 1, 0])

def literalIter : Nat → List Int
  | 0 => [1]
  | n + 1 => literalStep (literalIter n)

theorem literal_first_three : literalIter 1 = [1,0,0] ∧
    literalIter 2 = [1,0,0,1,1,0,1,1,0] ∧
    literalIter 3 = [1,0,0,1,1,0,1,1,0,1,0,0,1,0,0,1,1,0,1,0,0,1,0,0,1,1,0] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem indexed_matches_literal :
    (List.range 3).map (parityWord unequal100110) = literalIter 1 ∧
    (List.range 9).map (parityWord unequal100110) = literalIter 2 ∧
    (List.range 27).map (parityWord unequal100110) = literalIter 3 ∧
    (List.range 81).map (parityWord unequal100110) = literalIter 4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- A genuine positive integer has the first 81 specified parity bits, without
claiming an infinite realization. No seed interval is searched. -/
theorem positive_integer_prefix :
    (List.range 81).map (seedParity 1 2301021985950669302953629) = literalIter 4 ∧
    numIter 1 2301021985950669302953629 81 = 34710635340769718209 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem signed_unreduced_prefixes :
    (List.range 81).map (seedParity 5 (-584148266392945232293615)) = literalIter 4 ∧
    (List.range 81).map (seedParity 15 (-1752444799178835696880845)) = literalIter 4 ∧
    numIter 5 (-584148266392945232293615) 81 = -8811805182005340970 ∧
    numIter 15 (-1752444799178835696880845) 81 = -26435415546016022910 := by decide

/-- Equality of reduced and unreduced signed rational itineraries is universal,
not just a finite list computation. -/
theorem signed_unreduced_equiv (n : Nat) :
    seedParity 15 (-1752444799178835696880845) n =
      seedParity 5 (-584148266392945232293615) n :=
  (numIter_equiv (p := -1752444799178835696880845) (q := 15)
    (p' := -584148266392945232293615) (q' := 5)
    (by decide) (by decide) (by decide) n).2

theorem expanding_image_and_contracting_group :
    (3 : Int) ^ weight (image unequal100110 false) 3 = 9 ∧
    (2 : Int) ^ 3 = 8 ∧
    (3 : Int) ^ weight (fun j => word unequal100110 j) 9 = 243 ∧
    offset (fun j => word unequal100110 j) 9 = 761 := by decide

/-- The previously proved rational unequal-weight example remains an explicit
negative regression for any unconditional unequal-weight exclusion. -/
theorem rational_control_preserved : RealizesWord 1 1 (parityWord unequalAlternating) :=
  unequalAlternating_realized

theorem rational_control_periodic : EventuallyPeriodic (parityWord unequalAlternating) := by
  refine ⟨0, 2, by decide, ?_⟩
  intro n _
  rw [unequalAlternating_word]
  have hh : (n + 2) % 2 = n % 2 := by omega
  simp only [hh]

end CollatzLab.UnequalContractionChecks
