import CollatzLab.FrontierSix

/-! Independent literal substitution and actual signed finite-prefix witnesses. -/
namespace CollatzLab.FrontierSixChecks
open Morphism

def literalStep (xs : List Int) : List Int :=
  xs.flatMap (fun b => if b = 1 then [1, 0, 0, 1, 1, 1] else [1, 1, 1, 1, 1, 0])

def literalIter : Nat → List Int
  | 0 => [1]
  | k + 1 => literalStep (literalIter k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem literal_semantics :
    (List.range 6).map (parityWord frontierSix) = literalIter 1 ∧
    (List.range 36).map (parityWord frontierSix) = literalIter 2 ∧
    (List.range 216).map (parityWord frontierSix) = literalIter 3 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem signed_finite_semantics :
    (List.range 81).map (seedParity 1 553314936599421495781373) = (literalIter 3).take 81 ∧
    numIter 1 553314936599421495781373 81 = 119765852333396201932225031 ∧
    (List.range 81).map (seedParity 5 (-2069128595461409219917839)) = (literalIter 3).take 81 ∧
    numIter 5 (-2069128595461409219917839) 81 = -447866004387740064765897887 ∧
    (List.range 81).map (seedParity 15 (-6207385786384227659753517)) = (literalIter 3).take 81 := by decide

end CollatzLab.FrontierSixChecks
