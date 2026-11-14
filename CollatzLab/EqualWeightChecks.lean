import CollatzLab.EqualWeight

/-! Non-vacuity and a reversed base-order instance with genuine cancellation. -/
namespace CollatzLab.Morphism

def reverseOrder : Images 4 where
  zero := fun j => decide (j.val = 0 ∨ j.val = 2)
  one := fun j => decide (j.val < 2)

theorem reverseOrder_admissible : image reverseOrder true 0 = true ∧
    weight (image reverseOrder false) 4 = weight (image reverseOrder true) 4 ∧
    reverseOrder.zero ≠ reverseOrder.one := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := congrArg (fun f : Fin 4 → Bool => f ⟨1, by decide⟩) h
  change false = true at hh
  contradiction

set_option maxRecDepth 100000 in
theorem reverseOrder_criterion : Criterion reverseOrder := by unfold Criterion; decide

theorem reverseOrder_parameters :
    (t reverseOrder, s reverseOrder, e reverseOrder, N reverseOrder,
      A 4, B reverseOrder, D reverseOrder 1 0) = (2, 1, 2, 9, 16, 9, -7) := by decide

set_option maxRecDepth 100000 in
theorem independent_prefix_witnesses :
    (List.range 9).map (parityWord sigma) = [1,1,0,1,1,0,0,1,1] ∧
    (List.range 9).map (seedParity 1 187) = (List.range 9).map (parityWord sigma) ∧
    (List.range 16).map (parityWord reverseOrder) =
      [1,1,0,0,1,1,0,0,1,0,1,0,1,0,1,0] ∧
    (List.range 16).map (seedParity 1 12947) = (List.range 16).map (parityWord reverseOrder) := by decide

end CollatzLab.Morphism

namespace CollatzLab

theorem no_rational_seed_realizes_reverseOrder (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.reverseOrder) :=
  no_rational_seed_realizes_equal_weight (by decide) Morphism.reverseOrder
    Morphism.reverseOrder_admissible.1 Morphism.reverseOrder_admissible.2.1
    Morphism.reverseOrder_admissible.2.2 Morphism.reverseOrder_criterion p q

end CollatzLab
