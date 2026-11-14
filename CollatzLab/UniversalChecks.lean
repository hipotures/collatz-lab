import CollatzLab.UniversalEqualWeight
import CollatzLab.EqualWeightChecks
import CollatzLab.Secondary
import CollatzLab.FamilySemanticChecks

/-! Corollaries and independent semantic checks, including a supercritical length-six example. -/
namespace CollatzLab.Morphism

def supercriticalSix : Images 6 where
  zero := fun j => decide (j.val = 1 ∨ j.val = 2 ∨ j.val = 4 ∨ j.val = 5)
  one := fun j => decide (j.val = 0 ∨ j.val = 2 ∨ j.val = 4 ∨ j.val = 5)

def lengthFive : Images 5 where
  zero := fun j => decide (j.val ≠ 3)
  one := fun j => decide (j.val < 4)

theorem supercriticalSix_admissible : image supercriticalSix true 0 = true ∧
    weight (image supercriticalSix false) 6 = weight (image supercriticalSix true) 6 ∧
    supercriticalSix.zero ≠ supercriticalSix.one := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := congrArg (fun f : Fin 6 → Bool => f ⟨0, by decide⟩) h
  change false = true at hh
  contradiction

theorem supercriticalSix_parameters : weight (image supercriticalSix true) 6 = 4 ∧
    A 6 = 64 ∧ B supercriticalSix = 81 ∧ s supercriticalSix = 0 ∧
    e supercriticalSix = 1 ∧ t supercriticalSix = 1 ∧ N supercriticalSix = 6 := by decide

set_option maxRecDepth 100000 in
theorem supercriticalSix_fails_old_criterion : A 6 < B supercriticalSix ∧
    ¬ Criterion supercriticalSix ∧
    (81 : Int) ^ (6 * 5 + 6 + 1) < (2 : Int) ^ (6 * 5 * 13) := by
  unfold Criterion
  decide

end CollatzLab.Morphism

namespace CollatzLab

theorem no_rational_seed_realizes_supercriticalSix (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.supercriticalSix) :=
  no_rational_seed_realizes_all_equal_weight (by decide) Morphism.supercriticalSix
    Morphism.supercriticalSix_admissible.1 Morphism.supercriticalSix_admissible.2.1
    Morphism.supercriticalSix_admissible.2.2 p q

theorem no_rational_seed_realizes_thueMorse_universal (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.thueMorse) :=
  no_rational_seed_realizes_all_equal_weight (by decide) Morphism.thueMorse
    Morphism.thueMorse_admissible.1 Morphism.thueMorse_admissible.2.1
    Morphism.thueMorse_admissible.2.2 p q

theorem no_rational_seed_realizes_secondary_universal (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.secondary) :=
  no_rational_seed_realizes_all_equal_weight (by decide) Morphism.secondary
    Morphism.secondary_admissible.1 Morphism.secondary_admissible.2.1
    Morphism.secondary_admissible.2.2 p q

theorem no_rational_seed_realizes_sigma_universal (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.sigma) :=
  no_rational_seed_realizes_all_equal_weight (by decide) Morphism.sigma
    Morphism.sigma_admissible.1 Morphism.sigma_admissible.2.1
    Morphism.sigma_admissible.2.2 p q

theorem no_rational_seed_realizes_reverseOrder_universal (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.reverseOrder) :=
  no_rational_seed_realizes_all_equal_weight (by decide) Morphism.reverseOrder
    Morphism.reverseOrder_admissible.1 Morphism.reverseOrder_admissible.2.1
    Morphism.reverseOrder_admissible.2.2 p q

namespace Phase8Audit

def supercriticalPair : PolynomialPair where
  degree := 6
  p0 := fun j => ([0, -1, 0, -1, 1, -1, 0] : List Int).getD j 0
  p1 := fun j => ([0, 1, 0, 0, -1, 0, 0] : List Int).getD j 0

set_option maxRecDepth 100000 in
theorem supercritical_pair_valid :
    supercriticalPair.First (Morphism.parityWord Morphism.supercriticalSix) 13 ∧
    supercriticalPair.residual (Morphism.parityWord Morphism.supercriticalSix) 13 = 1 ∧
    supercriticalPair.Gap Morphism.supercriticalSix 13 ∧
    supercriticalPair.p1 0 = 0 ∧ supercriticalPair.p1 1 ≠ 0 := by
  unfold PolynomialPair.First PolynomialPair.Gap
  decide

/-- Two literal substitutions, independent of the base-L recurrence. -/
def literalTwo (zero one : List Int) : List Int :=
  one.flatMap (fun b => if b = 1 then one else zero)

theorem literal_words_two_through_six :
    (List.range 4).map (Morphism.parityWord Morphism.thueMorse) = literalTwo [0,1] [1,0] ∧
    (List.range 9).map (Morphism.parityWord Morphism.secondary) = literalTwo [0,1,1] [1,0,1] ∧
    (List.range 16).map (Morphism.parityWord Morphism.reverseOrder) = literalTwo [1,0,1,0] [1,1,0,0] ∧
    (List.range 25).map (Morphism.parityWord Morphism.lengthFive) = literalTwo [1,1,1,0,1] [1,1,1,1,0] ∧
    (List.range 36).map (Morphism.parityWord Morphism.supercriticalSix) = literalTwo [0,1,1,0,1,1] [1,0,1,0,1,1] := by decide

set_option maxRecDepth 100000 in
theorem positive_prefixes_two_through_six :
    (List.range 4).map (seedParity 1 13) = literalTwo [0,1] [1,0] ∧
    (List.range 9).map (seedParity 1 353) = literalTwo [0,1,1] [1,0,1] ∧
    (List.range 16).map (seedParity 1 12947) = literalTwo [1,0,1,0] [1,1,0,0] ∧
    (List.range 25).map (seedParity 1 25850607) = literalTwo [1,1,1,0,1] [1,1,1,1,0] ∧
    (List.range 36).map (seedParity 1 11999337121) = literalTwo [0,1,1,0,1,1] [1,0,1,0,1,1] ∧
    numIter 1 11999337121 36 = 49315963742 := by decide

set_option maxRecDepth 100000 in
theorem negative_prefixes_two_through_six :
    (List.range 4).map (seedParity 5 (-15)) = literalTwo [0,1] [1,0] ∧
    (List.range 9).map (seedParity 5 (-283)) = literalTwo [0,1,1] [1,0,1] ∧
    (List.range 16).map (seedParity 5 (-801)) = literalTwo [1,0,1,0] [1,1,0,0] ∧
    (List.range 25).map (seedParity 5 (-4964693)) = literalTwo [1,1,1,0,1] [1,1,1,1,0] ∧
    (List.range 36).map (seedParity 5 (-8722791131)) = literalTwo [0,1,1,0,1,1] [1,0,1,0,1,1] ∧
    (List.range 36).map (seedParity 15 (-26168373393)) = literalTwo [0,1,1,0,1,1] [1,0,1,0,1,1] := by decide

/-- The rational representation is not silently required to be reduced. -/
theorem unreduced_seed_equivalence (n : Nat) :
    seedParity 15 (-26168373393) n = seedParity 5 (-8722791131) n := by
  exact (numIter_equiv (p := -26168373393) (q := 15) (p' := -8722791131) (q' := 5)
    (by decide) (by decide) (by decide) n).2

/-- Actual infinite rational itineraries still exist outside the hypotheses. -/
theorem predicate_nonvacuous : RealizesWord 0 1 (fun _ => 0) ∧ RealizesWord (-5) 5 (fun _ => 1) := by
  exact ⟨realizes_all_zero, Phase7Audit.negative_realization⟩

end Phase8Audit
end CollatzLab
