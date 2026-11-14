import CollatzLab.PeriodicCertificate

/-! The `101/011` target, excluded using the independently found period-two control. -/
namespace CollatzLab.Morphism

theorem secondary_admissible : image secondary true 0 = true ∧
    weight (image secondary false) 3 = weight (image secondary true) 3 ∧
    secondary.zero ≠ secondary.one := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := congrArg (fun f : Fin 3 → Bool => f ⟨0, by decide⟩) h
  change false = true at hh
  contradiction

def alternatingControl : PeriodicControl where
  period := 2
  block := fun j => decide (j.val = 0)
  order := 5

theorem secondary_control_valid : alternatingControl.Valid secondary := by
  unfold PeriodicControl.Valid
  decide

set_option maxRecDepth 100000 in
theorem secondary_control_gap : alternatingControl.Gap secondary := by
  unfold PeriodicControl.Gap
  decide

/-- A second, independent infinite proof of the primary target via Mahler forms. -/
def thueMorseControl : PeriodicControl where
  period := 6
  block := fun j => decide (j.val = 0 ∨ j.val = 3 ∨ j.val = 5)
  order := 10

theorem thueMorse_control_valid : thueMorseControl.Valid thueMorse := by
  unfold PeriodicControl.Valid
  decide

set_option maxRecDepth 100000 in
theorem thueMorse_control_gap : thueMorseControl.Gap thueMorse := by
  unfold PeriodicControl.Gap
  decide

set_option maxRecDepth 100000 in
theorem secondary_positive_prefix :
    (List.range 9).map (parityWord secondary) = [1,0,1,0,1,1,1,0,1] ∧
    (List.range 32).map (seedParity 1 2567104865) = (List.range 32).map (parityWord secondary) ∧
    tIterInt 2567104865 32 = 6252160216 := by decide

end CollatzLab.Morphism

namespace CollatzLab

theorem no_rational_seed_realizes_thueMorse_mahler (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.thueMorse) :=
  no_rational_seed_with_periodic_control (by decide) Morphism.thueMorse
    Morphism.thueMorse_admissible.1 Morphism.thueMorse_admissible.2.1
    Morphism.thueMorse_admissible.2.2 Morphism.thueMorseControl
    Morphism.thueMorse_control_valid Morphism.thueMorse_control_gap p q

theorem no_rational_seed_realizes_secondary (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.secondary) :=
  no_rational_seed_with_periodic_control (by decide) Morphism.secondary
    Morphism.secondary_admissible.1 Morphism.secondary_admissible.2.1
    Morphism.secondary_admissible.2.2 Morphism.alternatingControl
    Morphism.secondary_control_valid Morphism.secondary_control_gap p q

theorem no_rational_seed_realizes_shifted_secondary (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.secondary) t) :=
  no_rational_seed_with_shifted_periodic_control (by decide) Morphism.secondary
    Morphism.secondary_admissible.1 Morphism.secondary_admissible.2.1
    Morphism.secondary_admissible.2.2 Morphism.alternatingControl
    Morphism.secondary_control_valid Morphism.secondary_control_gap t p q

theorem no_eventually_shifted_secondary_itinerary (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = Morphism.parityWord Morphism.secondary (t + j)) := by
  intro ht
  apply no_rational_seed_realizes_shifted_secondary t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

end CollatzLab
