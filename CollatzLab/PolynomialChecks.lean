import CollatzLab.PolynomialCertificate
import CollatzLab.Secondary
import CollatzLab.DegreeSix

/-! Independent periodic and non-unit degree-six regressions. -/
namespace CollatzLab.PolynomialPair

def secondaryPair : PolynomialPair where
  degree := 2
  p0 := fun j => ([1, 0, 0] : List Int).getD j 0
  p1 := fun j => ([-1, 0, 1] : List Int).getD j 0

def thueMorsePeriodicPair : PolynomialPair where
  degree := 6
  p0 := fun j => ([1, 0, 0, 1, 0, 1, 0] : List Int).getD j 0
  p1 := fun j => ([-1, 0, 0, 0, 0, 0, 1] : List Int).getD j 0

def thueMorseSix : PolynomialPair where
  degree := 6
  p0 := fun j => ([1, -6, 3, -4, -3, 6, -9] : List Int).getD j 0
  p1 := fun j => ([-1, 6, -3, 5, -3, -2, -1] : List Int).getD j 0

theorem secondaryPair_first : secondaryPair.First (Morphism.parityWord Morphism.secondary) 5 ∧
    secondaryPair.residual (Morphism.parityWord Morphism.secondary) 5 = -1 := by
  unfold First
  decide

theorem thueMorsePeriodicPair_first :
    thueMorsePeriodicPair.First (Morphism.parityWord Morphism.thueMorse) 10 := by
  unfold First
  decide

set_option maxRecDepth 100000 in
theorem thueMorsePeriodicPair_gap : thueMorsePeriodicPair.Gap Morphism.thueMorse 10 := by
  unfold Gap
  decide

theorem thueMorseSix_first : thueMorseSix.First (Morphism.parityWord Morphism.thueMorse) 13 ∧
    thueMorseSix.residual (Morphism.parityWord Morphism.thueMorse) 13 = 8 := by
  unfold First
  decide

set_option maxRecDepth 100000 in
theorem secondaryPair_gap : secondaryPair.Gap Morphism.secondary 5 := by
  unfold Gap
  decide

theorem thueMorseSix_gap : thueMorseSix.Gap Morphism.thueMorse 13 :=
  Morphism.degree_six_ledger (by decide) Morphism.thueMorse
    Morphism.thueMorse_admissible.2.1 Morphism.thueMorse_admissible.2.2

set_option maxRecDepth 100000 in
theorem thueMorseSix_finite_valuation :
    (List.range 64).map (seedParity 1 3195543223027673837) =
      (List.range 64).map (Morphism.parityWord Morphism.thueMorse) ∧
    E Morphism.thueMorse thueMorseSix 3195543223027673837 1 0 = 69953636695298807955456 ∧
    E Morphism.thueMorse thueMorseSix 3195543223027673837 1 1 = -7357915019712427889214357504 ∧
    (69953636695298807955456 : Int) % 2 ^ 29 = 0 ∧
    (69953636695298807955456 : Int) % 2 ^ 30 ≠ 0 ∧
    (-7357915019712427889214357504 : Int) % 2 ^ 55 = 0 ∧
    (-7357915019712427889214357504 : Int) % 2 ^ 56 ≠ 0 := by decide

/-- Coefficient 8 requires discarding level zero; level one is the first safe level. -/
theorem thueMorseSix_start : ¬ (3 < 2 ^ (0 + 1)) ∧ 3 < 2 ^ (1 + 1) := by decide

end CollatzLab.PolynomialPair

namespace CollatzLab

theorem no_rational_seed_realizes_thueMorse_polynomial (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.thueMorse) :=
  no_rational_seed_with_polynomial_pair (by decide) Morphism.thueMorse
    Morphism.thueMorse_admissible.1 Morphism.thueMorse_admissible.2.1
    Morphism.thueMorse_admissible.2.2 PolynomialPair.thueMorseSix 13 (by decide)
    PolynomialPair.thueMorseSix_first.1 PolynomialPair.thueMorseSix_gap p q

theorem no_rational_seed_realizes_secondary_polynomial (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.secondary) :=
  no_rational_seed_with_polynomial_pair (by decide) Morphism.secondary
    Morphism.secondary_admissible.1 Morphism.secondary_admissible.2.1
    Morphism.secondary_admissible.2.2 PolynomialPair.secondaryPair 5 (by decide)
    PolynomialPair.secondaryPair_first.1 PolynomialPair.secondaryPair_gap p q

end CollatzLab
