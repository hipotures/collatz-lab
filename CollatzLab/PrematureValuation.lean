import CollatzLab.PolynomialCertificate
import CollatzLab.Secondary

/-! A genuine finite-prefix obstruction to an all-level non-unit valuation shortcut. -/
namespace CollatzLab.PolynomialPair

def secondaryTen : PolynomialPair where
  degree := 10
  p0 := fun j => ([13, 4, 17, 8, 21, 25, 18, 7, 20, -2, 9] : List Int).getD j 0
  p1 := fun j => ([-13, -4, -4, -4, -4, -4, 7, 9, -2, 9, 11] : List Int).getD j 0

def secondaryTenSeed : Int := 24489870188561073689074139556808871213586148320332801509179590176121701984609

theorem secondaryTen_first : secondaryTen.First (Morphism.parityWord Morphism.secondary) 21 ∧
    secondaryTen.residual (Morphism.parityWord Morphism.secondary) 21 = 24 := by
  unfold First
  decide

set_option maxRecDepth 100000 in
theorem secondaryTen_gap : secondaryTen.Gap Morphism.secondary 21 := by
  unfold Gap
  decide

theorem secondaryTen_spacing : (24 : Int) = 2 ^ 3 * 3 ∧
    ¬ (3 < 3 ^ (0 + 1)) ∧ 3 < 3 ^ (1 + 1) := by decide

set_option maxRecDepth 100000 in
theorem secondaryTen_actual_prefix :
    (List.range 256).map (seedParity 1 secondaryTenSeed) =
      (List.range 256).map (Morphism.parityWord Morphism.secondary) := by decide

set_option maxRecDepth 100000 in
/-- The required finite tower congruences hold at both levels without an infinite realization premise. -/
theorem secondaryTen_finite_congruences :
    (Morphism.b Morphism.secondary 0 ^ 21 * Morphism.u Morphism.secondary secondaryTenSeed 1 0 -
      Morphism.D Morphism.secondary 1 0 * Morphism.pre Morphism.secondary
        (Morphism.a Morphism.secondary 0) (Morphism.b Morphism.secondary 0) 22) %
          (Morphism.a Morphism.secondary 0 ^ 22) = 0 ∧
    (Morphism.b Morphism.secondary 1 ^ 21 * Morphism.u Morphism.secondary secondaryTenSeed 1 1 -
      Morphism.D Morphism.secondary 1 1 * Morphism.pre Morphism.secondary
        (Morphism.a Morphism.secondary 1) (Morphism.b Morphism.secondary 1) 22) %
          (Morphism.a Morphism.secondary 1 ^ 22) = 0 := by decide

set_option maxRecDepth 100000 in
theorem secondaryTen_forms :
    E Morphism.secondary secondaryTen secondaryTenSeed 1 0 = -10849436295364754159278076178886372901371891473571896460239574286064854308525179534311424 ∧
    E Morphism.secondary secondaryTen secondaryTenSeed 1 1 = -340302811308838090340341396689767994901269577202276359709448945591401935237405133383389766671299933587063701504 := by decide

set_option maxRecDepth 100000 in
/-- Level zero has valuation 68, whereas the premature formula would give 21*3+3=66. -/
theorem secondaryTen_premature_failure :
    E Morphism.secondary secondaryTen secondaryTenSeed 1 0 % 2 ^ 68 = 0 ∧
    E Morphism.secondary secondaryTen secondaryTenSeed 1 0 % 2 ^ 69 ≠ 0 ∧
    E Morphism.secondary secondaryTen secondaryTenSeed 1 0 % 2 ^ (21 * 3 + 3 + 1) = 0 ∧
    E Morphism.secondary secondaryTen secondaryTenSeed 1 1 % 2 ^ 192 = 0 ∧
    E Morphism.secondary secondaryTen secondaryTenSeed 1 1 % 2 ^ 193 ≠ 0 := by decide

end CollatzLab.PolynomialPair

namespace CollatzLab

theorem no_rational_seed_realizes_secondary_nonunit (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.secondary) :=
  no_rational_seed_with_polynomial_pair (by decide) Morphism.secondary
    Morphism.secondary_admissible.1 Morphism.secondary_admissible.2.1
    Morphism.secondary_admissible.2.2 PolynomialPair.secondaryTen 21 (by decide)
    PolynomialPair.secondaryTen_first.1 PolynomialPair.secondaryTen_gap p q

end CollatzLab
