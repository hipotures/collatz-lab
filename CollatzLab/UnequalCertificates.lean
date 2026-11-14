import CollatzLab.Unequal100110
import CollatzLab.WindowCertificate

/-! Exact finite-language certificates and sharper bounds for unequal images. -/
namespace CollatzLab.Morphism

def unequal100110_language : List (List Bool) :=
  [[false, false, true], [false, true, false], [false, true, true],
   [true, false, false], [true, false, true], [true, true, false]]

/-- Both membership at zero and closure at every residue are finite kernel
computations. Infinite coverage follows from the generic strong induction. -/
def unequal100110_certificate : WindowCertificate unequal100110 3 where
  language := unequal100110_language
  initial := by decide
  closed := by decide

theorem unequal100110_language_covers (a : Nat) :
    window (word unequal100110) 3 a ∈ unequal100110_language :=
  window_certificate_covers (by decide) unequal100110
    unequal100110_prolongable_distinct.1 unequal100110_certificate a

/-- Every certified row actually occurs, so this is the exact length-three
language rather than only a closed over-approximation. -/
theorem unequal100110_language_occurs :
    ∀ xs ∈ unequal100110_language, ∃ a ∈ List.range 27, window (word unequal100110) 3 a = xs :=
  by decide

theorem unequal100110_language_table :
    unequal100110_language.map (fun xs =>
      (listImageWeight unequal100110 xs, finiteOffset (expandWindow unequal100110 9 xs 0))) =
      [(5,319), (5,527), (4,133), (5,761), (4,211), (4,419)] := by decide

theorem unequal100110_certificate_weight :
    ∀ xs ∈ unequal100110_certificate.language, listImageWeight unequal100110 xs ≤ 5 := by decide

theorem unequal100110_certificate_offset :
    ∀ xs ∈ unequal100110_certificate.language,
      finiteOffset (expandWindow unequal100110 9 xs 0) ≤ 761 := by decide

/-- The finite cap 761 now has a universal infinite-word Lean proof. -/
theorem unequal100110_nine_offset_sharp (n : Nat) :
    0 ≤ offset (fun j => word unequal100110 (9 * n + j)) 9 ∧
    offset (fun j => word unequal100110 (9 * n + j)) 9 ≤ 761 := by
  refine ⟨offset_nonneg _ _, ?_⟩
  have hh := window_certificate_offset_bound (by decide) unequal100110
    unequal100110_prolongable_distinct.1 unequal100110_certificate 761
    unequal100110_certificate_offset (3 * n)
  simpa only [show 3 * (3 * n) = 9 * n by omega] using hh

theorem unequal100110_nine_offset_attained :
    offset (fun j => word unequal100110 j) 9 = 761 := by decide

theorem unequal100110_two_source_obstruction :
    imageWeightSum unequal100110 (2 * 5) 2 = 4 ∧ (2 : Int) ^ 6 < (3 : Int) ^ 4 := by decide

end CollatzLab.Morphism

namespace CollatzLab

/-- An independent application of the generic finite certificate interface to
the same concrete exclusion. Aperiodicity is still proved separately. -/
theorem no_rational_seed_unequal_100_110_via_certificate (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.unequal100110) :=
  Morphism.no_rational_seed_window_certificate (by decide) Morphism.unequal100110
    Morphism.unequal100110_prolongable_distinct.1 (by decide)
    Morphism.unequal100110_certificate Morphism.unequal100110_certificate_weight
    (by decide) Morphism.unequal100110_not_eventually_periodic p q

end CollatzLab
