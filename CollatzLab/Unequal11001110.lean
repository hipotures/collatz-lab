import CollatzLab.ColumnCertificate
import CollatzLab.MorphismBalance

/-! A non-sparse unequal example certified by two finite kernel-checked tables. -/
namespace CollatzLab
namespace Morphism

def unequal11001110 : Images 4 where
  zero := fun j => decide (j.val < 3)
  one := fun j => decide (j.val < 2)

theorem unequal11001110_images_weights :
    List.ofFn unequal11001110.one = [true,true,false,false] ∧
    List.ofFn unequal11001110.zero = [true,true,true,false] ∧
    weight (image unequal11001110 true) 4 = 2 ∧
    weight (image unequal11001110 false) 4 = 3 := by decide

def unequal11001110_columns : ColumnCertificate unequal11001110 where
  distinguish := ⟨2, by decide⟩
  different := by decide
  separate := fun r => if r.val = 1 then ⟨3, by decide⟩ else
    if r.val = 2 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  separates := by decide

theorem unequal11001110_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord unequal11001110) :=
  column_certificate_not_eventually_periodic (by decide) unequal11001110 (by decide)
    unequal11001110_columns

def unequal11001110_language : List (List Bool) :=
  [[false,false,true,true], [false,true,true,false], [false,true,true,true],
   [true,false,false,true], [true,false,true,true], [true,true,false,false],
   [true,true,false,true], [true,true,true,false]]

def unequal11001110_windows : WindowCertificate unequal11001110 4 where
  language := unequal11001110_language
  initial := by decide
  closed := by decide

theorem unequal11001110_language_covers (a : Nat) :
    window (word unequal11001110) 4 a ∈ unequal11001110_language :=
  window_certificate_covers (by decide) unequal11001110 (by decide) unequal11001110_windows a

set_option maxRecDepth 100000 in
theorem unequal11001110_language_occurs :
    ∀ xs ∈ unequal11001110_language, ∃ a ∈ List.range 64, window (word unequal11001110) 4 a = xs :=
  by decide

theorem unequal11001110_certificate_weight :
    ∀ xs ∈ unequal11001110_windows.language, listImageWeight unequal11001110 xs ≤ 10 := by decide

theorem unequal11001110_certificate_offset :
    ∀ xs ∈ unequal11001110_windows.language,
      finiteOffset (expandWindow unequal11001110 16 xs 0) ≤ 300277 := by decide

theorem unequal11001110_sixteen_weight (n : Nat) :
    weight (fun j => word unequal11001110 (16 * n + j)) 16 ≤ 10 :=
  spectral_weight_bound (by decide) unequal11001110 (by decide) 2 10
    (by decide) (by decide) (by decide) n

theorem unequal11001110_sixteen_offset (n : Nat) :
    0 ≤ offset (fun j => word unequal11001110 (16 * n + j)) 16 ∧
    offset (fun j => word unequal11001110 (16 * n + j)) 16 ≤ 300277 := by
  refine ⟨offset_nonneg _ _, ?_⟩
  have hh := window_certificate_offset_bound (by decide) unequal11001110 (by decide)
    unequal11001110_windows 300277 unequal11001110_certificate_offset (4 * n)
  simpa only [show 4 * (4 * n) = 16 * n by omega] using hh

theorem unequal11001110_sixteen_recurrence {p q : Int}
    (hr : RealizesWord p q (parityWord unequal11001110)) (n : Nat) :
    65536 * numIter q p (16 * (n + 1)) =
      (3 : Int) ^ weight (fun j => word unequal11001110 (16 * n + j)) 16 *
        numIter q p (16 * n) + offset (fun j => word unequal11001110 (16 * n + j)) 16 * q :=
  numIter_chunk (word unequal11001110) 16 n hr

theorem unequal11001110_offset_attained : offset (word unequal11001110) 16 = 300277 := by decide

theorem unequal11001110_locally_expanding :
    (3 : Int) ^ weight (image unequal11001110 false) 4 = 27 ∧ (2 : Int) ^ 4 = 16 := by decide

set_option maxRecDepth 100000 in
theorem unequal11001110_positive_prefix :
    (List.range 81).map (seedParity 1 1062454736003492165269651) =
      (List.range 81).map (parityWord unequal11001110) ∧
    numIter 1 1062454736003492165269651 81 = 105153145684560865940321 := by decide

end Morphism

theorem no_rational_seed_realizes_unequal_1100_1110 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.unequal11001110) :=
  Morphism.no_rational_seed_finite_certificates (by decide) Morphism.unequal11001110 (by decide)
    Morphism.unequal11001110_columns (by decide) Morphism.unequal11001110_windows
    Morphism.unequal11001110_certificate_weight (by decide) p q

theorem no_rational_seed_realizes_shifted_unequal_1100_1110 (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.unequal11001110) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_1100_1110 t p q

theorem no_eventually_shifted_unequal_1100_1110_itinerary (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.unequal11001110 (t + j)) :=
  no_eventually_shifted_itinerary_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_1100_1110 s t p q hq ho

end CollatzLab
