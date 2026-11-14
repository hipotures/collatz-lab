import CollatzLab.ColumnAperiodic
import CollatzLab.WindowCertificate

/-! A second aperiodic unequal-weight example, with a locally expanding one image. -/
namespace CollatzLab
namespace Morphism

def unequal110100 : Images 3 where
  zero := fun j => decide (j.val = 0)
  one := fun j => decide (j.val < 2)

theorem unequal110100_images_weights :
    List.ofFn unequal110100.one = [true, true, false] ∧
    List.ofFn unequal110100.zero = [true, false, false] ∧
    weight (image unequal110100 true) 3 = 2 ∧
    weight (image unequal110100 false) 3 = 1 := by decide

theorem unequal110100_prolongable_distinct : image unequal110100 true 0 = true ∧
    unequal110100.zero ≠ unequal110100.one := by
  refine ⟨by decide, ?_⟩
  intro he
  have hh := congrArg (fun f : Fin 3 → Bool => f ⟨1, by decide⟩) he
  change false = true at hh
  contradiction

theorem unequal110100_first (n : Nat) : parityWord unequal110100 (3 * n) = 1 := by
  have hh := word_block (by decide) unequal110100
    unequal110100_prolongable_distinct.1 n 0 (by decide)
  simp only [Nat.add_zero] at hh
  simp only [parityWord, hh]
  cases word unequal110100 n <;> rfl

theorem unequal110100_middle (n : Nat) :
    parityWord unequal110100 (3 * n + 1) = parityWord unequal110100 n := by
  simp only [parityWord,
    word_block (by decide) unequal110100 unequal110100_prolongable_distinct.1 n 1 (by decide)]
  cases word unequal110100 n <;> rfl

theorem unequal110100_last (n : Nat) : parityWord unequal110100 (3 * n + 2) = 0 := by
  simp only [parityWord,
    word_block (by decide) unequal110100 unequal110100_prolongable_distinct.1 n 2 (by decide)]
  cases word unequal110100 n <;> rfl

theorem unequal110100_not_eventually_periodic : ¬ EventuallyPeriodic (parityWord unequal110100) :=
  ternary_columns_not_eventually_periodic _ (fun x => x) (fun _ _ h => h)
    unequal110100_first unequal110100_middle unequal110100_last

def unequal110100_language : List (List Bool) :=
  [[false, false, true], [false, true, false], [false, true, true],
   [true, false, false], [true, false, true], [true, true, false]]

def unequal110100_certificate : WindowCertificate unequal110100 3 where
  language := unequal110100_language
  initial := by decide
  closed := by decide

theorem unequal110100_language_covers (a : Nat) :
    window (word unequal110100) 3 a ∈ unequal110100_language :=
  window_certificate_covers (by decide) unequal110100
    unequal110100_prolongable_distinct.1 unequal110100_certificate a

theorem unequal110100_language_occurs :
    ∀ xs ∈ unequal110100_language, ∃ a ∈ List.range 27, window (word unequal110100) 3 a = xs :=
  by decide

theorem unequal110100_certificate_weight :
    ∀ xs ∈ unequal110100_certificate.language, listImageWeight unequal110100 xs ≤ 5 := by decide

theorem unequal110100_certificate_offset :
    ∀ xs ∈ unequal110100_certificate.language,
      finiteOffset (expandWindow unequal110100 9 xs 0) ≤ 761 := by decide

theorem unequal110100_nine_weight (n : Nat) :
    weight (fun j => word unequal110100 (9 * n + j)) 9 ≤ 5 := by
  have hh := weight_source_blocks (by decide) unequal110100
    unequal110100_prolongable_distinct.1 (3 * n) 3
  rw [show 3 * (3 * n) = 9 * n by omega] at hh
  rw [hh]
  exact window_certificate_weight_bound (by decide) unequal110100
    unequal110100_prolongable_distinct.1 unequal110100_certificate unequal110100_certificate_weight _

theorem unequal110100_nine_offset (n : Nat) :
    0 ≤ offset (fun j => word unequal110100 (9 * n + j)) 9 ∧
    offset (fun j => word unequal110100 (9 * n + j)) 9 ≤ 761 := by
  refine ⟨offset_nonneg _ _, ?_⟩
  have hh := window_certificate_offset_bound (by decide) unequal110100
    unequal110100_prolongable_distinct.1 unequal110100_certificate 761
    unequal110100_certificate_offset (3 * n)
  simpa only [show 3 * (3 * n) = 9 * n by omega] using hh

theorem unequal110100_nine_recurrence {p q : Int}
    (hr : RealizesWord p q (parityWord unequal110100)) (n : Nat) :
    512 * numIter q p (9 * (n + 1)) =
      (3 : Int) ^ weight (fun j => word unequal110100 (9 * n + j)) 9 *
        numIter q p (9 * n) + offset (fun j => word unequal110100 (9 * n + j)) 9 * q :=
  numIter_chunk (word unequal110100) 9 n hr

theorem unequal110100_locally_expanding :
    (3 : Int) ^ weight (image unequal110100 true) 3 = 9 ∧ (2 : Int) ^ 3 = 8 := by decide

set_option maxRecDepth 100000 in
theorem unequal110100_positive_prefix :
    (List.range 81).map (seedParity 1 1357326276294383431942267) =
      (List.range 81).map (parityWord unequal110100) ∧
    numIter 1 1357326276294383431942267 81 = 20475100934524160408 := by decide

end Morphism

theorem no_rational_seed_realizes_unequal_110_100 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.unequal110100) :=
  Morphism.no_rational_seed_window_certificate (by decide) Morphism.unequal110100
    Morphism.unequal110100_prolongable_distinct.1 (by decide)
    Morphism.unequal110100_certificate Morphism.unequal110100_certificate_weight
    (by decide) Morphism.unequal110100_not_eventually_periodic p q

theorem no_rational_seed_realizes_shifted_unequal_110_100 (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.unequal110100) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_110_100 t p q

theorem no_eventually_shifted_unequal_110_100_itinerary (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.unequal110100 (t + j)) :=
  no_eventually_shifted_itinerary_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_110_100 s t p q hq ho

theorem no_int_seed_realizes_shifted_unequal_110_100 (t : Nat) (p : Int) :
    ¬ RealizesWord p 1 (shiftWord (Morphism.parityWord Morphism.unequal110100) t) :=
  no_rational_seed_realizes_shifted_unequal_110_100 t p 1

theorem no_int_orbit_enters_shifted_unequal_110_100 (s t : Nat) (p : Int) :
    ¬ RealizesWord (tIterInt p s) 1
      (shiftWord (Morphism.parityWord Morphism.unequal110100) t) :=
  no_int_seed_realizes_shifted_unequal_110_100 t (tIterInt p s)

end CollatzLab
