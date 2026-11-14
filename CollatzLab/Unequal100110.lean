import CollatzLab.MorphismContraction

/-! The unequal-weight fixed point `1 -> 100`, `0 -> 110` has no rational seed. -/
namespace CollatzLab
namespace Morphism

def unequal100110 : Images 3 where
  zero := fun j => decide (j.val < 2)
  one := fun j => decide (j.val = 0)

theorem unequal100110_images :
    List.ofFn unequal100110.one = [true, false, false] ∧
    List.ofFn unequal100110.zero = [true, true, false] := by decide

theorem unequal100110_prolongable_distinct : image unequal100110 true 0 = true ∧
    unequal100110.zero ≠ unequal100110.one := by
  refine ⟨by decide, ?_⟩
  intro he
  have hh := congrArg (fun f : Fin 3 → Bool => f ⟨1, by decide⟩) he
  change true = false at hh
  contradiction

theorem unequal100110_weights :
    weight (image unequal100110 true) 3 = 1 ∧
    weight (image unequal100110 false) 3 = 2 := by decide

theorem unequal100110_image_weight (b : Bool) :
    weight (image unequal100110 b) 3 = if b then 1 else 2 := by cases b <;> decide

theorem unequal100110_word_first (n : Nat) : word unequal100110 (3 * n) = true := by
  have hh := word_block (by decide) unequal100110
    unequal100110_prolongable_distinct.1 n 0 (by decide)
  simp only [Nat.add_zero] at hh
  rw [hh]
  cases word unequal100110 n <;> rfl

theorem unequal100110_word_middle (n : Nat) :
    word unequal100110 (3 * n + 1) = !(word unequal100110 n) := by
  rw [word_block (by decide) unequal100110 unequal100110_prolongable_distinct.1 n 1 (by decide)]
  cases word unequal100110 n <;> rfl

theorem unequal100110_word_last (n : Nat) : word unequal100110 (3 * n + 2) = false := by
  rw [word_block (by decide) unequal100110 unequal100110_prolongable_distinct.1 n 2 (by decide)]
  cases word unequal100110 n <;> rfl

theorem unequal100110_first (n : Nat) : parityWord unequal100110 (3 * n) = 1 := by
  simp [parityWord, unequal100110_word_first, bit]

theorem unequal100110_middle (n : Nat) :
    parityWord unequal100110 (3 * n + 1) = 1 - parityWord unequal100110 n := by
  simp only [parityWord, unequal100110_word_middle]
  cases word unequal100110 n <;> rfl

theorem unequal100110_last (n : Nat) : parityWord unequal100110 (3 * n + 2) = 0 := by
  simp [parityWord, unequal100110_word_last, bit]

/-- Residues one and two contradict forced columns; residue zero descends to
the smaller positive period `p/3`. The starting index is arbitrary. -/
theorem unequal100110_not_periodic_from (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → parityWord unequal100110 (n + p) = parityWord unequal100110 n) →
    False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    rcases (show p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 by omega) with h0 | h1 | h2
    · let d := p / 3
      apply ih d (by dsimp [d]; omega) start (by dsimp [d]; omega)
      intro n hn
      have hh := hper (3 * n + 1) (by omega)
      rw [show 3 * n + 1 + p = 3 * (n + d) + 1 by dsimp [d]; omega,
        unequal100110_middle, unequal100110_middle] at hh
      omega
    · have hh := hper (3 * start + 2) (by omega)
      rw [show 3 * start + 2 + p = 3 * (start + p / 3 + 1) by omega,
        unequal100110_first, unequal100110_last] at hh
      omega
    · have hh := hper (3 * start) (by omega)
      rw [show 3 * start + p = 3 * (start + p / 3) + 2 by omega,
        unequal100110_last, unequal100110_first] at hh
      omega

theorem unequal100110_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord unequal100110) := by
  rintro ⟨start, p, hp, hper⟩
  exact unequal100110_not_periodic_from p start hp hper

/-- Every three consecutive symbols contain a one, including windows across
image boundaries. This statement is stronger than an aligned-image check. -/
theorem unequal100110_no_000 (n : Nat) : word unequal100110 n = true ∨
    word unequal100110 (n + 1) = true ∨ word unequal100110 (n + 2) = true := by
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h0 | h1 | h2
  · left
    rw [show n = 3 * (n / 3) by omega]
    exact unequal100110_word_first _
  · right; right
    rw [show n + 2 = 3 * (n / 3 + 1) by omega]
    exact unequal100110_word_first _
  · right; left
    rw [show n + 1 = 3 * (n / 3 + 1) by omega]
    exact unequal100110_word_first _

theorem unequal100110_three_image_weight (a : Nat) :
    imageWeightSum unequal100110 a 3 ≤ 5 := by
  have hh := unequal100110_no_000 a
  simp only [imageWeightSum, Nat.add_zero, unequal100110_image_weight]
  cases h0 : word unequal100110 a <;>
    cases h1 : word unequal100110 (a + 1) <;>
      cases h2 : word unequal100110 (a + 2) <;> simp_all

theorem unequal100110_nine_weight (n : Nat) :
    weight (fun j => word unequal100110 (9 * n + j)) 9 ≤ 5 := by
  have hh := weight_source_blocks (by decide) unequal100110
    unequal100110_prolongable_distinct.1 (3 * n) 3
  change weight (fun j => word unequal100110 (3 * (3 * n) + j)) 9 = _ at hh
  rw [show 3 * (3 * n) = 9 * n by omega] at hh
  rw [hh]
  exact unequal100110_three_image_weight _

theorem unequal100110_nine_gap : (3 : Int) ^ 5 = 243 ∧ (2 : Int) ^ 9 = 512 ∧
    (3 : Int) ^ 5 < (2 : Int) ^ 9 := by decide

theorem unequal100110_nine_offset (n : Nat) :
    0 ≤ offset (fun j => word unequal100110 (9 * n + j)) 9 ∧
    offset (fun j => word unequal100110 (9 * n + j)) 9 ≤ 19171 :=
  offset_bounds _ 9

/-- The actual nine-step recurrence, with universally quantified chunk index. -/
theorem unequal100110_nine_recurrence {p q : Int}
    (hr : RealizesWord p q (parityWord unequal100110)) (n : Nat) :
    512 * numIter q p (9 * (n + 1)) =
      (3 : Int) ^ weight (fun j => word unequal100110 (9 * n + j)) 9 *
        numIter q p (9 * n) + offset (fun j => word unequal100110 (9 * n + j)) 9 * q :=
  numIter_chunk (word unequal100110) 9 n hr

end Morphism

theorem no_rational_seed_realizes_unequal_100_110 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.unequal100110) :=
  Morphism.no_rational_seed_block_contraction (by decide) Morphism.unequal100110
    Morphism.unequal100110_prolongable_distinct.1 3 5 (by decide)
    (fun n => Morphism.unequal100110_three_image_weight (3 * n))
    (by decide) Morphism.unequal100110_not_eventually_periodic p q

theorem no_rational_seed_realizes_shifted_unequal_100_110 (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.unequal100110) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_100_110 t p q

theorem no_eventually_shifted_unequal_100_110_itinerary (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.unequal100110 (t + j)) :=
  no_eventually_shifted_itinerary_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_100_110 s t p q hq ho

theorem no_int_seed_realizes_shifted_unequal_100_110 (t : Nat) (p : Int) :
    ¬ RealizesWord p 1 (shiftWord (Morphism.parityWord Morphism.unequal100110) t) :=
  no_rational_seed_realizes_shifted_unequal_100_110 t p 1

theorem no_int_orbit_enters_shifted_unequal_100_110 (s t : Nat) (p : Int) :
    ¬ RealizesWord (tIterInt p s) 1
      (shiftWord (Morphism.parityWord Morphism.unequal100110) t) :=
  no_int_seed_realizes_shifted_unequal_100_110 t (tIterInt p s)

theorem no_int_eventually_shifted_unequal_100_110_itinerary (s t : Nat) (p : Int) :
    ¬ (∀ j, seedParity 1 p (s + j) = Morphism.parityWord Morphism.unequal100110 (t + j)) :=
  no_eventually_shifted_unequal_100_110_itinerary s t p 1 (by decide) (by decide)

end CollatzLab
