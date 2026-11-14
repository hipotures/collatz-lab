import CollatzLab.ColumnAperiodic
import CollatzLab.MorphismBalance

/-! Sparse one images versus dense zero images: finite spectral applications. -/
set_option maxRecDepth 10000

namespace CollatzLab
namespace Morphism

/-- `1 -> 10^(L-1)`, `0 -> 1^(L-1)0`. -/
def unequalSparse (L : Nat) : Images L where
  zero := fun j => decide (j.val < L - 1)
  one := fun j => decide (j.val = 0)

theorem unequalSparse_prolongable (L : Nat) (hL : 1 ≤ L) :
    image (unequalSparse L) true 0 = true := by simp [image, unequalSparse]; omega

theorem unequalSparse_distinct (L : Nat) (hL : 3 ≤ L) :
    (unequalSparse L).zero ≠ (unequalSparse L).one := by
  intro he
  have hh := congrArg (fun f : Fin L → Bool => f ⟨1, by omega⟩) he
  simp [unequalSparse, show 1 < L - 1 by omega] at hh

theorem unequalSparse_first (L : Nat) (hL : 3 ≤ L) (n : Nat) :
    parityWord (unequalSparse L) (L * n) = 1 := by
  have hh := word_block (by omega) (unequalSparse L) (unequalSparse_prolongable L (by omega))
    n 0 (by omega)
  simp only [Nat.add_zero] at hh
  simp only [parityWord, hh]
  cases word (unequalSparse L) n <;> simp [image, unequalSparse, bit, show 0 < L by omega,
    show 0 < L - 1 by omega]

theorem unequalSparse_middle (L : Nat) (hL : 3 ≤ L) (n j : Nat)
    (hj : 1 ≤ j) (hj' : j < L - 1) :
    parityWord (unequalSparse L) (L * n + j) = 1 - parityWord (unequalSparse L) n := by
  simp only [parityWord, word_block (by omega) (unequalSparse L)
    (unequalSparse_prolongable L (by omega)) n j (by omega)]
  cases word (unequalSparse L) n <;>
    simp [image, unequalSparse, bit, show j < L by omega, show j ≠ 0 by omega, hj']

theorem unequalSparse_last (L : Nat) (hL : 3 ≤ L) (n : Nat) :
    parityWord (unequalSparse L) (L * n + (L - 1)) = 0 := by
  simp only [parityWord, word_block (by omega) (unequalSparse L)
    (unequalSparse_prolongable L (by omega)) n (L - 1) (by omega)]
  cases word (unequalSparse L) n <;>
    simp [image, unequalSparse, bit, show L - 1 < L by omega, show L - 1 ≠ 0 by omega]

theorem unequalSparse_not_eventually_periodic (L : Nat) (hL : 3 ≤ L) :
    ¬ EventuallyPeriodic (parityWord (unequalSparse L)) :=
  complement_columns_not_eventually_periodic L hL _
    (unequalSparse_first L hL) (unequalSparse_middle L hL) (unequalSparse_last L hL)

theorem unequalSparse_four_spectral :
    frequencyDen (unequalSparse 4) = 6 ∧ weightDelta (unequalSparse 4) = -2 ∧
    (3 : Int) ^ 10 = 59049 ∧ (2 : Int) ^ (4 ^ 2) = 65536 ∧
    (3 : Int) ^ 10 < (2 : Int) ^ (4 ^ 2) := by decide

theorem unequalSparse_five_spectral :
    frequencyDen (unequalSparse 5) = 8 ∧ weightDelta (unequalSparse 5) = -3 ∧
    (3 : Int) ^ 76 < (2 : Int) ^ (5 ^ 3) := by decide

theorem unequalSparse_five_uniform_count (n : Nat) :
    weight (fun j => word (unequalSparse 5) (125 * n + j)) 125 ≤ 76 :=
  spectral_weight_bound (by decide) (unequalSparse 5) (by decide) 3 76
    (by decide) (by decide) (by decide) n

theorem unequalSparse_five_all_windows (a h : Nat) :
    weight (fun j => word (unequalSparse 5) (a + j)) h ≤ (h / 125 + 2) * 76 :=
  weight_window_from_aligned _ 125 76 (by decide) unequalSparse_five_uniform_count a h

end Morphism

theorem no_rational_seed_realizes_unequal_1000_1110 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord (Morphism.unequalSparse 4)) :=
  Morphism.no_rational_seed_spectral_certificate (by decide) (Morphism.unequalSparse 4)
    (by decide) 2 10 (by decide) (by decide) (by decide) (by decide)
    (Morphism.unequalSparse_not_eventually_periodic 4 (by decide)) p q

theorem no_rational_seed_realizes_unequal_10000_11110 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord (Morphism.unequalSparse 5)) :=
  Morphism.no_rational_seed_spectral_certificate (by decide) (Morphism.unequalSparse 5)
    (by decide) 3 76 (by decide) (by decide) (by decide) (by decide)
    (Morphism.unequalSparse_not_eventually_periodic 5 (by decide)) p q

theorem no_rational_seed_realizes_shifted_unequalSparse_four (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord (Morphism.unequalSparse 4)) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_1000_1110 t p q

theorem no_rational_seed_realizes_shifted_unequalSparse_five (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord (Morphism.unequalSparse 5)) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_10000_11110 t p q

theorem no_eventually_shifted_unequalSparse_four_itinerary (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord (Morphism.unequalSparse 4) (t + j)) :=
  no_eventually_shifted_itinerary_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_1000_1110 s t p q hq ho

theorem no_eventually_shifted_unequalSparse_five_itinerary (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord (Morphism.unequalSparse 5) (t + j)) :=
  no_eventually_shifted_itinerary_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_10000_11110 s t p q hq ho

end CollatzLab
