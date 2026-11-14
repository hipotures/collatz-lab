import CollatzLab.NonContracting110111
import CollatzLab.RepeatedPrefix
import CollatzLab.SignedContraction

/-! A concrete noncontracting rational exclusion from repeated prefixes. -/
namespace CollatzLab

/-- The first two letters agree, so every iterated image occurs twice initially. -/
theorem nonContracting_square_prefix (k j : Nat) (hj : j < 3 ^ k) :
    Morphism.word Morphism.nonContracting110111 (3 ^ k + j) =
      Morphism.word Morphism.nonContracting110111 j :=
  Morphism.initial_double_square (by decide) _ Morphism.nonContracting_images.2.2.1
    (by decide) k j hj

theorem no_rational_seed_realizes_nonContracting110111 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.nonContracting110111) :=
  no_rational_seed_morphism_initial_double (by decide) _ Morphism.nonContracting_images.2.2.1
    (by decide) Morphism.nonContracting_not_eventually_periodic p q

theorem no_rational_seed_shifted_nonContracting110111 (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.nonContracting110111) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_nonContracting110111 t p q

theorem no_eventually_shifted_nonContracting110111 (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.nonContracting110111 (t + j)) :=
  no_eventually_shifted_itinerary_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_nonContracting110111 s t p q hq ho

theorem no_eventually_shifted_nonContracting110111_signed (s t : Nat) (p q : Int)
    (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.nonContracting110111 (t + j)) :=
  no_eventually_shifted_itinerary_odd_denominator _ (Morphism.parity_binary _)
    no_rational_seed_realizes_nonContracting110111 s t p q ho

end CollatzLab

namespace CollatzLab

/-- The two expanding affine maps have different intercepts; this exact cocycle
is the one used by rational realizations, not an equal-multiplier substitute. -/
theorem nonContracting_variable_cocycle {p q : Int}
    (hr : RealizesWord p q (Morphism.parityWord Morphism.nonContracting110111)) (n : Nat) :
    8 * numIter q p (3 * (n + 1)) =
      (if Morphism.word Morphism.nonContracting110111 n then 9 else 27) * numIter q p (3 * n) +
      (if Morphism.word Morphism.nonContracting110111 n then 5 else 19) * q := by
  have hh := Morphism.numIter_variable_block (by decide) _
    Morphism.nonContracting_images.2.2.1 hr n
  cases hb : Morphism.word Morphism.nonContracting110111 n <;> rw [hb] at hh
  all_goals simpa [Morphism.c, Morphism.offset, Morphism.weight,
      Morphism.image, Morphism.nonContracting110111] using hh

/-- No common translation simultaneously removes both affine intercepts. -/
theorem nonContracting_no_common_center :
    ¬ ∃ c : Int, 5 = (8 - 9) * c ∧ 19 = (8 - 27) * c := by omega

end CollatzLab
