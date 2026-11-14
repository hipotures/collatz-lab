import CollatzLab.Subcritical

/-! Uniform finite-block contraction without an equal-image-weight hypothesis. -/
namespace CollatzLab
namespace Morphism

/-- The all-one word maximizes the affine offset at every length. -/
theorem offset_upper (v : Nat → Bool) : ∀ n,
    offset v n ≤ (3 : Int) ^ n - (2 : Int) ^ n
  | 0 => by simp [offset]
  | n + 1 => by
    have hi := offset_upper v n
    have hp := pow_le_pow_of_le (x := (2 : Int)) (y := 3) (by decide) (by decide) n
    have h2 := pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) n
    rw [offset, Int.pow_succ, Int.pow_succ]
    split <;> omega

theorem offset_bounds (v : Nat → Bool) (n : Nat) :
    0 ≤ offset v n ∧ offset v n ≤ (3 : Int) ^ n - (2 : Int) ^ n :=
  ⟨offset_nonneg v n, offset_upper v n⟩

/-- Arbitrary aligned chunks of an actual rational parity itinerary obey this
exact recurrence, regardless of image weights or signs of the numerator. -/
theorem numIter_chunk (v : Nat → Bool) (k n : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j))) :
    (2 : Int) ^ k * numIter q p (k * (n + 1)) =
      (3 : Int) ^ weight (fun j => v (k * n + j)) k * numIter q p (k * n) +
        offset (fun j => v (k * n + j)) k * q := by
  have hh := affine_prefix (fun j => v (k * n + j)) q p hr.2.1 (k * n) k
    (fun j _ => hr.2.2 (k * n + j))
  simpa only [Nat.mul_succ] using hh

/-- Sum of the selected image weights in a source window. -/
def imageWeightSum {L : Nat} (M : Images L) (a : Nat) : Nat → Nat
  | 0 => 0
  | h + 1 => imageWeightSum M a h + weight (image M (word M (a + h))) L

/-- Exact link between source-symbol weights and arbitrary aligned expanded
windows. It does not require equal weights or an arithmetic realization. -/
theorem weight_source_blocks {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (a : Nat) : ∀ h,
    weight (fun j => word M (L * a + j)) (L * h) = imageWeightSum M a h
  | 0 => by simp [weight, imageWeightSum]
  | h + 1 => by
    rw [Nat.mul_succ, weight_segment, weight_source_blocks hL M h1 a h, imageWeightSum]
    congr 1
    apply (common_prefix _ _ L ?_).1
    intro j hj
    rw [show L * a + (L * h + j) = L * (a + h) + j by rw [Nat.mul_add]; omega]
    exact word_block hL M h1 (a + h) j hj

/-- The unequal-weight single-image recurrence, with the multiplier selected by
the actual parent symbol. -/
theorem numIter_variable_block {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) {p q : Int}
    (hr : RealizesWord p q (parityWord M)) (n : Nat) :
    (2 : Int) ^ L * numIter q p (L * (n + 1)) =
      (3 : Int) ^ weight (image M (word M n)) L * numIter q p (L * n) +
        c M (word M n) * q := by
  have hh := affine_prefix (image M (word M n)) q p hr.2.1 (L * n) L
    (fun j hj => (hr.2.2 (L * n + j)).trans
      (congrArg bit (word_block hL M h1 n j hj)))
  simpa only [Nat.mul_succ, c] using hh

/-- Every aligned group of source images gives the true multi-block numerator
identity. The exponent is exactly the sum of the selected image weights. -/
theorem numIter_source_blocks {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (h n : Nat) {p q : Int}
    (hr : RealizesWord p q (parityWord M)) :
    (2 : Int) ^ (L * h) * numIter q p ((L * h) * (n + 1)) =
      (3 : Int) ^ imageWeightSum M (h * n) h * numIter q p ((L * h) * n) +
        offset (fun j => word M ((L * h) * n + j)) (L * h) * q := by
  have hh := numIter_chunk (word M) (L * h) n hr
  rw [show (L * h) * n = L * (h * n) from Nat.mul_assoc L h n,
    weight_source_blocks hL M h1] at hh
  simpa only [Nat.mul_assoc] using hh

end Morphism

/-- A rational itinerary with uniformly contracting aligned chunks is eventually
periodic. The radius is explicit and works for unreduced signed numerators. -/
theorem uniformly_contracting_blocks_periodic (v : Nat → Bool) (k R : Nat)
    (hk : 1 ≤ k)
    (hw : ∀ n, Morphism.weight (fun j => v (k * n + j)) k ≤ R)
    (hgap : (3 : Int) ^ R < (2 : Int) ^ k) {p q : Int}
    (hr : RealizesWord p q (fun j => Morphism.bit (v j))) :
    EventuallyPeriodic (fun j => Morphism.bit (v j)) := by
  let y := fun n => numIter q p (k * n)
  let B := fun n => (3 : Int) ^ Morphism.weight (fun j => v (k * n + j)) k
  let d := fun n => Morphism.offset (fun j => v (k * n + j)) k * q
  let C := ((3 : Int) ^ k - (2 : Int) ^ k) * q
  have hq : 0 ≤ q := by have := hr.1; omega
  have hC : 0 ≤ C := Int.mul_nonneg
    (by have := pow_le_pow_of_le (x := (2 : Int)) (y := 3) (by decide) (by decide) k; omega) hq
  have hB : ∀ n, 0 ≤ B n ∧ B n ≤ (3 : Int) ^ R := by
    intro n
    refine ⟨pow_nonneg_of_nonneg (by decide) _, ?_⟩
    have hh := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) (hw n))
    simpa only [Int.natCast_pow] using hh
  have hd : ∀ n, -C ≤ d n ∧ d n ≤ C := by
    intro n
    have hb := Morphism.offset_bounds (fun j => v (k * n + j)) k
    have hlo := Int.mul_nonneg hb.1 hq
    have hhi := Int.mul_le_mul_of_nonneg_right hb.2 hq
    exact ⟨by dsimp [d]; omega, hhi⟩
  have hb := variable_contracting_recurrence_bounded ((2 : Int) ^ k) ((3 : Int) ^ R) C
    hgap hC B y d hB hd (fun n => Morphism.numIter_chunk v k n hr)
  have hK : 0 ≤ absInt (y 0) + C := by have := absInt_nonneg (y 0); omega
  have hp := bounded_blocks_periodic k hk p q (absInt (y 0) + C) hK hb
  have he : seedParity q p = fun j => Morphism.bit (v j) := funext hr.2.2
  rwa [he] at hp

theorem no_rational_seed_uniform_block_contraction (v : Nat → Bool) (k R : Nat)
    (hk : 1 ≤ k)
    (hw : ∀ n, Morphism.weight (fun j => v (k * n + j)) k ≤ R)
    (hgap : (3 : Int) ^ R < (2 : Int) ^ k)
    (haper : ¬ EventuallyPeriodic (fun j => Morphism.bit (v j))) (p q : Int) :
    ¬ RealizesWord p q (fun j => Morphism.bit (v j)) :=
  fun hr => haper (uniformly_contracting_blocks_periodic v k R hk hw hgap hr)

namespace Morphism

/-- A reusable sufficient criterion for unequal-weight uniform morphisms. Only
aligned groups of `h` source symbols need a uniform image-weight bound. -/
theorem no_rational_seed_block_contraction {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (h R : Nat) (hh : 1 ≤ h)
    (hw : ∀ n, imageWeightSum M (h * n) h ≤ R)
    (hgap : (3 : Int) ^ R < (2 : Int) ^ (L * h))
    (haper : ¬ EventuallyPeriodic (parityWord M)) (p q : Int) :
    ¬ RealizesWord p q (parityWord M) := by
  apply no_rational_seed_uniform_block_contraction (word M) (L * h) R
    (by have := Nat.mul_le_mul hL hh; omega) ?_ hgap haper p q
  intro n
  rw [Nat.mul_assoc, weight_source_blocks hL M h1]
  exact hw n

end Morphism

/-- Binary inverse branches propagate any universal rational exclusion to every
finite shift. Their positive odd denominators are already verified. -/
theorem no_rational_seed_shifts_of_exclusion (v : Nat → Int)
    (hv : ∀ n, v n = 0 ∨ v n = 1)
    (hex : ∀ p q, ¬ RealizesWord p q v) :
    ∀ t p q, ¬ RealizesWord p q (shiftWord v t)
  | 0, p, q, hr => hex p q ⟨hr.1, hr.2.1, fun n => by simpa [shiftWord] using hr.2.2 n⟩
  | t + 1, p, q, hr => no_rational_seed_shifts_of_exclusion v hv hex t
      (invBranchNum (v t) p q) (invBranchDen (v t) q)
      (realizes_shiftWord_pred (hv t) hr)

theorem no_eventually_shifted_itinerary_of_exclusion (v : Nat → Int)
    (hv : ∀ n, v n = 0 ∨ v n = 1)
    (hex : ∀ p q, ¬ RealizesWord p q v) (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = v (t + j)) := by
  intro ht
  apply no_rational_seed_shifts_of_exclusion v hv hex t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

end CollatzLab
