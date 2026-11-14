import CollatzLab.MorphismContraction
import CollatzLab.ExponentialGap

/-! Rational exclusion from arbitrarily long square prefixes, without contraction. -/
namespace CollatzLab
open Morphism

def prefixCycleForm (v : Nat → Bool) (m : Nat) (p q : Int) : Int :=
  ((2 : Int) ^ m - (3 : Int) ^ weight v m) * p - offset v m * q

/-- Matching a prefix again at m forces a period-closing congruence of
precision m+ell, even for a partial repetition shorter than a square. -/
theorem matching_prefix_divisibility (v : Nat → Bool) (m ell : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (hmatch : ∀ j, j < ell → v (m + j) = v j) :
    (2 : Int) ^ (m + ell) ∣ prefixCycleForm v m p q := by
  have h0 := affine_prefix v q p hr.2.1 0 ell (fun j _ => by simpa using hr.2.2 j)
  have h1 := affine_prefix v q p hr.2.1 m ell
    (fun j hj => (hr.2.2 (m + j)).trans (congrArg bit (hmatch j hj)))
  have hfull := affine_prefix v q p hr.2.1 0 m (fun j _ => by simpa using hr.2.2 j)
  simp only [Nat.zero_add, numIter] at h0 hfull
  let A := (2 : Int) ^ ell
  let B := (3 : Int) ^ weight v ell
  have hd : A ∣ B * (numIter q p m - p) := by
    refine ⟨numIter q p (m + ell) - numIter q p ell, ?_⟩
    dsimp [A, B]
    family_ring
  have hbez : IsBezout A B := IsBezout.pow (show IsBezout 2 3 from ⟨-1, 1, rfl⟩) _ _
  rcases hbez.dvd_of_dvd_mul_left hd with ⟨d, hd⟩
  refine ⟨-d, ?_⟩
  have he : prefixCycleForm v m p q = (2 : Int) ^ m * (p - numIter q p m) := by
    dsimp [prefixCycleForm]
    family_ring
  rw [he, show p - numIter q p m = -(A * d) by omega, int_pow_add]
  dsimp [A]
  family_ring

/-- Two equal initial blocks supply twice their length in congruence precision. -/
theorem square_prefix_divisibility (v : Nat → Bool) (m : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (hsquare : ∀ j, j < m → v (m + j) = v j) :
    (2 : Int) ^ (m + m) ∣ prefixCycleForm v m p q :=
  matching_prefix_divisibility v m m hr hsquare

/-- The period-closing form can vanish only if the actual orbit repeats. -/
theorem prefixCycleForm_nonzero (v : Nat → Bool) (m : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j))) :
    prefixCycleForm v m p q ≠ 0 := by
  intro hz
  have h0 := affine_prefix v q p hr.2.1 0 m (fun j _ => by simpa using hr.2.2 j)
  simp only [Nat.zero_add, numIter] at h0
  have he : numIter q p m = p := by
    apply Int.eq_of_mul_eq_mul_left (a := (2 : Int) ^ m)
      (by have := pow_pos_of_pos (x := (2 : Int)) (by decide) m; omega)
    unfold prefixCycleForm at hz
    family_ring
  have hp := repeated_numIter_periodic q p 0 m (by omega) he.symm
  have hv : seedParity q p = fun j => bit (v j) := funext hr.2.2
  rw [hv] at hp
  exact haper hp

/-- A universal crude height bound suffices: the offset is at most 3^m-2^m.
No supercritical frequency or common image multiplier is assumed. -/
theorem prefixCycleForm_height (v : Nat → Bool) (m : Nat) (p q : Int) (hq : 0 ≤ q) :
    absInt (prefixCycleForm v m p q) ≤ (absInt p + q) * (3 : Int) ^ m := by
  have hA := pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) m
  have hB := pow_nonneg_of_nonneg (x := (3 : Int)) (by decide) (weight v m)
  have hM := pow_nonneg_of_nonneg (x := (3 : Int)) (by decide) m
  have hAM := pow_le_pow_of_le (x := (2 : Int)) (y := 3) (by decide) (by decide) m
  have hBM := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) (weight_le v m))
  simp only [Int.natCast_pow] at hBM
  change (3 : Int) ^ weight v m ≤ (3 : Int) ^ m at hBM
  have hdiff : absInt ((2 : Int) ^ m - (3 : Int) ^ weight v m) ≤ (3 : Int) ^ m := by
    unfold absInt; split <;> omega
  have hc := offset_bounds v m
  have ht := absInt_sub_le (((2 : Int) ^ m - (3 : Int) ^ weight v m) * p) (offset v m * q)
  rw [absInt_mul, absInt_mul, absInt_of_nonneg hc.1, absInt_of_nonneg hq] at ht
  have hp := Int.mul_le_mul_of_nonneg_right hdiff (absInt_nonneg p)
  have hq' := Int.mul_le_mul_of_nonneg_right (show offset v m ≤ (3 : Int) ^ m by omega) hq
  unfold prefixCycleForm
  family_ring

/-- Exact weight-dependent offset cap, attained by placing all ones last.
This improves the crude 3^m bound without assuming frequency convergence. -/
theorem offset_weight_upper (v : Nat → Bool) : ∀ m,
    offset v m ≤ (2 : Int) ^ (m - weight v m) * (3 : Int) ^ weight v m - (2 : Int) ^ m
  | 0 => by simp [weight, offset]
  | m + 1 => by
    have hi := offset_weight_upper v m
    have hn := weight_le v m
    have hc := offset_nonneg v m
    cases hb : v m
    · simp only [offset, weight, hb, Bool.false_eq_true, if_false, Nat.add_zero]
      rw [show m + 1 - weight v m = (m - weight v m) + 1 by omega, Int.pow_succ, Int.pow_succ]
      family_ring
    · simp only [offset, weight, hb, if_true]
      rw [show m + 1 - (weight v m + 1) = m - weight v m by omega,
        Int.pow_succ, Int.pow_succ]
      have hi3 := Int.mul_le_mul_of_nonneg_left hi (show (0 : Int) ≤ 3 by decide)
      family_ring

/-- Sharper height for the same actual cycle-closing form, retaining the prefix
one-count. Neither equal weights nor a common block multiplier is assumed. -/
theorem prefixCycleForm_weight_height (v : Nat → Bool) (m : Nat) (p q : Int) (hq : 0 ≤ q) :
    absInt (prefixCycleForm v m p q) ≤
      (absInt p + q) * ((2 : Int) ^ (m - weight v m) * (3 : Int) ^ weight v m) := by
  let H := (2 : Int) ^ (m - weight v m) * (3 : Int) ^ weight v m
  have hM := weight_le v m
  have h2 := pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) m
  have h3 := pow_nonneg_of_nonneg (x := (3 : Int)) (by decide) (weight v m)
  have hp := Family.pow_ge_one (x := (2 : Int)) (by decide) (m - weight v m)
  have hm := pow_le_pow_of_le (x := (2 : Int)) (y := 3) (by decide) (by decide) (weight v m)
  have ht := Int.mul_le_mul_of_nonneg_left hm
    (pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) (m - weight v m))
  rw [← int_pow_add, Nat.sub_add_cancel hM] at ht
  have hH3 := Int.mul_le_mul_of_nonneg_right hp h3
  have hd : absInt ((2 : Int) ^ m - (3 : Int) ^ weight v m) ≤ H := by
    dsimp [H] at *
    unfold absInt; split <;> omega
  have hc := offset_nonneg v m
  have hcap := offset_weight_upper v m
  have hh := absInt_sub_le (((2 : Int) ^ m - (3 : Int) ^ weight v m) * p) (offset v m * q)
  rw [absInt_mul, absInt_mul, absInt_of_nonneg hc, absInt_of_nonneg hq] at hh
  have hd' := Int.mul_le_mul_of_nonneg_right hd (absInt_nonneg p)
  have hc' := Int.mul_le_mul_of_nonneg_right (show offset v m ≤ H by dsimp [H]; omega) hq
  unfold prefixCycleForm
  dsimp [H] at *
  family_ring

/-- A partial return in a nonperiodic rational itinerary must respect this exact
weight-dependent bound. This can apply even when the prefix is not a square. -/
theorem rational_matching_prefix_weight_bound (v : Nat → Bool) (m ell : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j)))
    (hmatch : ∀ j, j < ell → v (m + j) = v j) :
    (2 : Int) ^ (ell + weight v m) ≤ (absInt p + q) * (3 : Int) ^ weight v m := by
  rcases matching_prefix_divisibility v m ell hr hmatch with ⟨d, hd⟩
  have he := prefixCycleForm_nonzero v m hm hr haper
  have hd0 : d ≠ 0 := by intro hz; rw [hz, Int.mul_zero] at hd; exact he hd
  have hd1 := absInt_pos_of_ne_zero hd0
  have hpow := pow_pos_of_pos (x := (2 : Int)) (by decide) (m + ell)
  have hlo := Int.mul_le_mul_of_nonneg_left hd1 (by omega : 0 ≤ (2 : Int) ^ (m + ell))
  have habs : absInt (prefixCycleForm v m p q) = (2 : Int) ^ (m + ell) * absInt d := by
    rw [hd, absInt_mul, absInt_of_nonneg (by omega)]
  have hhi := prefixCycleForm_weight_height v m p q (by have := hr.1; omega)
  have hbound : (2 : Int) ^ (m + ell) ≤
      (absInt p + q) * ((2 : Int) ^ (m - weight v m) * (3 : Int) ^ weight v m) := by omega
  have hn := weight_le v m
  have hexp : m + ell = (m - weight v m) + (ell + weight v m) := by omega
  rw [hexp, int_pow_add] at hbound
  have hf : (2 : Int) ^ (m - weight v m) * (2 : Int) ^ (ell + weight v m) ≤
      (2 : Int) ^ (m - weight v m) * ((absInt p + q) * (3 : Int) ^ weight v m) := by
    simpa only [Int.mul_assoc, Int.mul_left_comm] using hbound
  exact Int.le_of_mul_le_mul_left hf (pow_pos_of_pos (by decide) _)

/-- Quantitative finite obstruction for any repeated prefix, including partial
repetitions: the precision is m+ell and the height depends only on m. -/
theorem rational_matching_prefix_bound (v : Nat → Bool) (m ell : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j)))
    (hmatch : ∀ j, j < ell → v (m + j) = v j) :
    (2 : Int) ^ (m + ell) ≤ (absInt p + q) * (3 : Int) ^ m := by
  rcases matching_prefix_divisibility v m ell hr hmatch with ⟨d, hd⟩
  have he := prefixCycleForm_nonzero v m hm hr haper
  have hd0 : d ≠ 0 := by intro hz; rw [hz, Int.mul_zero] at hd; exact he hd
  have hd1 := absInt_pos_of_ne_zero hd0
  have hpow := pow_pos_of_pos (x := (2 : Int)) (by decide) (m + ell)
  have hlo := Int.mul_le_mul_of_nonneg_left hd1 (by omega : 0 ≤ (2 : Int) ^ (m + ell))
  have habs : absInt (prefixCycleForm v m p q) = (2 : Int) ^ (m + ell) * absInt d := by
    rw [hd, absInt_mul, absInt_of_nonneg (by omega)]
  have hhi := prefixCycleForm_height v m p q (by have := hr.1; omega)
  omega

/-- A nonperiodic rational orbit cannot have an arbitrarily long square prefix.
The bound applies to negative numerators and unreduced representations. -/
theorem rational_square_prefix_bound (v : Nat → Bool) (m : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j)))
    (hsquare : ∀ j, j < m → v (m + j) = v j) :
    (4 : Int) ^ m ≤ (absInt p + q) * (3 : Int) ^ m := by
  have hh := rational_matching_prefix_bound v m m hm hr haper hsquare
  have h4 : (4 : Int) ^ m = (2 : Int) ^ (m + m) := by
    rw [show m + m = 2 * m by omega, ← int_pow_mul]; rfl
  rwa [← h4] at hh

/-- A genuinely different sufficient criterion: unbounded initial squares and
independent non-eventual-periodicity, with no block contraction hypothesis. -/
theorem no_rational_seed_unbounded_square_prefix (v : Nat → Bool)
    (hsquares : ∀ K : Nat, ∃ m : Nat, K ≤ m ∧ 1 ≤ m ∧
      ∀ j, j < m → v (m + j) = v j)
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j))) (p q : Int) :
    ¬ RealizesWord p q (fun j => bit (v j)) := by
  intro hr
  let C := absInt p + q
  have hC : 1 ≤ C := by have := absInt_nonneg p; have := hr.1; dsimp [C]; omega
  let K := (3 * (C + 1)).toNat
  have hK : (K : Int) = 3 * (C + 1) := Int.toNat_of_nonneg (by omega)
  rcases hsquares K with ⟨m, hKm, hm, hs⟩
  have hb := rational_square_prefix_bound v m hm hr haper hs
  have hg := amplify_integer_gap 4 3 (C + 1) (by decide) (by decide) (by omega) m hm
    (by omega)
  have hp := pow_pos_of_pos (x := (3 : Int)) (by decide) m
  have hh : (C + 2) * (3 : Int) ^ m ≤ C * (3 : Int) ^ m := Int.le_trans (by simpa only [Int.add_assoc] using hg) hb
  have ht := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ 2 by decide)
    (show 0 ≤ (3 : Int) ^ m by omega)
  dsimp [C] at *
  family_ring

end CollatzLab

namespace CollatzLab.Morphism

/-- Equal parent letters have equal literal iterated images, for any two positions. -/
theorem word_power_congr {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) : ∀ k a b,
    word M a = word M b → ∀ j, j < L ^ k →
    word M (L ^ k * a + j) = word M (L ^ k * b + j)
  | 0, a, b, hab, j, hj => by
    have : j = 0 := by simpa using (show j ≤ 0 by simpa using hj)
    subst j
    simpa using hab
  | k + 1, a, b, hab, j, hj => by
    have hdiv : j / L < L ^ k := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      simpa only [Nat.pow_succ] using hj
    have hi := word_power_congr hL M h1 k a b hab (j / L) hdiv
    have he : ∀ a, L ^ (k + 1) * a + j = L * (L ^ k * a + j / L) + j % L := by
      intro a
      rw [Nat.pow_succ, Nat.mul_add]
      have hh := Nat.mod_add_div j L
      have hid : L ^ k * L * a = L * (L ^ k * a) := by ac_rfl
      omega
    rw [he a, he b, word_block hL M h1 _ _ (Nat.mod_lt j (by omega)),
      word_block hL M h1 _ _ (Nat.mod_lt j (by omega)), hi]

/-- A fixed word starting with two equal letters has square prefixes at all levels. -/
theorem initial_double_square {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hdouble : word M 1 = true) (k j : Nat)
    (hj : j < L ^ k) : word M (L ^ k + j) = word M j := by
  have hh := word_power_congr hL M h1 k 1 0 (hdouble.trans (word_zero M).symm) j hj
  simpa using hh

end CollatzLab.Morphism

namespace CollatzLab

/-- A general substitution theorem beyond equal weights and uniform contraction.
Only the repeated first letter and independent aperiodicity are required. -/
theorem no_rational_seed_morphism_initial_double {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true) (hdouble : Morphism.word M 1 = true)
    (haper : ¬ EventuallyPeriodic (Morphism.parityWord M)) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord M) := by
  apply no_rational_seed_unbounded_square_prefix (Morphism.word M) ?_ haper p q
  intro K
  refine ⟨L ^ K, ?_, Nat.pow_pos (by omega), Morphism.initial_double_square hL M h1 hdouble K⟩
  have h0 := nat_lt_pow2 K
  have h2 := Nat.pow_le_pow_left hL K
  omega

end CollatzLab
