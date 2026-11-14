import CollatzLab.MorphismContraction
import CollatzLab.ExponentialGap

/-! Rational exclusion from arbitrarily long square prefixes, without contraction. -/
namespace CollatzLab
open Morphism

def prefixCycleForm (v : Nat → Bool) (m : Nat) (p q : Int) : Int :=
  ((2 : Int) ^ m - (3 : Int) ^ weight v m) * p - offset v m * q

/-- Two consecutive equal blocks impose a modulus of twice the block length
on the period-closing form. This uses the actual signed numerator dynamics. -/
theorem square_prefix_divisibility (v : Nat → Bool) (m : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (hsquare : ∀ j, j < m → v (m + j) = v j) :
    (2 : Int) ^ (m + m) ∣ prefixCycleForm v m p q := by
  have h0 := affine_prefix v q p hr.2.1 0 m (fun j _ => by simpa using hr.2.2 j)
  have h1 := affine_prefix v q p hr.2.1 m m
    (fun j hj => (hr.2.2 (m + j)).trans (congrArg bit (hsquare j hj)))
  simp only [Nat.zero_add, numIter] at h0
  let A := (2 : Int) ^ m
  let B := (3 : Int) ^ weight v m
  have hd : A ∣ B * (numIter q p m - p) := by
    refine ⟨numIter q p (m + m) - numIter q p m, ?_⟩
    dsimp [A, B]
    family_ring
  have hbez : IsBezout A B := IsBezout.pow (show IsBezout 2 3 from ⟨-1, 1, rfl⟩) _ _
  rcases hbez.dvd_of_dvd_mul_left hd with ⟨d, hd⟩
  refine ⟨-d, ?_⟩
  have he : prefixCycleForm v m p q = A * (p - numIter q p m) := by
    dsimp [prefixCycleForm, A]
    family_ring
  rw [he, show p - numIter q p m = -(A * d) by omega, int_pow_add]
  dsimp [A]
  family_ring

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

/-- A nonperiodic rational orbit cannot have an arbitrarily long square prefix.
The bound applies to negative numerators and unreduced representations. -/
theorem rational_square_prefix_bound (v : Nat → Bool) (m : Nat) (hm : 1 ≤ m) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (haper : ¬ EventuallyPeriodic (fun j => bit (v j)))
    (hsquare : ∀ j, j < m → v (m + j) = v j) :
    (4 : Int) ^ m ≤ (absInt p + q) * (3 : Int) ^ m := by
  rcases square_prefix_divisibility v m hr hsquare with ⟨d, hd⟩
  have he := prefixCycleForm_nonzero v m hm hr haper
  have hd0 : d ≠ 0 := by intro hz; rw [hz, Int.mul_zero] at hd; exact he hd
  have hd1 := absInt_pos_of_ne_zero hd0
  have hpow := pow_pos_of_pos (x := (2 : Int)) (by decide) (m + m)
  have hlo := Int.mul_le_mul_of_nonneg_left hd1 (by omega : 0 ≤ (2 : Int) ^ (m + m))
  have habs : absInt (prefixCycleForm v m p q) = (2 : Int) ^ (m + m) * absInt d := by
    rw [hd, absInt_mul, absInt_of_nonneg (by omega)]
  have h4 : (4 : Int) ^ m = (2 : Int) ^ (m + m) := by
    rw [show m + m = 2 * m by omega, ← int_pow_mul]; rfl
  rw [← h4] at hlo habs
  have hhi := prefixCycleForm_height v m p q (by have := hr.1; omega)
  omega

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
