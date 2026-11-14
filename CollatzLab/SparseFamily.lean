import CollatzLab.UnequalSparse
import CollatzLab.FamilyTower

/-! Uniform exact contraction for the entire sparse/dense unequal-weight family. -/
namespace CollatzLab

theorem absInt_pow_eq (x : Int) : ∀ k, absInt (x ^ k) = absInt x ^ k
  | 0 => rfl
  | k + 1 => by rw [Int.pow_succ, absInt_mul, absInt_pow_eq, Int.pow_succ]

/-- A finite second-order binomial lower bound, in integer arithmetic. -/
theorem second_order_binomial_lower (x : Int) (hx : 0 ≤ x) : ∀ n : Nat,
    x ^ (n + 2) + 2 * ((n : Int) + 2) * x ^ (n + 1) +
      2 * ((n : Int) + 2) * ((n : Int) + 1) * x ^ n ≤ (x + 2) ^ (n + 2)
  | 0 => by simp only [Int.pow_succ, Int.pow_zero]; family_ring
  | n + 1 => by
    have hi := second_order_binomial_lower x hx n
    have hm := Int.mul_le_mul_of_nonneg_right hi (show 0 ≤ x + 2 by omega)
    have he : 0 ≤ 4 * ((n : Int) + 2) * ((n : Int) + 1) * x ^ n :=
      Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) (by omega)) (by omega))
        (pow_nonneg_of_nonneg hx n)
    simp only [Int.pow_succ, Int.pow_zero, Int.natCast_add, Int.natCast_one] at *
    family_ring

/-- A uniform power gap from the finite binomial inequality. -/
theorem four_times_power_le (t : Nat) :
    4 * (t : Int) ^ (t + 2) ≤ ((t : Int) + 2) ^ (t + 2) := by
  have hi := second_order_binomial_lower (t : Int) (by omega) t
  have hp := pow_nonneg_of_nonneg (x := (t : Int)) (by omega) t
  have hpoly : 4 * (t : Int) ^ 2 ≤ (t : Int) ^ 2 +
      2 * ((t : Int) + 2) * (t : Int) + 2 * ((t : Int) + 2) * ((t : Int) + 1) := by
    have hs := Int.mul_nonneg (show (0 : Int) ≤ t by omega) (show (0 : Int) ≤ t by omega)
    simp only [Int.pow_succ, Int.pow_zero]
    family_ring
  have hm := Int.mul_le_mul_of_nonneg_left hpoly hp
  simp only [Int.pow_succ, Int.pow_zero] at *
  family_ring

theorem quarter_power_gap (L : Nat) (hL : 2 ≤ L) :
    4 * (((L - 2) ^ L : Nat) : Int) ≤ ((L ^ L : Nat) : Int) := by
  have hh := four_times_power_le (L - 2)
  rw [show L - 2 + 2 = L by omega,
    show ((L - 2 : Nat) : Int) + 2 = (L : Int) by omega] at hh
  simpa only [Int.natCast_pow] using hh

/-- A rational density margin proved without real logarithms. -/
theorem five_eighths_contraction (S R : Nat) (hS : 1 ≤ S) (hR : 8 * R ≤ 5 * S) :
    (3 : Int) ^ R < (2 : Int) ^ S := by
  have hm : (3 : Int) ^ (8 * R) ≤ (3 : Int) ^ (5 * S) := by
    have hh := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) hR)
    simpa only [Int.natCast_pow] using hh
  have hs := Family.pow_strict (x := (3 : Int) ^ 5) (y := (2 : Int) ^ 8)
    (by decide) (by decide) S hS
  rw [int_pow_mul, int_pow_mul] at hs
  by_cases hgap : (3 : Int) ^ R < (2 : Int) ^ S
  · exact hgap
  · have hh := pow_le_pow_of_le (x := (2 : Int) ^ S) (y := (3 : Int) ^ R)
      (pow_nonneg_of_nonneg (by decide) S) (by omega) 8
    rw [int_pow_mul, int_pow_mul, Nat.mul_comm S 8, Nat.mul_comm R 8] at hh
    omega

namespace Morphism

theorem weight_initial_ones (t : Nat) : ∀ n,
    weight (fun j => decide (j < t)) n = min n t
  | 0 => by simp [weight]
  | n + 1 => by
    rw [weight, weight_initial_ones t n]
    by_cases hn : n < t <;> simp [hn] <;> omega

theorem weight_singleton_one : ∀ n,
    weight (fun j => decide (j = 0)) (n + 1) = 1
  | 0 => by decide
  | n + 1 => by rw [weight, weight_singleton_one n]; simp

theorem unequalSparse_one_image (L : Nat) (hL : 1 ≤ L) (j : Nat) :
    image (unequalSparse L) true j = decide (j = 0) := by
  by_cases hj : j < L
  · simp [image, unequalSparse, hj]
  · simp [image, hj, show j ≠ 0 by omega]

theorem unequalSparse_zero_image (L j : Nat) :
    image (unequalSparse L) false j = decide (j < L - 1) := by
  by_cases hj : j < L
  · simp [image, unequalSparse, hj]
  · simp [image, hj, show ¬j < L - 1 by omega]

theorem unequalSparse_weights (L : Nat) (hL : 3 ≤ L) :
    weight (image (unequalSparse L) true) L = 1 ∧
    weight (image (unequalSparse L) false) L = L - 1 := by
  constructor
  · have hh := (common_prefix _ (fun j => decide (j = 0)) L
      (fun j _ => unequalSparse_one_image L (by omega) j)).1
    rw [hh, show L = (L - 1) + 1 by omega]
    exact weight_singleton_one _
  · have hh := (common_prefix _ (fun j => decide (j < L - 1)) L
      (fun j _ => unequalSparse_zero_image L j)).1
    rw [hh, weight_initial_ones]
    omega

theorem unequalSparse_parameters (L : Nat) (hL : 3 ≤ L) :
    frequencyDen (unequalSparse L) = 2 * ((L : Int) - 1) ∧
    weightDelta (unequalSparse L) = 2 - (L : Int) := by
  have hw := unequalSparse_weights L hL
  unfold frequencyDen weightDelta
  rw [hw.1, hw.2]
  constructor <;> omega

/-- Exact scalar balance for every parent bit at every level. -/
theorem unequalSparse_power_balance (L : Nat) (hL : 3 ≤ L) (k a : Nat) :
    2 * (weight (fun j => word (unequalSparse L) (L ^ k * a + j)) (L ^ k) : Int) -
      (L ^ k : Nat) = if word (unequalSparse L) a then (2 - (L : Int)) ^ k else
        -((2 - (L : Int)) ^ k) := by
  let M := unequalSparse L
  have hw := unequalSparse_weights L hL
  have hparam := unequalSparse_parameters L hL
  have hzero : (weight (image M false) L : Int) = (L : Int) - 1 := by
    dsimp [M]; rw [hw.2]; omega
  have hbase : balance M a 1 = ((L : Int) - 1) * (if word M a then 1 else -1) := by
    unfold balance
    rw [hparam.1, hzero]
    cases hb : word M a <;> simp [weight, hb] <;> family_ring
  have hh := balance_power (by omega) M (unequalSparse_prolongable L (by omega)) k a 1
  rw [Nat.mul_one, hbase] at hh
  unfold balance at hh
  rw [hparam.1, hparam.2, hzero] at hh
  dsimp [M] at hh
  cases hb : word (unequalSparse L) a <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at hh ⊢
  all_goals
    apply Int.eq_of_mul_eq_mul_left (a := (L : Int) - 1) (by omega)
    family_ring

/-- A computable uniform bound on every aligned iterated-image weight, with
the spectral transient term retained exactly. -/
theorem unequalSparse_power_weight_bound (L : Nat) (hL : 3 ≤ L) (k a : Nat) :
    weight (fun j => word (unequalSparse L) (L ^ k * a + j)) (L ^ k) ≤
      (L ^ k + (L - 2) ^ k) / 2 := by
  have hh := unequalSparse_power_balance L hL k a
  have habs : absInt ((2 - (L : Int)) ^ k) = (((L - 2) ^ k : Nat) : Int) := by
    rw [absInt_pow_eq, Int.natCast_pow]
    congr 1
    unfold absInt
    split <;> omega
  have hlo : -((((L - 2) ^ k : Nat) : Int)) ≤ (2 - (L : Int)) ^ k := by
    unfold absInt at habs
    split at habs <;> omega
  have hhi : (2 - (L : Int)) ^ k ≤ (((L - 2) ^ k : Nat) : Int) := by
    unfold absInt at habs
    split at habs <;> omega
  cases word (unequalSparse L) a <;> simp only [Bool.false_eq_true, if_false, if_true] at hh
  all_goals omega

theorem unequalSparse_uniform_margin (L : Nat) (hL : 3 ≤ L) :
    8 * ((L ^ L + (L - 2) ^ L) / 2) ≤ 5 * L ^ L := by
  have hh := quarter_power_gap L (by omega)
  omega

end Morphism

/-- Every length in this explicit unequal sparse/dense family has a finite
uniform contraction proof; this is not a claim about arbitrary unequal images. -/
theorem no_rational_seed_realizes_unequalSparse (L : Nat) (hL : 3 ≤ L) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord (Morphism.unequalSparse L)) :=
  no_rational_seed_uniform_block_contraction (Morphism.word (Morphism.unequalSparse L))
    (L ^ L) ((L ^ L + (L - 2) ^ L) / 2) (Nat.pow_pos (by omega))
    (Morphism.unequalSparse_power_weight_bound L hL L)
    (five_eighths_contraction _ _ (Nat.pow_pos (by omega))
      (Morphism.unequalSparse_uniform_margin L hL))
    (Morphism.unequalSparse_not_eventually_periodic L hL) p q

theorem no_rational_seed_realizes_shifted_unequalSparse (L : Nat) (hL : 3 ≤ L)
    (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord (Morphism.unequalSparse L)) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    (no_rational_seed_realizes_unequalSparse L hL) t p q

theorem no_eventually_shifted_unequalSparse_itinerary (L : Nat) (hL : 3 ≤ L)
    (s t : Nat) (p q : Int) (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord (Morphism.unequalSparse L) (t + j)) :=
  no_eventually_shifted_itinerary_of_exclusion _ (Morphism.parity_binary _)
    (no_rational_seed_realizes_unequalSparse L hL) s t p q hq ho

theorem no_int_seed_realizes_shifted_unequalSparse (L : Nat) (hL : 3 ≤ L)
    (t : Nat) (p : Int) :
    ¬ RealizesWord p 1 (shiftWord (Morphism.parityWord (Morphism.unequalSparse L)) t) :=
  no_rational_seed_realizes_shifted_unequalSparse L hL t p 1

theorem no_int_orbit_enters_shifted_unequalSparse (L : Nat) (hL : 3 ≤ L)
    (s t : Nat) (p : Int) :
    ¬ RealizesWord (tIterInt p s) 1
      (shiftWord (Morphism.parityWord (Morphism.unequalSparse L)) t) :=
  no_int_seed_realizes_shifted_unequalSparse L hL t (tIterInt p s)

end CollatzLab
