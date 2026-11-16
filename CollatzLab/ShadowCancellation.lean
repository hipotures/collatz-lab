import CollatzLab.FrontierHeight

/-!
# Exact 3-adic non-cancellation, all-level shadow minima, and unconditional two-shadow lower bounds

For the Phase 12/13 substitution `1 -> 100111, 0 -> 111110` (`frontierSix`), the
substituted rational shadows at `L_k = (56 * 6^k - 1) / 5` have raw coordinates
`P_k = shadowNum k` and `Q_k = shadowDen k = a_k * (b_k - 2^(6^k))`, where
`a_k = 3 ^ weight w (3 * 6^k)` is the preperiod denominator factor and
`b_k = 3 ^ weight w (6^k)` is the periodic-tail weight power.

This module proves in the Lean 4 kernel:
1. For every block index `n`, `offset w (6 * (n + 1)) % 3` is `2` when `w n = true`
   and `1` when `w n = false`.
2. For all `k >= 0`, `w (6^k - 1) = true` and `w (3 * 6^k - 1) = false`, so for
   all `k >= 1`, `offset w (6^k) % 3 = 2`, `offset w (3 * 6^k) % 3 = 1`, and
   `shadowNum k % 3 = 2`.
3. Consequently `shadowNum k` is coprime to `3` and to the entire preperiod factor
   `a_k = 3 ^ weight w (3 * 6^k)` for every `k >= 1`.
4. The raw shadow GCD reduces unconditionally to the periodic-tail GCD for all `k >= 1`:
   `gcd(shadowNum k, shadowDen k) = gcd(offset w (6^k), 3 ^ weight w (6^k) - 2^(6^k))`,
   which divides `3 ^ weight w (6^k) - 2^(6^k)`.
5. Every rational pair `(p, q)` with `q > 0` equivalent to the level-`k` shadow
   (`k >= 1`) satisfies `3 ^ weight w (3 * 6^k) ∣ q` and `height p q >= 3 ^ weight w (3 * 6^k)`.
6. For all `k >= 2`, `2 * (shadowCap k)^2 < 2 ^ matchLength k` holds strictly, and
   together with `k = 0, 1` establishes the exact all-level subsequence minimum
   formula `gcd(shadowNum k, shadowDen k) * H w (matchLength k) = height (shadowNum k) (shadowDen k)`
   and the unconditional lower bound `3 ^ weight w (3 * 6^k) <= H w (matchLength k)` for `k >= 1`.
7. For every `k >= 0` and `matchLength k < N <= matchLength (k + 1)`, unconditionally
   either `3 ^ weight w (3 * 6^(k+1)) <= H w N` (when the minimizer at `N` equals the
   level-`(k+1)` shadow) or both `2 ^ matchLength k <= 2 * shadowCap k * H w N` and
   `2 ^ N <= 2 * shadowCap (k + 1) * H w N` hold simultaneously. This removes the
   subexponential-gcd hypothesis from the two-shadow lower bound `B >= (1 - c) / (1 + 5c)`.
-/
namespace CollatzLab.ShadowCancellation
open CollatzLab Morphism RationalHeight FrontierHeight

theorem bit_eq_one_iff (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> decide

theorem bit_eq_zero_iff (b : Bool) : bit b = 0 ↔ b = false := by
  cases b <;> decide

theorem word_col4 (n : Nat) : word frontierSix (6 * n + 4) = true := by
  have h := (frontierSix_columns n).2.2.2.2.1
  exact (bit_eq_one_iff _).1 h

theorem word_col5 (n : Nat) : word frontierSix (6 * n + 5) = word frontierSix n := by
  have h := (frontierSix_columns n).2.2.2.2.2
  change bit (word frontierSix (6 * n + 5)) = bit (word frontierSix n) at h
  cases h1 : word frontierSix (6 * n + 5) <;> cases h2 : word frontierSix n <;>
    simp_all [bit]

theorem word_pow_six_pred : ∀ k : Nat, word frontierSix (6 ^ k - 1) = true
  | 0 => by decide
  | k + 1 => by
    have hp := Nat.pow_pos (a := 6) (by decide) (n := k)
    have hsplit : 6 ^ (k + 1) - 1 = 6 * (6 ^ k - 1) + 5 := by
      rw [Nat.pow_succ]; omega
    rw [hsplit, word_col5]
    exact word_pow_six_pred k

theorem word_three_pow_six_pred : ∀ k : Nat, word frontierSix (3 * 6 ^ k - 1) = false
  | 0 => by decide
  | k + 1 => by
    have hp := Nat.pow_pos (a := 6) (by decide) (n := k)
    have hsplit : 3 * 6 ^ (k + 1) - 1 = 6 * (3 * 6 ^ k - 1) + 5 := by
      rw [Nat.pow_succ]; omega
    rw [hsplit, word_col5]
    exact word_three_pow_six_pred k

theorem pow_two_even_mod_three : ∀ m : Nat, ((2 : Int) ^ (2 * m)) % 3 = 1
  | 0 => by decide
  | m + 1 => by
    have he : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [he, int_pow_add]
    change ((2 : Int) ^ (2 * m) * 4) % 3 = 1
    rw [Int.mul_emod, pow_two_even_mod_three m]
    decide

theorem pow_two_col4_mod_three (n : Nat) : ((2 : Int) ^ (6 * n + 4)) % 3 = 1 := by
  have he : 6 * n + 4 = 2 * (3 * n + 2) := by omega
  rw [he]
  exact pow_two_even_mod_three (3 * n + 2)

theorem pow_two_col5_mod_three (n : Nat) : ((2 : Int) ^ (6 * n + 5)) % 3 = 2 := by
  have he : 6 * n + 5 = (6 * n + 4) + 1 := by omega
  rw [he, Int.pow_succ, Int.mul_emod, pow_two_col4_mod_three n]
  decide

/-- The mod-3 value of `offset w (6 * (n + 1))` depends only on the parent bit `w n`. -/
theorem offset_six_block_mod_three (n : Nat) :
    offset (word frontierSix) (6 * (n + 1)) % 3 =
      if word frontierSix n then 2 else 1 := by
  have he6 : 6 * (n + 1) = (6 * n + 5) + 1 := by omega
  have he5 : 6 * n + 5 = (6 * n + 4) + 1 := by omega
  have hc4 := word_col4 n
  have hc5 := word_col5 n
  have hp4 := pow_two_col4_mod_three n
  have hp5 := pow_two_col5_mod_three n
  rw [he6, offset, hc5]
  cases hw : word frontierSix n
  · simp only [Bool.false_eq_true, if_false]
    rw [he5, offset, hc4]
    simp only [if_true]
    omega
  · simp only [if_true]
    omega

theorem offset_period_mod_three (k : Nat) :
    offset (word frontierSix) (6 ^ (k + 1)) % 3 = 2 := by
  have hp := Nat.pow_pos (a := 6) (by decide) (n := k)
  have he : 6 ^ (k + 1) = 6 * (6 ^ k - 1 + 1) := by
    rw [Nat.pow_succ]; omega
  rw [he, offset_six_block_mod_three (6 ^ k - 1), word_pow_six_pred k]
  rfl

theorem offset_preperiod_mod_three (k : Nat) :
    offset (word frontierSix) (3 * 6 ^ (k + 1)) % 3 = 1 := by
  have hp := Nat.pow_pos (a := 6) (by decide) (n := k)
  have he : 3 * 6 ^ (k + 1) = 6 * (3 * 6 ^ k - 1 + 1) := by
    rw [Nat.pow_succ]; omega
  rw [he, offset_six_block_mod_three (3 * 6 ^ k - 1), word_three_pow_six_pred k]
  rfl

theorem weight_period_pos (k : Nat) :
    1 ≤ weight (word frontierSix) (6 ^ k) := by
  have hg := power_gap k
  have hp := Nat.pow_pos (a := 6) (by decide) (n := k)
  have h2 : (2 : Int) ≤ (2 : Int) ^ (6 ^ k) := by
    have h1 : 6 ^ k = (6 ^ k - 1) + 1 := by omega
    rw [h1, Int.pow_succ]
    have := Family.pow_ge_one (x := (2 : Int)) (by decide) (6 ^ k - 1)
    omega
  by_cases hw : weight (word frontierSix) (6 ^ k) = 0
  · rw [hw] at hg
    change (2 : Int) ^ (6 ^ k) < 1 at hg
    omega
  · omega

theorem pow_three_period_mod_three (k : Nat) :
    ((3 : Int) ^ weight (word frontierSix) (6 ^ k)) % 3 = 0 := by
  have hw := weight_period_pos k
  have he : weight (word frontierSix) (6 ^ k) = (weight (word frontierSix) (6 ^ k) - 1) + 1 := by omega
  rw [he, Int.pow_succ]
  omega

theorem pow_two_period_mod_three (k : Nat) :
    ((2 : Int) ^ (6 ^ (k + 1))) % 3 = 1 := by
  have he : 6 ^ (k + 1) = 2 * (3 * 6 ^ k) := by rw [Nat.pow_succ]; omega
  rw [he]
  exact pow_two_even_mod_three (3 * 6 ^ k)

theorem pow_two_preperiod_mod_three (k : Nat) :
    ((2 : Int) ^ (3 * 6 ^ (k + 1))) % 3 = 1 := by
  have he : 3 * 6 ^ (k + 1) = 2 * (9 * 6 ^ k) := by rw [Nat.pow_succ]; omega
  rw [he]
  exact pow_two_even_mod_three (9 * 6 ^ k)

/-- For all `k >= 1`, `shadowNum k ≡ 2 (mod 3)` (i.e. `-1 mod 3`), so `3` never divides `shadowNum k`. -/
theorem shadowNum_mod_three (k : Nat) :
    shadowNum (k + 1) % 3 = 2 := by
  unfold shadowNum
  have hd := offset_period_mod_three k
  have hc := offset_preperiod_mod_three k
  have hb := pow_three_period_mod_three (k + 1)
  have hv := pow_two_period_mod_three k
  have hu := pow_two_preperiod_mod_three k
  generalize offset (word frontierSix) (6 ^ (k + 1)) = d at hd ⊢
  generalize offset (word frontierSix) (3 * 6 ^ (k + 1)) = c at hc ⊢
  generalize (3 : Int) ^ weight (word frontierSix) (6 ^ (k + 1)) = b at hb ⊢
  generalize (2 : Int) ^ (6 ^ (k + 1)) = V at hv ⊢
  generalize (2 : Int) ^ (3 * 6 ^ (k + 1)) = U at hu ⊢
  have h1 : (U * d) % 3 = 2 := by rw [Int.mul_emod, hu, hd]; decide
  have h2 : (b - V) % 3 = 2 := by omega
  have h3 : (c * (b - V)) % 3 = 2 := by rw [Int.mul_emod, hc, h2]; decide
  omega

theorem isBezout_three_shadowNum (k : Nat) :
    IsBezout 3 (shadowNum (k + 1)) := by
  have hm := shadowNum_mod_three k
  refine ⟨shadowNum (k + 1) / 3 + 1, -1, ?_⟩
  omega

theorem isBezout_preperiod_shadowNum (k : Nat) :
    IsBezout ((3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1))) (shadowNum (k + 1)) :=
  (isBezout_three_shadowNum k).pow_left _

/-- Any pair `(p, q)` representing the same rational as the level-`(k + 1)` shadow
has denominator divisible by the full preperiod power `3 ^ weight w (3 * 6^(k + 1))`. -/
theorem preperiod_dvd_of_shadow_eq (k : Nat) {p q : Int}
    (heq : p * shadowDen (k + 1) = shadowNum (k + 1) * q) :
    (3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ∣ q := by
  apply (isBezout_preperiod_shadowNum k).dvd_of_dvd_mul_left
  rw [← heq]
  unfold shadowDen
  refine ⟨p * ((3 : Int) ^ weight (word frontierSix) (6 ^ (k + 1)) - (2 : Int) ^ (6 ^ (k + 1))), ?_⟩
  ac_rfl

/-- Unconditional height lower bound for any positive-denominator pair representing
the level-`(k + 1)` shadow. -/
theorem preperiod_le_height_of_shadow_eq (k : Nat) {p q : Int}
    (hq : 0 < q) (heq : p * shadowDen (k + 1) = shadowNum (k + 1) * q) :
    3 ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ≤ height p q := by
  rcases preperiod_dvd_of_shadow_eq k heq with ⟨m, hm⟩
  have ha := pow_pos_of_pos (x := (3 : Int)) (by decide) (weight (word frontierSix) (3 * 6 ^ (k + 1)))
  have hmpos : 1 ≤ m := by
    by_cases h : 1 ≤ m
    · exact h
    · have hle : (3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) * m ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
  have hle : (3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ≤ q := by
    have hmul := Int.mul_le_mul_of_nonneg_left hmpos (show 0 ≤ (3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) by omega)
    rw [Int.mul_one] at hmul
    omega
  have hqb := (height_bounds p q).2
  rw [absInt_of_nonneg (by omega)] at hqb
  have htot := Int.le_trans hle hqb
  exact Int.ofNat_le.mp (by simpa only [Int.natCast_pow] using htot)

def tailOffset (k : Nat) : Int :=
  offset (word frontierSix) (6 ^ k)

def tailDen (k : Nat) : Int :=
  (3 : Int) ^ weight (word frontierSix) (6 ^ k) - (2 : Int) ^ (6 ^ k)

theorem tailDen_pos (k : Nat) : 0 < tailDen k := by
  have hg := power_gap k
  unfold tailDen
  omega

theorem tailDen_odd (k : Nat) : tailDen k % 2 = 1 := by
  unfold tailDen
  have ho := odd_pow (x := (3 : Int)) (by decide) (weight (word frontierSix) (6 ^ k))
  have hs : 1 ≤ 6 ^ k := Nat.pow_pos (by decide)
  have he := Family.even_pow (x := (2 : Int)) (by decide) hs
  omega

/-- Because `shadowNum (k + 1)` is coprime to the preperiod power `3 ^ weight w (3 * 6^(k + 1))`,
common divisors of `(shadowNum (k + 1), shadowDen (k + 1))` are exactly common divisors
of the periodic-tail pair `(tailOffset (k + 1), tailDen (k + 1))`. -/
theorem shadow_common_divisor_iff (k : Nat) (g : Int) :
    (g ∣ shadowNum (k + 1) ∧ g ∣ shadowDen (k + 1)) ↔
      (g ∣ tailOffset (k + 1) ∧ g ∣ tailDen (k + 1)) := by
  let a := (3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1))
  let c := offset (word frontierSix) (3 * 6 ^ (k + 1))
  let U := (2 : Int) ^ (3 * 6 ^ (k + 1))
  have hP : shadowNum (k + 1) = -(U * tailOffset (k + 1) + c * tailDen (k + 1)) := rfl
  have hQ : shadowDen (k + 1) = a * tailDen (k + 1) := rfl
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    rcases isBezout_preperiod_shadowNum k with ⟨x, y, hxy⟩
    change a * x + shadowNum (k + 1) * y = 1 at hxy
    have hbg : IsBezout g a := ⟨u * y, x, by rw [hu] at hxy; family_ring⟩
    have htd : g ∣ tailDen (k + 1) := by
      apply hbg.dvd_of_dvd_mul_left
      refine ⟨v, ?_⟩
      rw [← hv, hQ]
    rcases htd with ⟨w, hw⟩
    have hgo : g % 2 = 1 := by
      have ho := tailDen_odd (k + 1)
      rw [hw, Int.mul_emod] at ho
      by_cases h0 : g % 2 = 0
      · rw [h0] at ho; simp at ho
      · omega
    have hU : g ∣ U * tailOffset (k + 1) := by
      refine ⟨-(u + c * w), ?_⟩
      rw [hP, hw] at hu
      family_ring
    have hb2 : IsBezout g 2 := ⟨1, -(g / 2), by omega⟩
    exact ⟨(hb2.pow_right (3 * 6 ^ (k + 1))).dvd_of_dvd_mul_left hU, ⟨w, hw⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨-(U * u + c * v), ?_⟩, ⟨a * v, ?_⟩⟩
    · rw [hP, hu, hv]; family_ring
    · rw [hQ, hv]; family_ring

theorem dvd_natAbs_of_dvd {a b : Int} (h : a ∣ b) : a.natAbs ∣ b.natAbs := by
  rcases h with ⟨k, hk⟩
  refine ⟨k.natAbs, ?_⟩
  rw [hk, Int.natAbs_mul]

theorem shadow_gcd_eq_tail_gcd (k : Nat) :
    (shadowNum (k + 1)).gcd (shadowDen (k + 1)) =
      (tailOffset (k + 1)).gcd (tailDen (k + 1)) := by
  let g1 := (shadowNum (k + 1)).gcd (shadowDen (k + 1))
  let g2 := (tailOffset (k + 1)).gcd (tailDen (k + 1))
  apply Nat.dvd_antisymm
  · have hd1 : (g1 : Int) ∣ shadowNum (k + 1) ∧ (g1 : Int) ∣ shadowDen (k + 1) :=
      ⟨Int.gcd_dvd_left, Int.gcd_dvd_right⟩
    have hd2 := (shadow_common_divisor_iff k (g1 : Int)).1 hd1
    exact Nat.dvd_gcd (dvd_natAbs_of_dvd hd2.1) (dvd_natAbs_of_dvd hd2.2)
  · have hd2 : (g2 : Int) ∣ tailOffset (k + 1) ∧ (g2 : Int) ∣ tailDen (k + 1) :=
      ⟨Int.gcd_dvd_left, Int.gcd_dvd_right⟩
    have hd1 := (shadow_common_divisor_iff k (g2 : Int)).2 hd2
    exact Nat.dvd_gcd (dvd_natAbs_of_dvd hd1.1) (dvd_natAbs_of_dvd hd1.2)

theorem shadow_gcd_dvd_tailDen (k : Nat) :
    ((shadowNum (k + 1)).gcd (shadowDen (k + 1)) : Int) ∣ tailDen (k + 1) := by
  rw [shadow_gcd_eq_tail_gcd k]
  exact Int.gcd_dvd_right

theorem shadow_gcd_bound (k : Nat) :
    ((shadowNum (k + 1)).gcd (shadowDen (k + 1)) : Int) ≤ tailDen (k + 1) := by
  rcases shadow_gcd_dvd_tailDen k with ⟨m, hm⟩
  let g := ((shadowNum (k + 1)).gcd (shadowDen (k + 1)) : Int)
  change tailDen (k + 1) = g * m at hm
  have hpos := tailDen_pos (k + 1)
  have hg : 0 < g := by
    have hq : (shadowDen (k + 1)).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr (by have := (shadow_realized (k + 1)).1; omega)
    have hgp := Nat.gcd_pos_of_pos_right (shadowNum (k + 1)).natAbs (Nat.pos_of_ne_zero hq)
    exact Int.ofNat_lt.mpr hgp
  have hmpos : 1 ≤ m := by
    by_cases h : 1 ≤ m
    · exact h
    · have hle := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ g by omega) (show m ≤ 0 by omega)
      omega
  have hmul := Int.mul_le_mul_of_nonneg_left hmpos (show 0 ≤ g by omega)
  rw [Int.mul_one] at hmul
  omega

def shadowWeight (k : Nat) : Nat :=
  weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k)

def shadowCap (k : Nat) : Nat :=
  14 * 6 ^ k * 3 ^ shadowWeight k

theorem neg_one_pow_bounds : ∀ k : Nat,
    (-1 : Int) ≤ (-1 : Int) ^ k ∧ (-1 : Int) ^ k ≤ 1
  | 0 => by decide
  | k + 1 => by
    have ih := neg_one_pow_bounds k
    rw [Int.pow_succ]
    omega

theorem shadowWeight_step (k : Nat) :
    shadowWeight (k + 1) ≤ 6 * shadowWeight k + 6 := by
  have h0 := shadow_weight_sum k
  have h1 := shadow_weight_sum (k + 1)
  change 7 * (shadowWeight k : Int) = 20 * (6 ^ k : Nat) - 6 * (-1 : Int) ^ k at h0
  change 7 * (shadowWeight (k + 1) : Int) = 20 * (6 ^ (k + 1) : Nat) - 6 * (-1 : Int) ^ (k + 1) at h1
  have hb0 := neg_one_pow_bounds k
  have hb1 := neg_one_pow_bounds (k + 1)
  have hp : (6 ^ (k + 1) : Nat) = 6 ^ k * 6 := Nat.pow_succ 6 k
  rw [hp, Int.natCast_mul] at h1
  have hle : (shadowWeight (k + 1) : Int) ≤ (6 * shadowWeight k + 6 : Nat) := by
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  exact Int.ofNat_le.mp hle

theorem shadowCap_step (k : Nat) :
    shadowCap (k + 1) ≤ (shadowCap k) ^ 6 := by
  let D := 14 * 6 ^ k
  let W := 3 ^ shadowWeight k
  have hS : 1 ≤ 6 ^ k := Nat.pow_pos (by decide)
  have hD : 14 ≤ D := by dsimp [D]; omega
  have hD5 : 4374 ≤ D ^ 5 :=
    Nat.le_trans (by decide : 4374 ≤ 14 ^ 5) (Nat.pow_le_pow_left hD 5)
  have hD6 : 4374 * D ≤ D ^ 6 := by
    have hm := Nat.mul_le_mul_right D hD5
    simpa only [Nat.pow_succ] using hm
  have hW : 3 ^ shadowWeight (k + 1) ≤ 729 * W ^ 6 := by
    have hw := Nat.pow_le_pow_right (n := 3) (by decide) (shadowWeight_step k)
    have he : 3 ^ (6 * shadowWeight k + 6) = 729 * W ^ 6 := by
      rw [Nat.pow_add, Nat.mul_comm 6 (shadowWeight k), Nat.pow_mul]
      dsimp [W]; omega
    omega
  have h1 : shadowCap (k + 1) = 6 * D * 3 ^ shadowWeight (k + 1) := by
    dsimp [shadowCap, D]
    rw [Nat.pow_succ]
    ac_rfl
  have h2 : 6 * D * 3 ^ shadowWeight (k + 1) ≤ 6 * D * (729 * W ^ 6) :=
    Nat.mul_le_mul_left (6 * D) hW
  have h3 : 6 * D * (729 * W ^ 6) = (4374 * D) * W ^ 6 := by
    change 6 * D * (729 * W ^ 6) = 6 * 729 * D * W ^ 6
    ac_rfl
  have h4 : (4374 * D) * W ^ 6 ≤ D ^ 6 * W ^ 6 :=
    Nat.mul_le_mul_right (W ^ 6) hD6
  have h5 : D ^ 6 * W ^ 6 = (shadowCap k) ^ 6 := by
    dsimp [shadowCap, D, W]
    exact (Nat.mul_pow (14 * 6 ^ k) (3 ^ shadowWeight k) 6).symm
  omega

theorem pow_six_lt_pow_six {a b : Nat} (ha : 0 < a) (hab : a < b) : a ^ 6 < b ^ 6 := by
  have h1 : a ≤ b := Nat.le_of_lt hab
  have h2 := Nat.pow_le_pow_left h1 5
  have h3 : a ^ 5 * a < a ^ 5 * b :=
    Nat.mul_lt_mul_of_pos_left hab (Nat.pow_pos ha)
  have h4 : a ^ 5 * b ≤ b ^ 5 * b := Nat.mul_le_mul_right b h2
  simpa only [Nat.pow_succ] using Nat.lt_of_lt_of_le h3 h4

set_option exponentiation.threshold 512 in
theorem shadow_strict_uniqueness_ge_two : ∀ k : Nat,
    2 * (shadowCap (k + 2)) * (shadowCap (k + 2)) < 2 ^ matchLength (k + 2)
  | 0 => by
    have h2 := shadow_weight_sum 2
    change 7 * (shadowWeight 2 : Int) = 20 * (6 ^ 2 : Nat) - 6 * (-1 : Int) ^ 2 at h2
    have hw2 : shadowWeight 2 = 102 := by omega
    change 2 * shadowCap 2 * shadowCap 2 < 2 ^ matchLength 2
    unfold shadowCap
    rw [hw2]
    decide
  | k + 1 => by
    have ih := shadow_strict_uniqueness_ge_two k
    let C := shadowCap (k + 2)
    let L := matchLength (k + 2)
    change 2 * C * C < 2 ^ L at ih
    have hCpos : 0 < 2 * C * C := by
      have hS : 1 ≤ 6 ^ (k + 2) := Nat.pow_pos (by decide)
      have hW : 1 ≤ 3 ^ shadowWeight (k + 2) := Nat.pow_pos (by decide)
      have hC : 1 ≤ C := Nat.mul_pos (by omega) hW
      exact Nat.mul_pos (Nat.mul_pos (by decide) hC) hC
    have hstep : shadowCap (k + 3) ≤ C ^ 6 := shadowCap_step (k + 2)
    have hsq1 : shadowCap (k + 3) * shadowCap (k + 3) ≤ C ^ 6 * C ^ 6 :=
      Nat.mul_le_mul hstep hstep
    have hsq2 : 2 * shadowCap (k + 3) * shadowCap (k + 3) ≤ (2 * C * C) ^ 6 := by
      have hm1 := Nat.mul_le_mul_left 2 hsq1
      have hm2 : 2 * (C ^ 6 * C ^ 6) ≤ 64 * (C ^ 6 * C ^ 6) :=
        Nat.mul_le_mul_right (C ^ 6 * C ^ 6) (by decide : 2 ≤ 64)
      have he1 : 2 * shadowCap (k + 3) * shadowCap (k + 3) =
          2 * (shadowCap (k + 3) * shadowCap (k + 3)) := Nat.mul_assoc ..
      have he2 : (2 * C * C) ^ 6 = 64 * (C ^ 6 * C ^ 6) := by
        rw [Nat.mul_pow (2 * C) C 6, Nat.mul_pow 2 C 6]
        change 64 * C ^ 6 * C ^ 6 = 64 * (C ^ 6 * C ^ 6)
        exact Nat.mul_assoc 64 (C ^ 6) (C ^ 6)
      omega
    have hlt1 : (2 * C * C) ^ 6 < (2 ^ L) ^ 6 := pow_six_lt_pow_six hCpos ih
    have hlt2 : (2 ^ L) ^ 6 < 2 ^ matchLength (k + 3) := by
      rw [← Nat.pow_mul, Nat.mul_comm L 6]
      change 2 ^ (6 * L) < 2 ^ (6 * L + 1)
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ (6 * L) := Nat.pow_pos (by decide)
      omega
    exact Nat.lt_of_le_of_lt hsq2 (Nat.lt_trans hlt1 hlt2)

theorem shadow_unreduced_strict_uniqueness (k : Nat) :
    2 * height (shadowNum (k + 1)) (shadowDen (k + 1)) *
      height (shadowNum (k + 1)) (shadowDen (k + 1)) < 2 ^ matchLength (k + 1) := by
  cases k with
  | zero => decide
  | succ k =>
    let h := height (shadowNum (k + 2)) (shadowDen (k + 2))
    let C := shadowCap (k + 2)
    have hb : h ≤ C := shadow_height_bound (k + 2)
    have h1 : h * h ≤ C * C := Nat.mul_le_mul hb hb
    have h2 : 2 * (h * h) ≤ 2 * (C * C) := Nat.mul_le_mul_left 2 h1
    have he1 : 2 * h * h = 2 * (h * h) := Nat.mul_assoc 2 h h
    have he2 : 2 * C * C = 2 * (C * C) := Nat.mul_assoc 2 C C
    have hmul : 2 * h * h ≤ 2 * C * C := by omega
    exact Nat.lt_of_le_of_lt hmul (shadow_strict_uniqueness_ge_two k)

/-- At every level `k + 1 >= 1`, any minimizing pair `(p, q)` at `matchLength (k + 1)`
represents the exact same rational number as `(shadowNum (k + 1), shadowDen (k + 1))`. -/
theorem H_shadow_minimizer_eq (k : Nat) {p q : Int}
    (hqo : q % 2 = 1)
    (hp : Prefix q p (word frontierSix) (matchLength (k + 1)))
    (he : height p q = H (word frontierSix) (matchLength (k + 1))) :
    p * shadowDen (k + 1) = shadowNum (k + 1) * q := by
  let P := shadowNum (k + 1)
  let Q := shadowDen (k + 1)
  let B := height P Q
  have hr := shadow_realized (k + 1)
  have hsh := shadow_prefix (k + 1)
  have hmin : H (word frontierSix) (matchLength (k + 1)) ≤ B :=
    (H_spec (word frontierSix) (matchLength (k + 1))).2 P Q hr.1 hr.2.1 hsh
  have h1 : height p q ≤ B := by rw [he]; exact hmin
  exact bounded_height_unique hqo hr.2.1 hp hsh h1 (Nat.le_refl B)
    (shadow_unreduced_strict_uniqueness k)

/-- Unconditional all-level lower bound on the shadow subsequence minima `H w (matchLength (k + 1))`. -/
theorem H_shadow_lower (k : Nat) :
    3 ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ≤
      H (word frontierSix) (matchLength (k + 1)) := by
  rcases (H_spec (word frontierSix) (matchLength (k + 1))).1 with ⟨p, q, hqp, hqo, hp, he⟩
  have heq := H_shadow_minimizer_eq k hqo hp he
  rw [← he]
  exact preperiod_le_height_of_shadow_eq k hqp heq

/-- Exact all-level subsequence minimum formula: for every `k >= 0`,
`gcd(shadowNum k, shadowDen k) * H w (matchLength k) = height (shadowNum k) (shadowDen k)`. -/
theorem H_shadow_exact : ∀ k : Nat,
    ((shadowNum k).gcd (shadowDen k)) * H (word frontierSix) (matchLength k) =
      height (shadowNum k) (shadowDen k)
  | 0 => by
    rw [show matchLength 0 = 11 from rfl, H_eleven]
    decide
  | k + 1 => by
    let P := shadowNum (k + 1)
    let Q := shadowDen (k + 1)
    let L := matchLength (k + 1)
    rcases (H_spec (word frontierSix) L).1 with ⟨p, q, hqp, hqo, hp, he⟩
    have hcop : Nat.gcd p.natAbs q.natAbs = 1 :=
      minimizer_primitive hqp hqo hp he
    have heq := H_shadow_minimizer_eq k hqo hp he
    have habs : p.natAbs * Q.natAbs = P.natAbs * q.natAbs := by
      have h := congrArg Int.natAbs heq
      simpa only [Int.natAbs_mul] using h
    have hQ : Q.natAbs = P.gcd Q * q.natAbs := by
      calc Q.natAbs
        _ = 1 * Q.natAbs := (Nat.one_mul _).symm
        _ = Nat.gcd p.natAbs q.natAbs * Q.natAbs := by rw [hcop]
        _ = Nat.gcd (p.natAbs * Q.natAbs) (q.natAbs * Q.natAbs) := (Nat.gcd_mul_right ..).symm
        _ = Nat.gcd (P.natAbs * q.natAbs) (Q.natAbs * q.natAbs) := by
          rw [habs, Nat.mul_comm q.natAbs Q.natAbs]
        _ = P.gcd Q * q.natAbs := Nat.gcd_mul_right ..
    have hP : P.natAbs = P.gcd Q * p.natAbs := by
      calc P.natAbs
        _ = P.natAbs * 1 := (Nat.mul_one _).symm
        _ = P.natAbs * Nat.gcd p.natAbs q.natAbs := by rw [hcop]
        _ = Nat.gcd (P.natAbs * p.natAbs) (P.natAbs * q.natAbs) := (Nat.gcd_mul_left ..).symm
        _ = Nat.gcd (P.natAbs * p.natAbs) (Q.natAbs * p.natAbs) := by
          rw [← habs, Nat.mul_comm p.natAbs Q.natAbs]
        _ = P.gcd Q * p.natAbs := Nat.gcd_mul_right ..
    unfold height at he ⊢
    change P.gcd Q * H (word frontierSix) L = max P.natAbs Q.natAbs
    rw [← he, hP, hQ]
    exact (Nat.mul_max_mul_left (P.gcd Q) p.natAbs q.natAbs).symm

theorem shadowCap_cast (k : Nat) :
    (shadowCap k : Int) =
      14 * (6 ^ k : Nat) * (3 : Int) ^
        (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k)) := by
  unfold shadowCap shadowWeight
  simp only [Int.natCast_mul, Int.natCast_pow]
  rfl

/-- Unconditional two-shadow dichotomy for every `N` in `(matchLength k, matchLength (k + 1)]`:
either the minimizer at `N` is the level-`(k + 1)` shadow (forcing `H w N >= 3 ^ weight w (3 * 6^(k + 1))`),
or it differs from both adjacent shadows (forcing both cross-product lower bounds simultaneously). -/
theorem H_two_shadow_dichotomy (k N : Nat)
    (hlo : matchLength k < N) (hhi : N ≤ matchLength (k + 1)) :
    3 ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ≤ H (word frontierSix) N ∨
      ((2 : Int) ^ matchLength k ≤
        2 * (shadowCap k : Int) * (H (word frontierSix) N : Int) ∧
       (2 : Int) ^ N ≤
        2 * (shadowCap (k + 1) : Int) * (H (word frontierSix) N : Int)) := by
  rcases (H_spec (word frontierSix) N).1 with ⟨p, q, hqp, hqo, hp, he⟩
  by_cases heq : p * shadowDen (k + 1) = shadowNum (k + 1) * q
  · left
    rw [← he]
    exact preperiod_le_height_of_shadow_eq k hqp heq
  · right
    refine ⟨?_, ?_⟩
    · rw [shadowCap_cast k]
      exact H_after_shadow k N hlo
    · have hr := shadow_realized (k + 1)
      have hsh := shadow_prefix (k + 1)
      have hsep := same_prefix_height_separation hqo hr.2.1
        hp (fun j hj => hsh j (by omega)) heq
      have hcap := Int.ofNat_le.mpr (shadow_height_bound (k + 1))
      change (height (shadowNum (k + 1)) (shadowDen (k + 1)) : Int) ≤ (shadowCap (k + 1) : Int) at hcap
      rw [he] at hsep
      have hm := Int.mul_le_mul_of_nonneg_left hcap
        (show 0 ≤ 2 * (H (word frontierSix) N : Int) by omega)
      have hcomm1 : 2 * (H (word frontierSix) N : Int) *
          (height (shadowNum (k + 1)) (shadowDen (k + 1)) : Int) ≤
            2 * (H (word frontierSix) N : Int) * (shadowCap (k + 1) : Int) := by
        simpa only [Int.mul_assoc] using hm
      have hcomm2 : 2 * (H (word frontierSix) N : Int) * (shadowCap (k + 1) : Int) =
          2 * (shadowCap (k + 1) : Int) * (H (word frontierSix) N : Int) := by ac_rfl
      omega

/-- Exact shadow plateau theorem: for every `k` and `N <= matchLength k` inside the strict
uniqueness box `2 * height(P_k, Q_k)^2 < 2^N`, the height is constant: `H w N = H w (matchLength k)`. -/
theorem H_shadow_plateau (k N : Nat) (hhi : N ≤ matchLength k)
    (hsmall : 2 * height (shadowNum k) (shadowDen k) *
      height (shadowNum k) (shadowDen k) < 2 ^ N) :
    H (word frontierSix) N = H (word frontierSix) (matchLength k) := by
  have hle : H (word frontierSix) N ≤ H (word frontierSix) (matchLength k) :=
    H_mono (word frontierSix) hhi
  rcases (H_spec (word frontierSix) N).1 with ⟨p, q, hqp, hqo, hp, he⟩
  let P := shadowNum k
  let Q := shadowDen k
  let B := height P Q
  have hr := shadow_realized k
  have hsh := shadow_prefix k
  have hB : H (word frontierSix) (matchLength k) ≤ B :=
    (H_spec (word frontierSix) (matchLength k)).2 P Q hr.1 hr.2.1 hsh
  have hpB : height p q ≤ B := by omega
  have heq : p * Q = P * q :=
    bounded_height_unique hqo hr.2.1 hp (fun j hj => hsh j (by omega))
      hpB (Nat.le_refl B) hsmall
  have hfull : Prefix q p (word frontierSix) (matchLength k) := by
    intro j hj
    rw [(numIter_equiv hqo hr.2.1 heq j).2]
    exact hsh j hj
  have hge : H (word frontierSix) (matchLength k) ≤ H (word frontierSix) N := by
    rw [← he]
    exact (H_spec (word frontierSix) (matchLength k)).2 p q hqp hqo hfull
  omega

theorem H_shadow_plateau_cap (k N : Nat) (hhi : N ≤ matchLength k)
    (hsmall : 2 * shadowCap k * shadowCap k < 2 ^ N) :
    H (word frontierSix) N = H (word frontierSix) (matchLength k) := by
  let h := height (shadowNum k) (shadowDen k)
  let C := shadowCap k
  have hb : h ≤ C := shadow_height_bound k
  have h1 : h * h ≤ C * C := Nat.mul_le_mul hb hb
  have h2 : 2 * (h * h) ≤ 2 * (C * C) := Nat.mul_le_mul_left 2 h1
  have he1 : 2 * h * h = 2 * (h * h) := Nat.mul_assoc 2 h h
  have he2 : 2 * C * C = 2 * (C * C) := Nat.mul_assoc 2 C C
  change 2 * C * C < 2 ^ N at hsmall
  have hmul : 2 * h * h < 2 ^ N := by omega
  exact H_shadow_plateau k N hhi hmul

/-- Exact 67-bit minimum `H w 67 = 297087259`, proved in the kernel from `H_shadow_exact 1`. -/
theorem H_sixty_seven : H (word frontierSix) 67 = 297087259 := by
  have h := H_shadow_exact 1
  have hgcd : (shadowNum 1).gcd (shadowDen 1) = 1 := by decide
  have hht : height (shadowNum 1) (shadowDen 1) = 297087259 := by decide
  have hlen : matchLength 1 = 67 := rfl
  rw [hgcd, hht, hlen, Nat.one_mul] at h
  exact h

/-- Kernel-verified plateau at level 1: for all `59 <= N <= 67`, `H w N = 297087259`. -/
theorem H_level_one_plateau (N : Nat) (hlo : 59 ≤ N) (hhi : N ≤ 67) :
    H (word frontierSix) N = 297087259 := by
  have hbase : 2 * height (shadowNum 1) (shadowDen 1) *
      height (shadowNum 1) (shadowDen 1) < 2 ^ 59 := by decide
  have hpow : 2 ^ 59 ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) hlo
  have hplat := H_shadow_plateau 1 N hhi (Nat.lt_of_lt_of_le hbase hpow)
  rw [show matchLength 1 = 67 from rfl, H_sixty_seven] at hplat
  exact hplat

/-- Kernel-verified jump after `N = 67`: for all `N > 67`, `248368026765 <= H w N`. -/
theorem H_after_sixty_seven (N : Nat) (hN : 67 < N) :
    248368026765 ≤ H (word frontierSix) N := by
  have hcross := shadow_crossing (shadow_realized 1).2.1 (shadow_prefix 1) (shadow_failure 1)
  have hht : (height (shadowNum 1) (shadowDen 1) : Int) = 297087259 := by decide
  have hlen : matchLength 1 = 67 := rfl
  rw [hht, hlen] at hcross
  have hm := Int.ofNat_le.mpr (H_mono (word frontierSix) (show 67 + 1 ≤ N by omega))
  have hle : (248368026765 : Int) ≤ (H (word frontierSix) N : Int) := by omega
  exact Int.ofNat_le.mp hle

end CollatzLab.ShadowCancellation
