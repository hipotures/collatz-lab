/-
  CollatzLab.Pade:
  Formalization of the degree-4 Padé approximant `(p_0, p_1) = (1 + z + z^2, -1 + z^4)`
  (`N = 14, c = 1`), the integer linear form `E_k = D_k P_0(a_k, b_k) + u_k P_1(a_k, b_k)`,
  its exact 2-adic valuation `v_2(E_k) = 56 * 4^k`, the quantitative height bound
  `a_k b_k^2 + a_k^3 ≤ (15760/19683) b_k^3 < b_k^3`, `H_{k+1} ≤ b_k^7 H_k`,
  `|E_k| < 3 H_0 3^(19 * 4^k)`, and Theorem 7.1 (`no_rational_seed_realizes_w`).
-/
import CollatzLab.Tower

namespace CollatzLab

/-- Homogenised degree-4 Padé polynomial `P_0(a, b) = b^4 + a*b^3 + a^2*b^2`. -/
def P0 (a b : Int) : Int :=
  b ^ 4 + a * (b ^ 3) + (a ^ 2) * (b ^ 2)

/-- Homogenised degree-4 Padé polynomial `P_1(a, b) = -b^4 + a^4`. -/
def P1 (a b : Int) : Int :=
  -(b ^ 4) + a ^ 4

/-- Level-`k` degree-4 Padé integer linear form `E_k = D_k P_0(a_k, b_k) + u_k P_1(a_k, b_k)`. -/
def eForm (p q : Int) (k : Nat) : Int :=
  dTower q k * P0 (aTower k) (bTower k) + uTower p q k * P1 (aTower k) (bTower k)

/-- Integer absolute value `|x| ∈ ℤ`. -/
def absInt (x : Int) : Int :=
  if x ≥ 0 then x else -x

theorem absInt_eq_natAbs (x : Int) : absInt x = (x.natAbs : Int) := by
  unfold absInt; omega

theorem absInt_nonneg (x : Int) : 0 ≤ absInt x := by
  unfold absInt; omega

theorem absInt_of_nonneg {x : Int} (hx : 0 ≤ x) : absInt x = x := by
  unfold absInt; omega

theorem absInt_add_le (x y : Int) : absInt (x + y) ≤ absInt x + absInt y := by
  unfold absInt; omega

theorem absInt_sub_le (x y : Int) : absInt (x - y) ≤ absInt x + absInt y := by
  unfold absInt; omega

theorem absInt_pos_of_ne_zero {x : Int} (hx : x ≠ 0) : 1 ≤ absInt x := by
  unfold absInt; omega

theorem absInt_mul (x y : Int) : absInt (x * y) = absInt x * absInt y := by
  rw [absInt_eq_natAbs, absInt_eq_natAbs, absInt_eq_natAbs, Int.natAbs_mul, Int.ofNat_mul]

/-- Level-`k` archimedean height `H_k = |u_k| + D_k`. -/
def hTower (p q : Int) (k : Nat) : Int :=
  absInt (uTower p q k) + dTower q k

/-- Fuel-based structural 2-adic valuation on `Nat` (`v2Nat 0 = 0`). -/
def v2NatAux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n =>
    if n % 2 = 0 then 1 + v2NatAux fuel (n / 2) else 0

/-- Exact 2-adic valuation on natural numbers. -/
def v2Nat (n : Nat) : Nat :=
  v2NatAux n n

/-- Exact 2-adic valuation on integers `v_2(z) = v_2(|z|)`. -/
def v2Int (z : Int) : Nat :=
  v2Nat z.natAbs

theorem v2NatAux_step (fuel n : Nat) (hn : n > 0) :
    v2NatAux (fuel + 1) n = if n % 2 = 0 then 1 + v2NatAux fuel (n / 2) else 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

theorem v2NatAux_eq_of_le : ∀ (f1 f2 n : Nat), n ≤ f1 → n ≤ f2 → v2NatAux f1 n = v2NatAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by
    have hn : n = 0 := by omega
    subst hn; rfl
  | _ + 1, 0, n, _, h2 => by
    have hn : n = 0 := by omega
    subst hn; rfl
  | f1 + 1, f2 + 1, n, h1, h2 => by
    by_cases hn : n = 0
    · subst hn; rfl
    · rw [v2NatAux_step f1 n (by omega), v2NatAux_step f2 n (by omega)]
      split
      · rw [v2NatAux_eq_of_le f1 f2 (n / 2) (by omega) (by omega)]
      · rfl

theorem v2NatAux_ge (fuel n : Nat) (h : n ≤ fuel) : v2NatAux fuel n = v2Nat n :=
  v2NatAux_eq_of_le fuel n n h (Nat.le_refl n)

theorem v2Nat_odd {u : Nat} (hu : u % 2 = 1) : v2Nat u = 0 := by
  rw [← v2NatAux_ge (u + 1) u (by omega), v2NatAux_step u u (by omega)]
  have hmod : ¬ (u % 2 = 0) := by omega
  simp [hmod]

theorem nat_pow2_pos : ∀ m : Nat, 2 ^ m > 0
  | 0 => by decide
  | m + 1 => by
    rw [Nat.pow_succ]
    have := nat_pow2_pos m
    omega

theorem v2Nat_pow2_mul_odd {u : Nat} (hu : u % 2 = 1) : ∀ m : Nat, v2Nat (2 ^ m * u) = m
  | 0 => by
    simp [Nat.pow_zero, v2Nat_odd hu]
  | m + 1 => by
    have hm := v2Nat_pow2_mul_odd hu m
    have hn_pos : 2 ^ m * u > 0 := Nat.mul_pos (nat_pow2_pos m) (by omega)
    have hpow : 2 ^ (m + 1) * u = 2 * (2 ^ m * u) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [hpow]
    rw [← v2NatAux_ge (2 * (2 ^ m * u) + 1) (2 * (2 ^ m * u)) (by omega)]
    rw [v2NatAux_step (2 * (2 ^ m * u)) (2 * (2 ^ m * u)) (by omega)]
    have hmod : (2 * (2 ^ m * u)) % 2 = 0 := by omega
    have hdiv : (2 * (2 ^ m * u)) / 2 = 2 ^ m * u := by omega
    rw [if_pos hmod, hdiv, v2NatAux_ge (2 * (2 ^ m * u)) (2 ^ m * u) (by omega), hm]
    omega

/--
  Exact degree-4 Padé polynomial identity at length `L = 15`:
  `b^14 * P_0(a, b) + P_1(a, b) * preS(a, b, 15) = a^14 * (b^4 + a^2*b^2 + a^3*b)`.
-/
theorem pade4_identity (a b : Int) :
    (b ^ 14) * P0 a b + P1 a b * preS a b 15 =
      (a ^ 14) * (b ^ 4 + (a ^ 2) * (b ^ 2) + (a ^ 3) * b) := by
  have h_pos : (b ^ 14) * P0 a b + (a ^ 4) * preS a b 15 =
      (b ^ 4) * preS a b 15 + (a ^ 14) * (b ^ 4 + (a ^ 2) * (b ^ 2) + (a ^ 3) * b) := by
    dsimp [preS, P0, w, wAux]
    simp only [Int.pow_succ, Int.pow_zero, Int.add_mul, Int.mul_add,
      Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]
    ac_rfl
  have h_neg : P1 a b * preS a b 15 = -(b ^ 4 * preS a b 15) + (a ^ 4) * preS a b 15 := by
    dsimp [P1]
    rw [Int.add_mul, Int.neg_mul]
  omega

theorem pow_pos_of_pos {x : Int} (hx : x > 0) : ∀ n : Nat, x ^ n > 0
  | 0 => by rw [Int.pow_zero]; decide
  | n + 1 => by
    rw [Int.pow_succ]
    exact Int.mul_pos (pow_pos_of_pos hx n) hx

theorem odd_pow {x : Int} (hx : x % 2 = 1) : ∀ n : Nat, (x ^ n) % 2 = 1
  | 0 => by rw [Int.pow_zero]; decide
  | n + 1 => by
    rw [Int.pow_succ]
    exact odd_mul_odd (odd_pow hx n) hx

/-- Algebraic step for Theorem 7.1(1) on general parameters `a, b, u, D, r, S`. -/
theorem pade_linear_form_factor (a b u D r S : Int)
    (h_congr : (b ^ 14) * u - D * S = (a ^ 15) * r)
    (h_pade : (b ^ 14) * P0 a b + P1 a b * S =
      (a ^ 14) * (b ^ 4 + (a ^ 2) * (b ^ 2) + (a ^ 3) * b)) :
    (b ^ 14) * (D * P0 a b + u * P1 a b) =
      (a ^ 14) * (D * (b ^ 4) + a * (D * (a * (b ^ 2) + (a ^ 2) * b) + r * P1 a b)) := by
  have ha15 : (a ^ 15) * r = (a ^ 14) * a * r := by
    rw [Int.pow_succ a 14]
  have h1 : (b ^ 14) * (D * P0 a b + u * P1 a b) =
      D * ((b ^ 14) * P0 a b + P1 a b * S) + ((b ^ 14) * u - D * S) * P1 a b := by
    rw [Int.mul_add, Int.mul_add, Int.sub_mul]
    have ha : (b ^ 14) * (D * P0 a b) = D * ((b ^ 14) * P0 a b) := by ac_rfl
    have hb : (b ^ 14) * (u * P1 a b) = ((b ^ 14) * u) * P1 a b := by ac_rfl
    have hc : D * (P1 a b * S) = (D * S) * P1 a b := by ac_rfl
    omega
  rw [h1, h_pade, h_congr, ha15]
  simp only [Int.pow_succ, Int.pow_zero, Int.mul_add, Int.add_mul, Int.one_mul, Int.mul_one]
  ac_rfl

/--
  Core factorization of Theorem 7.1(1):
  For every `k ≥ 0`, `E_k` is an odd multiple of `a_k^14 = 2^(56 * 4^k)`.
-/
theorem eForm_odd_multiple_of_aTower14 {p q : Int} (hreal : RealizesWord p q w) (k : Nat) :
    ∃ Q : Int, Q % 2 = 1 ∧ eForm p q k = ((aTower k) ^ 14) * Q := by
  rcases hreal with ⟨hq_pos, hq_odd, hpar⟩
  have hreal' : RealizesWord p q w := ⟨hq_pos, hq_odd, hpar⟩
  rcases tower_congruence_all hreal' k 15 (by omega) with ⟨r, hr⟩
  have h_b14_E := pade_linear_form_factor (aTower k) (bTower k) (uTower p q k) (dTower q k) r
    (preS (aTower k) (bTower k) 15) hr (pade4_identity (aTower k) (bTower k))
  change (bTower k) ^ 14 * eForm p q k =
    (aTower k) ^ 14 *
      (dTower q k * ((bTower k) ^ 4) +
        aTower k * (dTower q k * (aTower k * ((bTower k) ^ 2) + ((aTower k) ^ 2) * bTower k) +
          r * P1 (aTower k) (bTower k))) at h_b14_E
  have hbez : IsBezout ((aTower k) ^ 14) ((bTower k) ^ 14) :=
    IsBezout.pow (isBezout_aTower_bTower k) 14 14
  have hdvd_E : (aTower k) ^ 14 ∣ eForm p q k :=
    IsBezout.dvd_of_dvd_mul_left hbez ⟨_, h_b14_E⟩
  rcases hdvd_E with ⟨Q, hQ⟩
  refine ⟨Q, ?_, hQ⟩
  have ha16 := (abTower_invariants k).1
  have ha14_pos : (aTower k) ^ 14 > 0 := pow_pos_of_pos (by omega) 14
  let T := dTower q k * (aTower k * ((bTower k) ^ 2) + ((aTower k) ^ 2) * bTower k) +
    r * P1 (aTower k) (bTower k)
  let R := dTower q k * ((bTower k) ^ 4) + aTower k * T
  have h_b14_Q : ((bTower k) ^ 14) * Q = R := by
    have h_eq : ((aTower k) ^ 14) * (((bTower k) ^ 14) * Q) = ((aTower k) ^ 14) * R := by
      calc
        ((aTower k) ^ 14) * (((bTower k) ^ 14) * Q) = ((bTower k) ^ 14) * (((aTower k) ^ 14) * Q) := by ac_rfl
        _ = ((bTower k) ^ 14) * eForm p q k := by rw [← hQ]
        _ = ((aTower k) ^ 14) * R := h_b14_E
    have h_sub : ((aTower k) ^ 14) * (((bTower k) ^ 14) * Q - R) = 0 := by
      rw [Int.mul_sub, h_eq]; omega
    have h_or : ((bTower k) ^ 14) * Q - R = 0 ∨ ((bTower k) ^ 14) * Q - R > 0 ∨
        ((bTower k) ^ 14) * Q - R < 0 := by omega
    rcases h_or with hz | hpos | hneg
    · omega
    · have : ((aTower k) ^ 14) * (((bTower k) ^ 14) * Q - R) > 0 := Int.mul_pos ha14_pos hpos
      omega
    · have : ((aTower k) ^ 14) * (-(((bTower k) ^ 14) * Q - R)) > 0 := Int.mul_pos ha14_pos (by omega)
      rw [Int.mul_neg] at this
      omega
  have ha_even : aTower k % 2 = 0 := (abTower_invariants k).2.2.2.1
  have hb_odd : bTower k % 2 = 1 := (abTower_invariants k).2.2.2.2
  have hD_odd : dTower q k % 2 = 1 := (dTower_pos_and_odd hq_pos hq_odd k).2
  have hb14_odd : ((bTower k) ^ 14) % 2 = 1 := odd_pow hb_odd 14
  have hb4_odd : ((bTower k) ^ 4) % 2 = 1 := odd_pow hb_odd 4
  have hDb4_odd : (dTower q k * ((bTower k) ^ 4)) % 2 = 1 := odd_mul_odd hD_odd hb4_odd
  have ha_half : aTower k = 2 * (aTower k / 2) := by omega
  have hR_mod : R % 2 = 1 := by
    dsimp [R]
    have h_aT : aTower k * T = 2 * ((aTower k / 2) * T) := by
      conv => lhs; arg 1; rw [ha_half]
      ac_rfl
    rw [h_aT]
    omega
  have h_prod_odd : (((bTower k) ^ 14) * Q) % 2 = 1 := by rw [h_b14_Q, hR_mod]
  by_cases hQ_even : Q % 2 = 0
  · have hQ_half : Q = 2 * (Q / 2) := by omega
    have h_prod_even : ((bTower k) ^ 14) * Q = 2 * (((bTower k) ^ 14) * (Q / 2)) := by
      conv => lhs; arg 2; rw [hQ_half]
      ac_rfl
    omega
  · omega

theorem aTower14_eq_pow2 (k : Nat) :
    (aTower k) ^ 14 = (2 : Int) ^ (56 * (4 ^ k)) := by
  rw [aTower_eq_pow2 k, int_pow_mul]
  have : 4 * (4 ^ k) * 14 = 56 * (4 ^ k) := by omega
  rw [this]

theorem int_ofNat_pow (b n : Nat) : ((b ^ n : Nat) : Int) = (b : Int) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Int.pow_succ, Int.ofNat_mul, ih]

/--
  Theorem 7.1(1): For every `k ≥ 0`:
  1. `E_k ≠ 0`;
  2. `v_2(E_k) = 56 * 4^k` (both via `v2Int` and exact power-of-2 divisibility); and
  3. `2^(56 * 4^k) ≤ |E_k|`.
-/
theorem theorem_7_1_part1 {p q : Int} (hreal : RealizesWord p q w) (k : Nat) :
    eForm p q k ≠ 0 ∧
    v2Int (eForm p q k) = 56 * (4 ^ k) ∧
    ((2 : Int) ^ (56 * (4 ^ k)) ∣ eForm p q k) ∧
    ¬ ((2 : Int) ^ (56 * (4 ^ k) + 1) ∣ eForm p q k) ∧
    (2 : Int) ^ (56 * (4 ^ k)) ≤ absInt (eForm p q k) := by
  rcases eForm_odd_multiple_of_aTower14 hreal k with ⟨Q, hQ_odd, hE_eq⟩
  rw [aTower14_eq_pow2 k] at hE_eq
  let M := 56 * (4 ^ k)
  change eForm p q k = (2 : Int) ^ M * Q at hE_eq
  have h2M_pos : (2 : Int) ^ M > 0 := pow_pos_of_pos (by decide) M
  have hQ_ne : Q ≠ 0 := by omega
  have hQ_abs_ge : absInt Q ≥ 1 := absInt_pos_of_ne_zero hQ_ne
  have habs_E : absInt (eForm p q k) = (2 : Int) ^ M * absInt Q := by
    rw [hE_eq, absInt_mul, absInt_of_nonneg (by omega)]
  have hE_ge : (2 : Int) ^ M ≤ absInt (eForm p q k) := by
    have : (2 : Int) ^ M * 1 ≤ (2 : Int) ^ M * absInt Q :=
      Int.mul_le_mul_of_nonneg_left hQ_abs_ge (by omega)
    omega
  have hE_ne : eForm p q k ≠ 0 := by
    intro h0
    rw [h0] at hE_ge
    unfold absInt at hE_ge
    omega
  have hdvd : (2 : Int) ^ M ∣ eForm p q k := ⟨Q, hE_eq⟩
  have hndvd : ¬ ((2 : Int) ^ (M + 1) ∣ eForm p q k) := by
    rintro ⟨S, hS⟩
    rw [Int.pow_succ] at hS
    have h_eq : (2 : Int) ^ M * (Q - 2 * S) = 0 := by
      have : (2 : Int) ^ M * 2 * S = (2 : Int) ^ M * (2 * S) := by ac_rfl
      rw [Int.mul_sub]
      omega
    have h_or : Q - 2 * S = 0 ∨ Q - 2 * S > 0 ∨ Q - 2 * S < 0 := by omega
    rcases h_or with hz | hpos | hneg
    · omega
    · have : (2 : Int) ^ M * (Q - 2 * S) > 0 := Int.mul_pos h2M_pos hpos
      omega
    · have : (2 : Int) ^ M * (-(Q - 2 * S)) > 0 := Int.mul_pos h2M_pos (by omega)
      rw [Int.mul_neg] at this
      omega
  have hv2 : v2Int (eForm p q k) = M := by
    unfold v2Int
    have hQ_nat_odd : Q.natAbs % 2 = 1 := by omega
    have h2M_nat : ((2 : Int) ^ M).natAbs = 2 ^ M := by
      have h_eq : (2 : Int) ^ M = ((2 ^ M : Nat) : Int) := (int_ofNat_pow 2 M).symm
      rw [h_eq]
      rfl
    rw [hE_eq, Int.natAbs_mul, h2M_nat]
    exact v2Nat_pow2_mul_odd hQ_nat_odd M
  exact ⟨hE_ne, hv2, hdvd, hndvd, hE_ge⟩

/-- Parametric quantitative inequality for `19683 * (a * b^2 + a^3) ≤ 15760 * b^3`. -/
theorem cubic_ratio_bound_aux {a b : Int} (ha : a ≥ 16) (hb : b ≥ 27) (hrat : 27 * a ≤ 16 * b) :
    19683 * (a * (b ^ 2) + a ^ 3) ≤ 15760 * (b ^ 3) ∧
    a * (b ^ 2) + a ^ 3 < b ^ 3 ∧
    b * (b ^ 3 + a * (b ^ 2) + a ^ 3) < 2 * (b ^ 4) := by
  have hb2_pos : b ^ 2 > 0 := pow_pos_of_pos (by omega) 2
  have hb3_pos : b ^ 3 > 0 := pow_pos_of_pos (by omega) 3
  have h_term1 : 19683 * (a * (b ^ 2)) ≤ 11664 * (b ^ 3) := by
    have hmul : (27 * a) * (729 * (b ^ 2)) ≤ (16 * b) * (729 * (b ^ 2)) :=
      Int.mul_le_mul_of_nonneg_right hrat (by omega)
    have h1 : (27 * a) * (729 * (b ^ 2)) = 27 * 729 * (a * (b ^ 2)) := by ac_rfl
    have h2 : (16 * b) * (729 * (b ^ 2)) = 16 * 729 * (b ^ 3) := by
      simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    omega
  have h_term2 : 19683 * (a ^ 3) ≤ 4096 * (b ^ 3) := by
    have h16b_nonneg : 0 ≤ (16 * b) * (16 * b) :=
      Int.mul_nonneg (by omega) (by omega)
    have h2 : (27 * a) * (27 * a) ≤ (16 * b) * (16 * b) :=
      Int.mul_le_mul hrat hrat (by omega) (by omega)
    have h3 : ((27 * a) * (27 * a)) * (27 * a) ≤ ((16 * b) * (16 * b)) * (16 * b) :=
      Int.mul_le_mul h2 hrat (by omega) h16b_nonneg
    have h1 : ((27 * a) * (27 * a)) * (27 * a) = 27 * 27 * 27 * (a ^ 3) := by
      simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    have h4 : ((16 * b) * (16 * b)) * (16 * b) = 16 * 16 * 16 * (b ^ 3) := by
      simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    omega
  have h_sum : 19683 * (a * (b ^ 2) + a ^ 3) ≤ 15760 * (b ^ 3) := by
    rw [Int.mul_add]
    omega
  have h_strict : a * (b ^ 2) + a ^ 3 < b ^ 3 := by omega
  have h_b4 : b * (b ^ 3 + a * (b ^ 2) + a ^ 3) < 2 * (b ^ 4) := by
    have h_assoc : b ^ 3 + a * (b ^ 2) + a ^ 3 = b ^ 3 + (a * (b ^ 2) + a ^ 3) := by omega
    have h_le : b * (b ^ 3 + (a * (b ^ 2) + a ^ 3)) < b * (b ^ 3 + b ^ 3) :=
      Int.mul_lt_mul_of_pos_left (by omega) (by omega)
    have h_rhs : b * (b ^ 3 + b ^ 3) = (b ^ 4) + (b ^ 4) := by
      rw [Int.mul_add]
      have : b * (b ^ 3) = b ^ 4 := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      omega
    rw [h_assoc]
    omega
  exact ⟨h_sum, h_strict, h_b4⟩

/--
  Quantitative inequality of Theorem 7.1(2):
  Because `27 * a_k ≤ 16 * b_k`, we have
  `19683 * (a_k * b_k^2 + a_k^3) ≤ 15760 * b_k^3 < 19683 * b_k^3`,
  hence `a_k * b_k^2 + a_k^3 < b_k^3` and `b_k * (b_k^3 + a_k * b_k^2 + a_k^3) < 2 * b_k^4`.
-/
theorem tower_cubic_ratio_bound (k : Nat) :
    19683 * (aTower k * ((bTower k) ^ 2) + (aTower k) ^ 3) ≤ 15760 * ((bTower k) ^ 3) ∧
    aTower k * ((bTower k) ^ 2) + (aTower k) ^ 3 < (bTower k) ^ 3 ∧
    bTower k * ((bTower k) ^ 3 + aTower k * ((bTower k) ^ 2) + (aTower k) ^ 3) <
      2 * ((bTower k) ^ 4) := by
  rcases abTower_invariants k with ⟨ha16, hb27, hrat, _, _⟩
  exact cubic_ratio_bound_aux ha16 hb27 hrat

/-- Parametric single-step height inequality on `(a, b, u, D, u1, D1, del)`. -/
theorem height_step_aux {a b u D u1 D1 del : Int}
    (ha16 : a ≥ 16) (hb27 : b ≥ 27) (hrat : 27 * a ≤ 16 * b)
    (hD_pos : D > 0) (hD1_pos : D1 > 0)
    (hdel_def : del = (b ^ 4 - a ^ 4) * u - D * b * (b ^ 3 + a * (b ^ 2) + a ^ 3))
    (hu1_eq : (a ^ 2) * u1 = (b ^ 3) * del)
    (hD1_def : D1 = D * (b - a) * (b ^ 4 - a ^ 4)) :
    absInt u1 + D1 ≤ (b ^ 7) * (absInt u + D) := by
  have ha_pos : a > 0 := by omega
  have hb_pos : b > 0 := by omega
  have hc_bound := (cubic_ratio_bound_aux ha16 hb27 hrat).2.2
  have ha2_lt_b2 : a ^ 2 < b ^ 2 := by
    have h1 : a * a < a * b := Int.mul_lt_mul_of_pos_left (by omega) ha_pos
    have h2 : a * b < b * b := Int.mul_lt_mul_of_pos_right (by omega) hb_pos
    have : a * a < b * b := by omega
    simpa [Int.pow_succ, Int.pow_zero] using this
  have ha2_pos : a ^ 2 > 0 := pow_pos_of_pos ha_pos 2
  have hb2_pos : b ^ 2 > 0 := pow_pos_of_pos hb_pos 2
  have hb3_pos : b ^ 3 > 0 := pow_pos_of_pos hb_pos 3
  have hb4_pos : b ^ 4 > 0 := pow_pos_of_pos hb_pos 4
  have hb7_pos : b ^ 7 > 0 := pow_pos_of_pos hb_pos 7
  have hba4_pos : b ^ 4 - a ^ 4 > 0 := by
    have h1 : (a ^ 2) * (a ^ 2) < (a ^ 2) * (b ^ 2) := Int.mul_lt_mul_of_pos_left ha2_lt_b2 ha2_pos
    have h2 : (a ^ 2) * (b ^ 2) < (b ^ 2) * (b ^ 2) := Int.mul_lt_mul_of_pos_right ha2_lt_b2 hb2_pos
    have ha4 : a ^ 4 = (a ^ 2) * (a ^ 2) := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    have hb4 : b ^ 4 = (b ^ 2) * (b ^ 2) := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    omega
  have ha4_pos : a ^ 4 > 0 := pow_pos_of_pos ha_pos 4
  -- Bound `|del| ≤ b^4 * |u| + 2 * b^4 * D`
  have h_del_bound : absInt del ≤ (b ^ 4) * absInt u + 2 * (b ^ 4) * D := by
    have h_tri := absInt_sub_le ((b ^ 4 - a ^ 4) * u) (D * b * (b ^ 3 + a * (b ^ 2) + a ^ 3))
    have h_abs1 : absInt ((b ^ 4 - a ^ 4) * u) = (b ^ 4 - a ^ 4) * absInt u := by
      rw [absInt_mul]
      have : absInt (b ^ 4 - a ^ 4) = b ^ 4 - a ^ 4 := absInt_of_nonneg (by omega)
      rw [this]
    have h_c_pos : b * (b ^ 3 + a * (b ^ 2) + a ^ 3) > 0 := by
      have ha3 := pow_pos_of_pos ha_pos 3
      have hab2 : a * (b ^ 2) > 0 := Int.mul_pos ha_pos hb2_pos
      exact Int.mul_pos hb_pos (by omega)
    have h_term2_pos : D * (b * (b ^ 3 + a * (b ^ 2) + a ^ 3)) > 0 :=
      Int.mul_pos hD_pos h_c_pos
    have h_abs2 : absInt (D * b * (b ^ 3 + a * (b ^ 2) + a ^ 3)) =
        D * (b * (b ^ 3 + a * (b ^ 2) + a ^ 3)) := by
      have h_assoc : D * b * (b ^ 3 + a * (b ^ 2) + a ^ 3) =
          D * (b * (b ^ 3 + a * (b ^ 2) + a ^ 3)) := by ac_rfl
      rw [h_assoc]
      exact absInt_of_nonneg (by omega)
    rw [← hdel_def, h_abs1, h_abs2] at h_tri
    have h_term1 : (b ^ 4 - a ^ 4) * absInt u ≤ (b ^ 4) * absInt u :=
      Int.mul_le_mul_of_nonneg_right (by omega) (absInt_nonneg u)
    have h_term2 : D * (b * (b ^ 3 + a * (b ^ 2) + a ^ 3)) ≤ 2 * (b ^ 4) * D := by
      have h_mul : D * (b * (b ^ 3 + a * (b ^ 2) + a ^ 3)) ≤ D * (2 * (b ^ 4)) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h2 : D * (2 * (b ^ 4)) = 2 * (b ^ 4) * D := by ac_rfl
      omega
    omega
  -- Multiply by `b^3` and use `a^2 ≥ 256`
  have h_u1_scaled : 256 * absInt u1 ≤ (b ^ 7) * absInt u + 2 * (b ^ 7) * D := by
    have h_abs_eq : (a ^ 2) * absInt u1 = (b ^ 3) * absInt del := by
      have h := congrArg absInt hu1_eq
      have h_a2 : absInt (a ^ 2) = a ^ 2 := absInt_of_nonneg (by omega)
      have h_b3 : absInt (b ^ 3) = b ^ 3 := absInt_of_nonneg (by omega)
      rw [absInt_mul, absInt_mul, h_a2, h_b3] at h
      exact h
    have ha2_ge : 256 ≤ a ^ 2 := by
      have : 16 * 16 ≤ a * a := Int.mul_le_mul ha16 ha16 (by omega) (by omega)
      simpa [Int.pow_succ, Int.pow_zero] using this
    have h_256_le : 256 * absInt u1 ≤ (a ^ 2) * absInt u1 :=
      Int.mul_le_mul_of_nonneg_right ha2_ge (absInt_nonneg u1)
    have h_b3_del : (b ^ 3) * absInt del ≤
        (b ^ 3) * ((b ^ 4) * absInt u + 2 * (b ^ 4) * D) :=
      Int.mul_le_mul_of_nonneg_left h_del_bound (by omega)
    have h_b7_exp : (b ^ 3) * ((b ^ 4) * absInt u + 2 * (b ^ 4) * D) =
        (b ^ 7) * absInt u + 2 * (b ^ 7) * D := by
      have hb7 : (b ^ 3) * (b ^ 4) = b ^ 7 := (int_pow_add b 3 4).symm
      rw [Int.mul_add]
      have h1 : (b ^ 3) * ((b ^ 4) * absInt u) = ((b ^ 3) * (b ^ 4)) * absInt u := by ac_rfl
      have h2 : (b ^ 3) * (2 * (b ^ 4) * D) = 2 * ((b ^ 3) * (b ^ 4)) * D := by ac_rfl
      rw [h1, h2, hb7]
    omega
  -- Bound `256 * D1 ≤ b^7 * D`
  have h_D1_scaled : 256 * D1 ≤ (b ^ 7) * D := by
    have h_D1_le_b5 : D1 ≤ D * (b ^ 5) := by
      have h1 : (b - a) * (b ^ 4 - a ^ 4) ≤ b * (b ^ 4) :=
        Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      have h2 : D * ((b - a) * (b ^ 4 - a ^ 4)) ≤ D * (b * (b ^ 4)) :=
        Int.mul_le_mul_of_nonneg_left h1 (by omega)
      have h3 : D1 = D * ((b - a) * (b ^ 4 - a ^ 4)) := by rw [hD1_def]; ac_rfl
      have h4 : b * (b ^ 4) = b ^ 5 := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      rw [h3, ← h4]
      exact h2
    have hb2_ge : 256 ≤ b ^ 2 := by
      have : 27 * 27 ≤ b * b := Int.mul_le_mul hb27 hb27 (by omega) (by omega)
      have : 729 ≤ b ^ 2 := by simpa [Int.pow_succ, Int.pow_zero] using this
      omega
    have h_256_b2 : 256 * D1 ≤ (b ^ 2) * D1 :=
      Int.mul_le_mul_of_nonneg_right hb2_ge (by omega)
    have h_b2_b7 : (b ^ 2) * D1 ≤ (b ^ 2) * (D * (b ^ 5)) :=
      Int.mul_le_mul_of_nonneg_left h_D1_le_b5 (by omega)
    have hb7 : (b ^ 2) * (D * (b ^ 5)) = (b ^ 7) * D := by
      have : (b ^ 2) * (b ^ 5) = b ^ 7 := (int_pow_add b 2 5).symm
      calc
        (b ^ 2) * (D * (b ^ 5)) = ((b ^ 2) * (b ^ 5)) * D := by ac_rfl
        _ = (b ^ 7) * D := by rw [this]
    omega
  have h_rhs_exp : (b ^ 7) * (absInt u + D) = (b ^ 7) * absInt u + (b ^ 7) * D :=
    Int.mul_add (b ^ 7) (absInt u) D
  have h_u_nonneg : 0 ≤ (b ^ 7) * absInt u := Int.mul_nonneg (by omega) (absInt_nonneg u)
  have h_D_pos : 0 < (b ^ 7) * D := Int.mul_pos hb7_pos hD_pos
  have h_2s : 2 * (b ^ 7) * D = 2 * ((b ^ 7) * D) := by ac_rfl
  rw [h_rhs_exp]
  omega

/--
  Single-step height inequality of Theorem 7.1(2):
  `H_{k+1} ≤ b_k^7 * H_k` for every `k ≥ 0`.
-/
theorem hTower_step {p q : Int} (hreal : RealizesWord p q w) (k : Nat) :
    hTower p q (k + 1) ≤ ((bTower k) ^ 7) * hTower p q k := by
  rcases hreal with ⟨hq_pos, hq_odd, hpar⟩
  have hreal' : RealizesWord p q w := ⟨hq_pos, hq_odd, hpar⟩
  rcases abTower_invariants k with ⟨ha16, hb27, hrat, _, _⟩
  exact height_step_aux ha16 hb27 hrat
    (dTower_pos_and_odd hq_pos hq_odd k).1
    (dTower_pos_and_odd hq_pos hq_odd (k + 1)).1
    rfl
    (deltaTower_exact_div hreal' k).2
    rfl

theorem pow4_ge_one : ∀ k : Nat, 4 ^ k ≥ 1
  | 0 => by decide
  | k + 1 => by
    rw [Nat.pow_succ]
    have := pow4_ge_one k
    omega

theorem bTower_pow7_eq_pow3 (k : Nat) :
    (bTower k) ^ 7 = (3 : Int) ^ (21 * (4 ^ k)) := by
  rw [bTower_eq_pow3 k, int_pow_mul]
  have : 3 * (4 ^ k) * 7 = 21 * (4 ^ k) := by omega
  rw [this]

theorem bTower_pow4_eq_pow3 (k : Nat) :
    (bTower k) ^ 4 = (3 : Int) ^ (12 * (4 ^ k)) := by
  rw [bTower_eq_pow3 k, int_pow_mul]
  have : 3 * (4 ^ k) * 4 = 12 * (4 ^ k) := by omega
  rw [this]

/--
  Closed-form height bound of Theorem 7.1(2):
  For all `k ≥ 0`, `H_k ≤ H_0 * 3^(7 * (4^k - 1)) < H_0 * 3^(7 * 4^k)`.
-/
theorem hTower_closed_bound {p q : Int} (hreal : RealizesWord p q w) :
    ∀ k : Nat,
      hTower p q k ≤ hTower p q 0 * (3 : Int) ^ (7 * (4 ^ k - 1)) ∧
      hTower p q k < hTower p q 0 * (3 : Int) ^ (7 * (4 ^ k))
  | 0 => by
    have hH0_pos : hTower p q 0 > 0 := by
      dsimp [hTower, dTower]
      have hq_pos := hreal.1
      have := absInt_nonneg (uTower p q 0)
      omega
    refine ⟨?_, ?_⟩
    · change hTower p q 0 ≤ hTower p q 0 * 1
      omega
    · change hTower p q 0 < hTower p q 0 * (3 : Int) ^ 7
      have : (3 : Int) ^ 7 = 2187 := by decide
      rw [this]
      omega
  | k + 1 => by
    rcases hTower_closed_bound hreal k with ⟨ih_le, _⟩
    have hstep := hTower_step hreal k
    have hb7_pos : (bTower k) ^ 7 > 0 :=
      pow_pos_of_pos (by have := (abTower_invariants k).2.1; omega) 7
    have h_mul : ((bTower k) ^ 7) * hTower p q k ≤
        ((bTower k) ^ 7) * (hTower p q 0 * (3 : Int) ^ (7 * (4 ^ k - 1))) :=
      Int.mul_le_mul_of_nonneg_left ih_le (by omega)
    rw [bTower_pow7_eq_pow3 k] at hstep h_mul
    have h4_ge : 4 ^ k ≥ 1 := pow4_ge_one k
    have hexp : 21 * (4 ^ k) + 7 * (4 ^ k - 1) = 7 * (4 ^ (k + 1) - 1) := by
      rw [Nat.pow_succ]
      omega
    have h_combine :
        (3 : Int) ^ (21 * (4 ^ k)) * (hTower p q 0 * (3 : Int) ^ (7 * (4 ^ k - 1))) =
          hTower p q 0 * (3 : Int) ^ (7 * (4 ^ (k + 1) - 1)) := by
      rw [← hexp, int_pow_add 3 (21 * (4 ^ k)) (7 * (4 ^ k - 1))]
      ac_rfl
    have h_le_next : hTower p q (k + 1) ≤ hTower p q 0 * (3 : Int) ^ (7 * (4 ^ (k + 1) - 1)) := by
      omega
    refine ⟨h_le_next, ?_⟩
    have hH0_pos : hTower p q 0 > 0 := by
      dsimp [hTower, dTower]
      have hq_pos := hreal.1
      have := absInt_nonneg (uTower p q 0)
      omega
    have h4_ge1 : 4 ^ (k + 1) ≥ 1 := pow4_ge_one (k + 1)
    have hexp_lt : 7 * (4 ^ (k + 1)) = 7 * (4 ^ (k + 1) - 1) + 7 := by omega
    rw [hexp_lt, int_pow_add 3 (7 * (4 ^ (k + 1) - 1)) 7]
    have h3_pow_pos : (3 : Int) ^ (7 * (4 ^ (k + 1) - 1)) > 0 :=
      pow_pos_of_pos (by decide) (7 * (4 ^ (k + 1) - 1))
    have h3_7 : (3 : Int) ^ 7 = 2187 := by decide
    rw [h3_7]
    have h_pos_prod : hTower p q 0 * (3 : Int) ^ (7 * (4 ^ (k + 1) - 1)) > 0 :=
      Int.mul_pos hH0_pos h3_pow_pos
    have h_assoc : hTower p q 0 * ((3 : Int) ^ (7 * (4 ^ (k + 1) - 1)) * 2187) =
        2187 * (hTower p q 0 * (3 : Int) ^ (7 * (4 ^ (k + 1) - 1))) := by ac_rfl
    omega

/-- Parametric linear form bound `|D * P_0(a, b) + u * P_1(a, b)| ≤ 3 * b^4 * (|u| + D)`. -/
theorem eForm_bound_aux {a b u D : Int}
    (ha16 : a ≥ 16) (hb27 : b ≥ 27) (hrat : 27 * a ≤ 16 * b) (hD_pos : D > 0) :
    absInt (D * P0 a b + u * P1 a b) ≤ 3 * (b ^ 4) * (absInt u + D) := by
  have ha_pos : a > 0 := by omega
  have hb_pos : b > 0 := by omega
  have ha_lt_b : a < b := by omega
  have ha2_lt_b2 : a ^ 2 < b ^ 2 := by
    have h1 : a * a < a * b := Int.mul_lt_mul_of_pos_left ha_lt_b ha_pos
    have h2 : a * b < b * b := Int.mul_lt_mul_of_pos_right ha_lt_b hb_pos
    have : a * a < b * b := by omega
    simpa [Int.pow_succ, Int.pow_zero] using this
  have ha2_pos : a ^ 2 > 0 := pow_pos_of_pos ha_pos 2
  have hb2_pos : b ^ 2 > 0 := pow_pos_of_pos hb_pos 2
  have hb3_pos : b ^ 3 > 0 := pow_pos_of_pos hb_pos 3
  have hb4_pos : b ^ 4 > 0 := pow_pos_of_pos hb_pos 4
  have hab3_pos : a * (b ^ 3) > 0 := Int.mul_pos ha_pos hb3_pos
  have ha2b2_pos : (a ^ 2) * (b ^ 2) > 0 := Int.mul_pos ha2_pos hb2_pos
  have hab3_lt_b4 : a * (b ^ 3) < b ^ 4 := by
    have : a * (b ^ 3) < b * (b ^ 3) := Int.mul_lt_mul_of_pos_right ha_lt_b hb3_pos
    have hb4 : b * (b ^ 3) = b ^ 4 := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    omega
  have ha2b2_lt_b4 : (a ^ 2) * (b ^ 2) < b ^ 4 := by
    have : (a ^ 2) * (b ^ 2) < (b ^ 2) * (b ^ 2) := Int.mul_lt_mul_of_pos_right ha2_lt_b2 hb2_pos
    have hb4 : (b ^ 2) * (b ^ 2) = b ^ 4 := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    omega
  have ha4_lt_b4 : a ^ 4 < b ^ 4 := by
    have h1 : (a ^ 2) * (a ^ 2) < (a ^ 2) * (b ^ 2) := Int.mul_lt_mul_of_pos_left ha2_lt_b2 ha2_pos
    have ha4 : (a ^ 2) * (a ^ 2) = a ^ 4 := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    omega
  have ha4_pos : a ^ 4 > 0 := pow_pos_of_pos ha_pos 4
  have hP0_bound : absInt (P0 a b) ≤ 3 * (b ^ 4) := by
    dsimp [P0]
    rw [absInt_of_nonneg (by omega)]
    omega
  have hP1_bound : absInt (P1 a b) ≤ 3 * (b ^ 4) := by
    dsimp [P1]
    unfold absInt
    omega
  have h_tri := absInt_add_le (D * P0 a b) (u * P1 a b)
  have h_absD : absInt D = D := absInt_of_nonneg (by omega)
  rw [absInt_mul, absInt_mul, h_absD] at h_tri
  have h_D_P0 : D * absInt (P0 a b) ≤ D * (3 * (b ^ 4)) :=
    Int.mul_le_mul_of_nonneg_left hP0_bound (by omega)
  have h_u_P1 : absInt u * absInt (P1 a b) ≤ absInt u * (3 * (b ^ 4)) :=
    Int.mul_le_mul_of_nonneg_left hP1_bound (absInt_nonneg u)
  have h_sum : D * (3 * (b ^ 4)) + absInt u * (3 * (b ^ 4)) =
      3 * (b ^ 4) * (absInt u + D) := by
    rw [Int.mul_add]
    have h1 : D * (3 * (b ^ 4)) = 3 * (b ^ 4) * D := by ac_rfl
    have h2 : absInt u * (3 * (b ^ 4)) = 3 * (b ^ 4) * absInt u := by ac_rfl
    omega
  omega

/--
  Theorem 7.1(2) (Linear form upper bound):
  For all `k ≥ 0`, `|E_k| ≤ 3 * b_k^4 * H_k < 3 * H_0 * 3^(19 * 4^k)`.
-/
theorem eForm_upper_bound {p q : Int} (hreal : RealizesWord p q w) (k : Nat) :
    absInt (eForm p q k) ≤ 3 * ((bTower k) ^ 4) * hTower p q k ∧
    absInt (eForm p q k) < 3 * hTower p q 0 * (3 : Int) ^ (19 * (4 ^ k)) := by
  rcases hreal with ⟨hq_pos, hq_odd, hpar⟩
  have hreal' : RealizesWord p q w := ⟨hq_pos, hq_odd, hpar⟩
  rcases abTower_invariants k with ⟨ha16, hb27, hrat, _, _⟩
  have hD_pos := (dTower_pos_and_odd hq_pos hq_odd k).1
  have h_le1 : absInt (eForm p q k) ≤ 3 * ((bTower k) ^ 4) * hTower p q k :=
    eForm_bound_aux ha16 hb27 hrat hD_pos
  refine ⟨h_le1, ?_⟩
  have hH_lt := (hTower_closed_bound hreal' k).2
  have hb4_pos : (bTower k) ^ 4 > 0 := pow_pos_of_pos (by omega) 4
  have h_strict : 3 * ((bTower k) ^ 4) * hTower p q k <
      3 * ((bTower k) ^ 4) * (hTower p q 0 * (3 : Int) ^ (7 * (4 ^ k))) :=
    Int.mul_lt_mul_of_pos_left hH_lt (by omega)
  rw [bTower_pow4_eq_pow3 k] at h_le1 h_strict
  have h_combine :
      3 * (3 : Int) ^ (12 * (4 ^ k)) * (hTower p q 0 * (3 : Int) ^ (7 * (4 ^ k))) =
        3 * hTower p q 0 * (3 : Int) ^ (19 * (4 ^ k)) := by
    have hexp : 12 * (4 ^ k) + 7 * (4 ^ k) = 19 * (4 ^ k) := by omega
    rw [← hexp, int_pow_add 3 (12 * (4 ^ k)) (7 * (4 ^ k))]
    ac_rfl
  omega

theorem pow_nonneg_of_nonneg {x : Int} (hx : 0 ≤ x) : ∀ n : Nat, 0 ≤ x ^ n
  | 0 => by rw [Int.pow_zero]; decide
  | n + 1 => by
    rw [Int.pow_succ]
    exact Int.mul_nonneg (pow_nonneg_of_nonneg hx n) hx

theorem pow_le_pow_of_le {x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x ^ n ≤ y ^ n
  | 0 => by simp [Int.pow_zero]
  | n + 1 => by
    rw [Int.pow_succ, Int.pow_succ]
    have hyn : 0 ≤ y ^ n := pow_nonneg_of_nonneg (by omega) n
    exact Int.mul_le_mul (pow_le_pow_of_le hx hxy n) hxy hx hyn

theorem mul_pow (x y : Int) : ∀ n : Nat, (x * y) ^ n = (x ^ n) * (y ^ n)
  | 0 => by simp [Int.pow_zero]
  | n + 1 => by
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, mul_pow x y n]
    ac_rfl

theorem pow25_mul_pow19_le_pow56 (n : Nat) :
    ((2 : Int) ^ (25 * n)) * ((3 : Int) ^ (19 * n)) ≤ (2 : Int) ^ (56 * n) := by
  rw [← int_pow_mul 2 25 n, ← int_pow_mul 3 19 n, ← int_pow_mul 2 56 n, ← mul_pow]
  have hbase : (2 : Int) ^ 25 * (3 : Int) ^ 19 ≤ (2 : Int) ^ 56 := by decide
  have hpos : (0 : Int) ≤ (2 : Int) ^ 25 * (3 : Int) ^ 19 := by decide
  exact pow_le_pow_of_le hpos hbase n

theorem nat_lt_pow2 : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := nat_lt_pow2 n
    rw [Nat.pow_succ]
    omega

theorem nat_lt_pow4 : ∀ k : Nat, k < 4 ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := nat_lt_pow4 k
    rw [Nat.pow_succ]
    omega

/--
  Theorem 7.1(3) (Asymptotic height contradiction):
  For any hypothetical rational seed `(p, q)` realizing `w`, every `k ≥ 0` satisfies
  `2^(25 * 4^k) < 3 * H_0`.
-/
theorem exponential_bound_from_seed {p q : Int} (hreal : RealizesWord p q w) (k : Nat) :
    (2 : Int) ^ (25 * (4 ^ k)) < 3 * hTower p q 0 := by
  have h_lower := (theorem_7_1_part1 hreal k).2.2.2.2
  have h_upper := (eForm_upper_bound hreal k).2
  have h_base := pow25_mul_pow19_le_pow56 (4 ^ k)
  have h_lt : ((2 : Int) ^ (25 * (4 ^ k))) * ((3 : Int) ^ (19 * (4 ^ k))) <
      (3 * hTower p q 0) * ((3 : Int) ^ (19 * (4 ^ k))) := by omega
  have h3_pos : (3 : Int) ^ (19 * (4 ^ k)) > 0 :=
    pow_pos_of_pos (by decide) (19 * (4 ^ k))
  have h_trich : (2 : Int) ^ (25 * (4 ^ k)) < 3 * hTower p q 0 ∨
      3 * hTower p q 0 ≤ (2 : Int) ^ (25 * (4 ^ k)) := by omega
  rcases h_trich with hlt | hge
  · exact hlt
  · have h_ge_mul : (3 * hTower p q 0) * ((3 : Int) ^ (19 * (4 ^ k))) ≤
        ((2 : Int) ^ (25 * (4 ^ k))) * ((3 : Int) ^ (19 * (4 ^ k))) :=
      Int.mul_le_mul_of_nonneg_right hge (by omega)
    omega

/--
  Primary Theorem (Theorem 7.1):
  There is no rational 2-adic seed `x = p / q` (`p, q ∈ ℤ`, `q > 0` odd) whose
  parity itinerary under the accelerated Collatz map equals `w` at every index.
-/
theorem no_rational_seed_realizes_w (p q : Int) : ¬ RealizesWord p q w := by
  intro hreal
  let K : Nat := (3 * hTower p q 0).toNat
  have hbound := exponential_bound_from_seed hreal K
  have h_k_lt : K < 2 ^ (25 * (4 ^ K)) := by
    have h1 : K < 4 ^ K := nat_lt_pow4 K
    have h2 : 4 ^ K ≤ 25 * (4 ^ K) := by omega
    have h3 : 25 * (4 ^ K) < 2 ^ (25 * (4 ^ K)) := nat_lt_pow2 (25 * (4 ^ K))
    omega
  have h_pow_eq : ((2 ^ (25 * (4 ^ K)) : Nat) : Int) = (2 : Int) ^ (25 * (4 ^ K)) :=
    int_ofNat_pow 2 (25 * (4 ^ K))
  have h_int_lt : (K : Int) < (2 : Int) ^ (25 * (4 ^ K)) := by
    rw [← h_pow_eq]
    exact Int.ofNat_lt.mpr h_k_lt
  have hH0_pos : 0 ≤ 3 * hTower p q 0 := by
    dsimp [hTower, dTower]
    have hq_pos := hreal.1
    have := absInt_nonneg (uTower p q 0)
    omega
  have hK_eq : (K : Int) = 3 * hTower p q 0 := Int.toNat_of_nonneg hH0_pos
  omega

/--
  No integer `n ∈ ℤ` realizes the 4-automatic parity word `w`.
-/
theorem no_int_seed_realizes_w (n : Int) : ¬ RealizesWord n 1 w :=
  no_rational_seed_realizes_w n 1

end CollatzLab
