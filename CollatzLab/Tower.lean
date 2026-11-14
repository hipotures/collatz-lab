/-
  CollatzLab.Tower:
  Formalization of Proposition 6.1 (refutation of the uncancelled polynomial
  denominator invariant `Odd D_k` for `B(z) = z^2 - z^3`), Bézout coprimality of
  `a_k = 16^(4^k)` and `b_k = 27^(4^k)`, and Theorem 6.2 (the repaired
  `a_k^2`-cancelled backward Mahler tower, exact `a_k^2 ∣ Δ_k` divisibility,
  positivity/oddness of `D_k`, and all-`(k, L)` congruence transport).
-/
import CollatzLab.Prefix

namespace CollatzLab

theorem int_pow_one (x : Int) : x ^ 1 = x := by
  rw [Int.pow_succ, Int.pow_zero, Int.one_mul]

theorem int_pow_mul (x : Int) (m : Nat) : ∀ n : Nat, (x ^ m) ^ n = x ^ (m * n)
  | 0 => by rw [Nat.mul_zero, Int.pow_zero, Int.pow_zero]
  | n + 1 => by
    rw [Nat.mul_succ, Int.pow_succ, int_pow_mul x m n, int_pow_add]

/-- Level-`k` numerator parameter `a_k`: `a_0 = 16`, `a_{k+1} = a_k^4`. -/
def aTower : Nat → Int
  | 0 => 16
  | k + 1 => (aTower k) ^ 4

/-- Level-`k` denominator base parameter `b_k`: `b_0 = 27`, `b_{k+1} = b_k^4`. -/
def bTower : Nat → Int
  | 0 => 27
  | k + 1 => (bTower k) ^ 4

/--
  Repaired (`a_k^2`-cancelled) denominator tower `D_k`:
  `D_0 = 11 * q`, `D_{k+1} = D_k * (b_k - a_k) * (b_k^4 - a_k^4)`.
-/
def dTower (q : Int) : Nat → Int
  | 0 => 11 * q
  | k + 1 => dTower q k * (bTower k - aTower k) * ((bTower k) ^ 4 - (aTower k) ^ 4)

/-- Single-step numerator combination `Δ(a, b, u, D) = (b^4 - a^4)*u - D*b*(b^3 + a*b^2 + a^3)`. -/
def deltaStep (a b u D : Int) : Int :=
  (b ^ 4 - a ^ 4) * u - D * b * (b ^ 3 + a * (b ^ 2) + a ^ 3)

/--
  Repaired backward Mahler numerator tower `u_k`:
  `u_0 = 27 * ((11 * p + 23 * q) / 4)`,
  `u_{k+1} = b_k^3 * (Δ_k / a_k^2)`.
-/
def uTower (p q : Int) : Nat → Int
  | 0 => 27 * ((11 * p + 23 * q) / 4)
  | k + 1 =>
    ((bTower k) ^ 3) *
      (deltaStep (aTower k) (bTower k) (uTower p q k) (dTower q k) / ((aTower k) ^ 2))

/-- Level-`k` intermediate numerator `Δ_k = (b_k^4 - a_k^4)*u_k - D_k*b_k*(b_k^3 + a_k*b_k^2 + a_k^3)`. -/
def deltaTower (p q : Int) (k : Nat) : Int :=
  deltaStep (aTower k) (bTower k) (uTower p q k) (dTower q k)

@[simp]
theorem deltaTower_def (p q : Int) (k : Nat) :
    deltaTower p q k =
      ((bTower k) ^ 4 - (aTower k) ^ 4) * uTower p q k -
        dTower q k * bTower k * ((bTower k) ^ 3 + aTower k * ((bTower k) ^ 2) + (aTower k) ^ 3) :=
  rfl

@[simp]
theorem uTower_succ (p q : Int) (k : Nat) :
    uTower p q (k + 1) = ((bTower k) ^ 3) * (deltaTower p q k / ((aTower k) ^ 2)) :=
  rfl

/-- Uncancelled polynomial denominator recurrence from `Rung1.lean` applied to `B(z) = z^2 - z^3`. -/
def dTowerUncancelled (q : Int) : Nat → Int
  | 0 => 11 * q
  | k + 1 =>
    dTowerUncancelled q k * ((aTower k) ^ 2) * (bTower k - aTower k) *
      ((bTower k) ^ 4 - (aTower k) ^ 4)

/--
  Proposition 6.1 (`refuted` for uncancelled `Odd D_k`):
  Without cancelling `a_k^2`, `D_1` is divisible by `256 = 2^8` (hence even),
  and for `q = 1` its exact 2-adic valuation is `v_2(D_1) = 8`.
-/
theorem uncancelled_d1_divisible_by_256 (q : Int) :
    ((256 : Int) ∣ dTowerUncancelled q 1) ∧
    dTowerUncancelled q 1 % 2 = 0 ∧
    dTowerUncancelled 1 1 % 256 = 0 ∧
    dTowerUncancelled 1 1 % 512 ≠ 0 := by
  dsimp [dTowerUncancelled, aTower, bTower]
  refine ⟨⟨11 * q * (27 - 16) * (27 ^ 4 - 16 ^ 4), ?_⟩, ?_, by decide, by decide⟩
  · have : 11 * q * (16 : Int) ^ 2 * (27 - 16) * (27 ^ 4 - 16 ^ 4) =
        256 * (11 * q * (27 - 16) * (27 ^ 4 - 16 ^ 4)) := by
      simp only [Int.pow_succ, Int.pow_zero]
      ac_rfl
    exact this
  · omega

/-- Explicit Bézout coprimality `∃ u v : Int, A * u + B * v = 1`. -/
def IsBezout (A B : Int) : Prop :=
  ∃ u v : Int, A * u + B * v = 1

theorem isBezout_16_27 : IsBezout 16 27 :=
  ⟨-5, 3, rfl⟩

theorem IsBezout.symm {A B : Int} (h : IsBezout A B) : IsBezout B A := by
  rcases h with ⟨u, v, huv⟩
  exact ⟨v, u, by omega⟩

theorem IsBezout.mul_right {A B1 B2 : Int} (h1 : IsBezout A B1) (h2 : IsBezout A B2) :
    IsBezout A (B1 * B2) := by
  rcases h1 with ⟨u1, v1, huv1⟩
  rcases h2 with ⟨u2, v2, huv2⟩
  refine ⟨u1 + B1 * v1 * u2, v1 * v2, ?_⟩
  have h_id : A * (u1 + B1 * v1 * u2) + (B1 * B2) * (v1 * v2) =
      A * u1 + (B1 * v1) * (A * u2 + B2 * v2) := by
    simp only [Int.mul_add, Int.add_mul]
    ac_rfl
  rw [h_id, huv2, Int.mul_one, huv1]

theorem IsBezout.pow_right {A B : Int} (h : IsBezout A B) : ∀ n : Nat, IsBezout A (B ^ n)
  | 0 => ⟨0, 1, by rw [Int.pow_zero]; omega⟩
  | n + 1 => by
    rw [Int.pow_succ]
    exact IsBezout.mul_right (IsBezout.pow_right h n) h

theorem IsBezout.pow_left {A B : Int} (h : IsBezout A B) (m : Nat) : IsBezout (A ^ m) B :=
  IsBezout.symm (IsBezout.pow_right (IsBezout.symm h) m)

theorem IsBezout.pow {A B : Int} (h : IsBezout A B) (m n : Nat) : IsBezout (A ^ m) (B ^ n) :=
  IsBezout.pow_right (IsBezout.pow_left h m) n

/-- Euclid's lemma via Bézout identity: if `IsBezout A B` and `A ∣ B * X`, then `A ∣ X`. -/
theorem IsBezout.dvd_of_dvd_mul_left {A B X : Int} (h : IsBezout A B) (hdvd : A ∣ B * X) :
    A ∣ X := by
  rcases h with ⟨u, v, huv⟩
  rcases hdvd with ⟨q, hq⟩
  refine ⟨u * X + v * q, ?_⟩
  have h1 : (A * u + B * v) * X = A * (u * X) + v * (B * X) := by
    simp only [Int.add_mul]
    ac_rfl
  have h2 : A * (u * X + v * q) = A * (u * X) + v * (A * q) := by
    simp only [Int.mul_add]
    ac_rfl
  rw [huv, Int.one_mul, hq] at h1
  omega

theorem isBezout_aTower_bTower : ∀ k : Nat, IsBezout (aTower k) (bTower k)
  | 0 => isBezout_16_27
  | k + 1 => by
    dsimp [aTower, bTower]
    exact IsBezout.pow (isBezout_aTower_bTower k) 4 4

theorem aTower_eq_pow16 : ∀ k : Nat, aTower k = (16 : Int) ^ (4 ^ k)
  | 0 => rfl
  | k + 1 => by
    dsimp [aTower]
    rw [aTower_eq_pow16 k, int_pow_mul, Nat.pow_succ]

theorem bTower_eq_pow27 : ∀ k : Nat, bTower k = (27 : Int) ^ (4 ^ k)
  | 0 => rfl
  | k + 1 => by
    dsimp [bTower]
    rw [bTower_eq_pow27 k, int_pow_mul, Nat.pow_succ]

theorem aTower_eq_pow2 : ∀ k : Nat, aTower k = (2 : Int) ^ (4 * (4 ^ k))
  | 0 => rfl
  | k + 1 => by
    dsimp [aTower]
    rw [aTower_eq_pow2 k, int_pow_mul, Nat.pow_succ]
    have : 4 * 4 ^ k * 4 = 4 * (4 ^ k * 4) := by ac_rfl
    rw [this]

theorem bTower_eq_pow3 : ∀ k : Nat, bTower k = (3 : Int) ^ (3 * (4 ^ k))
  | 0 => rfl
  | k + 1 => by
    dsimp [bTower]
    rw [bTower_eq_pow3 k, int_pow_mul, Nat.pow_succ]
    have : 3 * 4 ^ k * 4 = 3 * (4 ^ k * 4) := by ac_rfl
    rw [this]

theorem odd_mul_odd {x y : Int} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    (x * y) % 2 = 1 := by
  have hx_eq : x = 2 * (x / 2) + 1 := by omega
  have hy_eq : y = 2 * (y / 2) + 1 := by omega
  have hmul : (2 * (x / 2) + 1) * (2 * (y / 2) + 1) =
      2 * (2 * (x / 2) * (y / 2) + (x / 2) + (y / 2)) + 1 := by
    simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
    ac_rfl
  rw [← hx_eq, ← hy_eq] at hmul
  omega

/--
  Combined positivity, lower-bound, parity, and ratio invariant (`27 * a_k ≤ 16 * b_k`)
  for `(a_k, b_k)` across all `k ≥ 0`.
-/
theorem abTower_invariants :
    ∀ k : Nat,
      aTower k ≥ 16 ∧
      bTower k ≥ 27 ∧
      27 * aTower k ≤ 16 * bTower k ∧
      aTower k % 2 = 0 ∧
      bTower k % 2 = 1
  | 0 => by
    dsimp [aTower, bTower]
    refine ⟨by decide, by decide, by decide, by decide, by decide⟩
  | k + 1 => by
    rcases abTower_invariants k with ⟨ha16, hb27, hrat, ha_even, hb_odd⟩
    dsimp [aTower, bTower]
    let a := aTower k
    let b := bTower k
    change a ^ 4 ≥ 16 ∧ b ^ 4 ≥ 27 ∧ 27 * (a ^ 4) ≤ 16 * (b ^ 4) ∧
      (a ^ 4) % 2 = 0 ∧ (b ^ 4) % 2 = 1
    have ha_lt_b : a < b := by omega
    have ha_pos : a > 0 := by omega
    have hb_pos : b > 0 := by omega
    have ha2 : a ^ 2 ≥ 16 * 16 := by
      have : a * a ≥ 16 * 16 := Int.mul_le_mul ha16 ha16 (by omega) (by omega)
      simpa [Int.pow_succ, Int.pow_zero] using this
    have ha3_pos : a ^ 3 > 0 := by
      have : a ^ 2 * a ≥ 256 * 16 := Int.mul_le_mul ha2 ha16 (by omega) (by omega)
      have heq : a ^ 3 = a ^ 2 * a := by simp [Int.pow_succ, Int.pow_zero]
      omega
    have ha4_ge : a ^ 4 ≥ 16 := by
      have : a ^ 2 * a ^ 2 ≥ 256 * 256 := Int.mul_le_mul ha2 ha2 (by omega) (by omega)
      have heq : a ^ 4 = a ^ 2 * a ^ 2 := by
        simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      omega
    have hb2 : b ^ 2 ≥ 27 * 27 := by
      have : b * b ≥ 27 * 27 := Int.mul_le_mul hb27 hb27 (by omega) (by omega)
      simpa [Int.pow_succ, Int.pow_zero] using this
    have hb4_ge : b ^ 4 ≥ 27 := by
      have : b ^ 2 * b ^ 2 ≥ 729 * 729 := Int.mul_le_mul hb2 hb2 (by omega) (by omega)
      have heq : b ^ 4 = b ^ 2 * b ^ 2 := by
        simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      omega
    have ha2_le_b2 : a ^ 2 ≤ b ^ 2 := by
      have : a * a ≤ b * b := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      simpa [Int.pow_succ, Int.pow_zero] using this
    have ha3_le_b3 : a ^ 3 ≤ b ^ 3 := by
      have : a ^ 2 * a ≤ b ^ 2 * b := Int.mul_le_mul ha2_le_b2 (by omega) (by omega) (by omega)
      simpa [Int.pow_succ, Int.pow_zero] using this
    have hrat_next : 27 * (a ^ 4) ≤ 16 * (b ^ 4) := by
      have hmul : (27 * a) * (a ^ 3) ≤ (16 * b) * (b ^ 3) :=
        Int.mul_le_mul hrat ha3_le_b3 (by omega) (by omega)
      have h1 : (27 * a) * (a ^ 3) = 27 * (a ^ 4) := by
        simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      have h2 : (16 * b) * (b ^ 3) = 16 * (b ^ 4) := by
        simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      omega
    have ha4_even : (a ^ 4) % 2 = 0 := by
      have h_decomp : a = 2 * (a / 2) := by omega
      have h_eq : a ^ 4 = 2 * ((a / 2) * (a ^ 3)) := by
        conv => lhs; rw [Int.pow_succ a 3]
        conv => lhs; rhs; rw [h_decomp]
        ac_rfl
      omega
    have hb4_odd : (b ^ 4) % 2 = 1 := by
      have hb4_eq : b ^ 4 = b * b * b * b := by
        simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]
      rw [hb4_eq]
      exact odd_mul_odd (odd_mul_odd (odd_mul_odd hb_odd hb_odd) hb_odd) hb_odd
    exact ⟨ha4_ge, hb4_ge, hrat_next, ha4_even, hb4_odd⟩

/-- Theorem 6.2(2): For every `k ≥ 0`, `D_k` is a positive odd integer. -/
theorem dTower_pos_and_odd {q : Int} (hq_pos : q > 0) (hq_odd : q % 2 = 1) :
    ∀ k : Nat, dTower q k > 0 ∧ dTower q k % 2 = 1
  | 0 => by
    dsimp [dTower]
    omega
  | k + 1 => by
    rcases dTower_pos_and_odd hq_pos hq_odd k with ⟨hd_pos, hd_odd⟩
    rcases abTower_invariants k with ⟨ha16, hb27, hrat, ha_even, hb_odd⟩
    dsimp [dTower]
    let a := aTower k
    let b := bTower k
    have hba_pos : b - a > 0 := by omega
    have hba_odd : (b - a) % 2 = 1 := by omega
    have ha4_even : (a ^ 4) % 2 = 0 := (abTower_invariants (k + 1)).2.2.2.1
    have hb4_odd : (b ^ 4) % 2 = 1 := (abTower_invariants (k + 1)).2.2.2.2
    have hba2 : b ^ 2 > a ^ 2 := by
      have : a * a < b * b := by
        have h1 : a * a < a * b := Int.mul_lt_mul_of_pos_left (by omega) (by omega)
        have h2 : a * b < b * b := Int.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      simpa [Int.pow_succ, Int.pow_zero] using this
    have hba4_pos : b ^ 4 - a ^ 4 > 0 := by
      have ha2_ge : a ^ 2 ≥ 256 := by
        have : a * a ≥ 16 * 16 := Int.mul_le_mul ha16 ha16 (by omega) (by omega)
        simpa [Int.pow_succ, Int.pow_zero] using this
      have ha2_pos : a ^ 2 > 0 := by omega
      have hb2_pos : b ^ 2 > 0 := by omega
      have h1 : a ^ 2 * a ^ 2 < a ^ 2 * b ^ 2 := Int.mul_lt_mul_of_pos_left hba2 ha2_pos
      have h2 : a ^ 2 * b ^ 2 < b ^ 2 * b ^ 2 := Int.mul_lt_mul_of_pos_right hba2 hb2_pos
      have ha4 : a ^ 4 = a ^ 2 * a ^ 2 := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      have hb4 : b ^ 4 = b ^ 2 * b ^ 2 := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      omega
    have hba4_odd : (b ^ 4 - a ^ 4) % 2 = 1 := by omega
    have hpos1 : dTower q k * (b - a) > 0 := Int.mul_pos hd_pos hba_pos
    have hpos2 : dTower q k * (b - a) * (b ^ 4 - a ^ 4) > 0 := Int.mul_pos hpos1 hba4_pos
    have hodd1 : (dTower q k * (b - a)) % 2 = 1 := odd_mul_odd hd_odd hba_odd
    have hodd2 : (dTower q k * (b - a) * (b ^ 4 - a ^ 4)) % 2 = 1 := odd_mul_odd hodd1 hba4_odd
    exact ⟨hpos2, hodd2⟩

/--
  Step A of Theorem 6.2(3):
  If the level-`k` congruence holds at `M = 2` (`a_k^2 ∣ (b_k * u_k - D_k * preS(a_k, b_k, 2))`),
  then `a_k^2 ∣ Δ_k` and `a_k^2 * u_{k+1} = b_k^3 * Δ_k`.
-/
theorem deltaTower_dvd_of_level_k {p q : Int} {k : Nat}
    (hM2 : (aTower k) ^ 2 ∣ ((bTower k) ^ 1 * uTower p q k - dTower q k * preS (aTower k) (bTower k) 2)) :
    ((aTower k) ^ 2 ∣ deltaTower p q k) ∧
    ((aTower k) ^ 2) * uTower p q (k + 1) = ((bTower k) ^ 3) * deltaTower p q k := by
  let a := aTower k
  let b := bTower k
  let u := uTower p q k
  let D := dTower q k
  rw [preS_two (aTower k) (bTower k), int_pow_one (bTower k)] at hM2
  rcases hM2 with ⟨r, hr⟩
  change b * u - D * (b + a) = a ^ 2 * r at hr
  have h_id : deltaTower p q k =
      (b ^ 3) * (b * u - D * (b + a)) - (a ^ 2) * ((a ^ 2) * u + D * b * a) := by
    dsimp [deltaTower, deltaStep]
    change (b ^ 4 - a ^ 4) * u - D * b * (b ^ 3 + a * b ^ 2 + a ^ 3) =
      b ^ 3 * (b * u - D * (b + a)) - a ^ 2 * (a ^ 2 * u + D * b * a)
    have h1 : (b ^ 4 - a ^ 4) * u = (b ^ 4) * u - (a ^ 4) * u := Int.sub_mul (b ^ 4) (a ^ 4) u
    have h2 : D * b * (b ^ 3 + a * b ^ 2 + a ^ 3) =
        D * (b ^ 4) + D * a * (b ^ 3) + D * b * (a ^ 3) := by
      simp only [Int.pow_succ, Int.pow_zero, Int.mul_add]
      ac_rfl
    have h3 : b ^ 3 * (b * u - D * (b + a)) =
        (b ^ 4) * u - (D * (b ^ 4) + D * a * (b ^ 3)) := by
      rw [Int.mul_sub, Int.mul_add, Int.mul_add]
      have ha : b ^ 3 * (b * u) = (b ^ 4) * u := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      have hb : b ^ 3 * (D * b) = D * (b ^ 4) := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      have hc : b ^ 3 * (D * a) = D * a * (b ^ 3) := by ac_rfl
      omega
    have h4 : a ^ 2 * (a ^ 2 * u + D * b * a) = (a ^ 4) * u + D * b * (a ^ 3) := by
      rw [Int.mul_add]
      have ha : a ^ 2 * (a ^ 2 * u) = (a ^ 4) * u := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      have hb : a ^ 2 * (D * b * a) = D * b * (a ^ 3) := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
      omega
    omega
  have hdvd : a ^ 2 ∣ deltaTower p q k := by
    refine ⟨(b ^ 3) * r - ((a ^ 2) * u + D * b * a), ?_⟩
    rw [h_id, hr]
    rw [Int.mul_sub]
    have : (b ^ 3) * (a ^ 2 * r) = a ^ 2 * ((b ^ 3) * r) := by ac_rfl
    omega
  refine ⟨hdvd, ?_⟩
  rcases hdvd with ⟨q_del, hq_del⟩
  dsimp [uTower]
  change a ^ 2 * (b ^ 3 * (deltaTower p q k / a ^ 2)) = b ^ 3 * deltaTower p q k
  have ha16 := (abTower_invariants k).1
  have ha2_ge : a ^ 2 ≥ 256 := by
    have : a * a ≥ 16 * 16 := Int.mul_le_mul ha16 ha16 (by omega) (by omega)
    simpa [Int.pow_succ, Int.pow_zero] using this
  have hdiv_exact : (a ^ 2) * (deltaTower p q k / (a ^ 2)) = deltaTower p q k := by
    have hmod : deltaTower p q k % (a ^ 2) = 0 := by
      rw [hq_del, Int.mul_emod_right]
    have := Int.ediv_add_emod (deltaTower p q k) (a ^ 2)
    omega
  calc
    a ^ 2 * (b ^ 3 * (deltaTower p q k / a ^ 2))
      = b ^ 3 * ((a ^ 2) * (deltaTower p q k / a ^ 2)) := by ac_rfl
    _ = b ^ 3 * deltaTower p q k := by rw [hdiv_exact]

/-- Helper: cancellation of a positive factor `c > 0` in `c * m ∣ c * x → m ∣ x`. -/
theorem dvd_cancel_left_of_pos {c m x : Int} (hc : c > 0) (h : c * m ∣ c * x) :
    m ∣ x := by
  rcases h with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have h1 : c * x = c * (m * q) := by
    calc
      c * x = c * m * q := hq
      _ = c * (m * q) := by ac_rfl
  have hdiff : c * (x - m * q) = 0 := by
    rw [Int.mul_sub, h1]
    omega
  have h_or : x - m * q = 0 ∨ x - m * q > 0 ∨ x - m * q < 0 := by omega
  rcases h_or with hz | hpos | hneg
  · omega
  · have : c * (x - m * q) > 0 := Int.mul_pos hc hpos
    omega
  · have : c * (-(x - m * q)) > 0 := Int.mul_pos hc (by omega)
    rw [Int.mul_neg] at this
    omega

/--
  Step B/C of Theorem 6.2(3):
  If the level-`k` congruence holds for all `M ≥ 1`, then the level-`k+1`
  congruence holds for all `L ≥ 1`.
-/
theorem tower_congruence_step {p q : Int} {k : Nat}
    (ih : ∀ M : Nat, M ≥ 1 →
      (aTower k) ^ M ∣
        ((bTower k) ^ (M - 1) * uTower p q k - dTower q k * preS (aTower k) (bTower k) M)) :
    ∀ L : Nat, L ≥ 1 →
      (aTower (k + 1)) ^ L ∣
        ((bTower (k + 1)) ^ (L - 1) * uTower p q (k + 1) -
          dTower q (k + 1) * preS (aTower (k + 1)) (bTower (k + 1)) L) := by
  intro L hL
  have hdel := deltaTower_dvd_of_level_k (ih 2 (by omega))
  have hu_next := hdel.2
  -- Apply level-`k` congruence at `M = 4 * (L + 1)`
  let M := 4 * (L + 1)
  have hM_ge : M ≥ 1 := by omega
  rcases ih M hM_ge with ⟨r, hr⟩
  let a := aTower k
  let b := bTower k
  let u := uTower p q k
  let D := dTower q k
  let a1 := aTower (k + 1)
  let b1 := bTower (k + 1)
  let u1 := uTower p q (k + 1)
  let D1 := dTower q (k + 1)
  have ha1_def : a1 = a ^ 4 := rfl
  have hb1_def : b1 = b ^ 4 := rfl
  have hD1_def : D1 = D * (b - a) * (b ^ 4 - a ^ 4) := rfl
  have hmahler :
      (b ^ 4 - a ^ 4) * preS a b M =
        (b ^ 3 + a * (b ^ 2) + a ^ 3) * (b ^ M - a ^ M) +
        (a ^ 2) * (b - a) * (b ^ 4 - a ^ 4) * preS a1 b1 (L + 1) :=
    preS_mahler_4L a b (L + 1)
  have hbM : b * (b ^ (M - 1)) = b ^ M := by
    have : M = (M - 1) + 1 := by omega
    conv => rhs; rw [this, Int.pow_succ]
    ac_rfl
  have hbM_split : b ^ M = b * (b ^ 3) * (b1 ^ L) := by
    have hM_eq : M = 4 + 4 * L := by omega
    rw [hM_eq, int_pow_add b 4 (4 * L), ← pow4_mul b L]
    change b ^ 4 * (b1 ^ L) = b * (b ^ 3) * (b1 ^ L)
    have : b ^ 4 = b * (b ^ 3) := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    rw [this]
  -- Combine `hr` and `hmahler` modulo `a^M`
  let C := b ^ 3 + a * (b ^ 2) + a ^ 3
  have h_transport :
      (a ^ 2) * b * ((b1 ^ L) * u1 - D1 * preS a1 b1 (L + 1)) =
        b * (b ^ 4 - a ^ 4) * ((a ^ M) * r) - D * b * C * (a ^ M) := by
    have h_u1_term : (a ^ 2) * b * ((b1 ^ L) * u1) = (b ^ M) * deltaTower p q k := by
      calc
        (a ^ 2) * b * ((b1 ^ L) * u1)
          = b * (b1 ^ L) * ((a ^ 2) * u1) := by ac_rfl
        _ = b * (b1 ^ L) * ((b ^ 3) * deltaTower p q k) := by rw [hu_next]
        _ = (b * (b ^ 3) * (b1 ^ L)) * deltaTower p q k := by ac_rfl
        _ = (b ^ M) * deltaTower p q k := by rw [← hbM_split]
    have h_del_exp : (b ^ M) * deltaTower p q k =
        (b ^ M) * ((b ^ 4 - a ^ 4) * u) - D * b * C * (b ^ M) := by
      dsimp [deltaTower, deltaStep]
      change (b ^ M) * ((b ^ 4 - a ^ 4) * u - D * b * C) =
        (b ^ M) * ((b ^ 4 - a ^ 4) * u) - D * b * C * (b ^ M)
      rw [Int.mul_sub]
      have : (b ^ M) * (D * b * C) = D * b * C * (b ^ M) := by ac_rfl
      omega
    have h_hr_mul : (b ^ M) * ((b ^ 4 - a ^ 4) * u) =
        b * (b ^ 4 - a ^ 4) * (D * preS a b M + (a ^ M) * r) := by
      have h_u : (b ^ (M - 1)) * u = D * preS a b M + (a ^ M) * r := by
        change b ^ (M - 1) * u - D * preS a b M = a ^ M * r at hr
        omega
      calc
        (b ^ M) * ((b ^ 4 - a ^ 4) * u)
          = b * (b ^ 4 - a ^ 4) * ((b ^ (M - 1)) * u) := by
            rw [← hbM]; ac_rfl
        _ = b * (b ^ 4 - a ^ 4) * (D * preS a b M + (a ^ M) * r) := by rw [h_u]
    have h_mahler_mul : b * (b ^ 4 - a ^ 4) * (D * preS a b M) =
        D * b * C * (b ^ M) - D * b * C * (a ^ M) + (a ^ 2) * b * (D1 * preS a1 b1 (L + 1)) := by
      have hm1 : b * (b ^ 4 - a ^ 4) * (D * preS a b M) =
          D * b * ((b ^ 4 - a ^ 4) * preS a b M) := by ac_rfl
      rw [hm1, hmahler]
      change D * b * (C * (b ^ M - a ^ M) + a ^ 2 * (b - a) * (b ^ 4 - a ^ 4) * preS a1 b1 (L + 1)) =
        D * b * C * (b ^ M) - D * b * C * (a ^ M) + (a ^ 2) * b * (D1 * preS a1 b1 (L + 1))
      rw [Int.mul_add, Int.mul_sub, Int.mul_sub]
      have hc1 : D * b * (C * (b ^ M)) = D * b * C * (b ^ M) := by ac_rfl
      have hc2 : D * b * (C * (a ^ M)) = D * b * C * (a ^ M) := by ac_rfl
      have hc3 : D * b * (a ^ 2 * (b - a) * (b ^ 4 - a ^ 4) * preS a1 b1 (L + 1)) =
          (a ^ 2) * b * (D1 * preS a1 b1 (L + 1)) := by
        rw [hD1_def]; ac_rfl
      omega
    rw [Int.mul_sub, h_u1_term, h_del_exp, h_hr_mul, Int.mul_add, h_mahler_mul]
    omega
  -- Deduce `(a^2 * a1^L) ∣ a^2 * b * (b1^L * u1 - D1 * preS a1 b1 (L + 1))`
  have haM_factor : a ^ M = (a ^ 2) * (a1 ^ L) * (a ^ 2) := by
    have hM_eq : M = 4 * L + 4 := by omega
    rw [hM_eq, int_pow_add a (4 * L) 4, ← pow4_mul a L]
    change (a1 ^ L) * (a ^ 4) = (a ^ 2) * (a1 ^ L) * (a ^ 2)
    have : a ^ 4 = (a ^ 2) * (a ^ 2) := by simp only [Int.pow_succ, Int.pow_zero]; ac_rfl
    rw [this]
    ac_rfl
  have hdvd_scaled :
      (a ^ 2) * (a1 ^ L) ∣ (a ^ 2) * (b * ((b1 ^ L) * u1 - D1 * preS a1 b1 (L + 1))) := by
    refine ⟨(a ^ 2) * (b * (b ^ 4 - a ^ 4) * r - D * b * C), ?_⟩
    have h_lhs : (a ^ 2) * (b * ((b1 ^ L) * u1 - D1 * preS a1 b1 (L + 1))) =
        (a ^ 2) * b * ((b1 ^ L) * u1 - D1 * preS a1 b1 (L + 1)) := by ac_rfl
    rw [h_lhs, h_transport, haM_factor]
    rw [Int.mul_sub (a ^ 2), Int.mul_sub ((a ^ 2) * (a1 ^ L))]
    have hr1 : b * (b ^ 4 - a ^ 4) * (a ^ 2 * a1 ^ L * a ^ 2 * r) =
        a ^ 2 * a1 ^ L * (a ^ 2 * (b * (b ^ 4 - a ^ 4) * r)) := by ac_rfl
    have hr2 : D * b * C * (a ^ 2 * a1 ^ L * a ^ 2) =
        a ^ 2 * a1 ^ L * (a ^ 2 * (D * b * C)) := by ac_rfl
    rw [hr1, hr2]
  have ha16 := (abTower_invariants k).1
  have ha2_ge : a ^ 2 ≥ 256 := by
    have : a * a ≥ 16 * 16 := Int.mul_le_mul ha16 ha16 (by omega) (by omega)
    simpa [Int.pow_succ, Int.pow_zero] using this
  have ha2_pos : a ^ 2 > 0 := by omega
  have hdvd_b : a1 ^ L ∣ b * ((b1 ^ L) * u1 - D1 * preS a1 b1 (L + 1)) :=
    dvd_cancel_left_of_pos ha2_pos hdvd_scaled
  have hbez_b : IsBezout (a1 ^ L) b := by
    rw [ha1_def, pow4_mul a L]
    exact IsBezout.pow_left (isBezout_aTower_bTower k) (4 * L)
  have hdvd_L1 : a1 ^ L ∣ ((b1 ^ L) * u1 - D1 * preS a1 b1 (L + 1)) :=
    IsBezout.dvd_of_dvd_mul_left hbez_b hdvd_b
  -- Shift `L + 1` back to `L` using `preS a1 b1 (L + 1) = b1 * preS a1 b1 L + w L * a1^L`
  rcases hdvd_L1 with ⟨s, hs⟩
  have hb1L : b1 ^ L = b1 * (b1 ^ (L - 1)) := by
    have : L = (L - 1) + 1 := by omega
    conv => lhs; rw [this, Int.pow_succ]
    ac_rfl
  have hdvd_b1 : a1 ^ L ∣ b1 * ((b1 ^ (L - 1)) * u1 - D1 * preS a1 b1 L) := by
    refine ⟨s + D1 * w L, ?_⟩
    dsimp [preS] at hs
    rw [hb1L] at hs
    have h_exp : b1 * (b1 ^ (L - 1) * u1 - D1 * preS a1 b1 L) =
        (b1 * (b1 ^ (L - 1)) * u1 - D1 * (b1 * preS a1 b1 L + w L * (a1 ^ L))) +
        (a1 ^ L) * (D1 * w L) := by
      rw [Int.mul_sub, Int.mul_add]
      have h1 : b1 * (b1 ^ (L - 1) * u1) = b1 * (b1 ^ (L - 1)) * u1 := by ac_rfl
      have h2 : b1 * (D1 * preS a1 b1 L) = D1 * (b1 * preS a1 b1 L) := by ac_rfl
      have h3 : D1 * (w L * (a1 ^ L)) = (a1 ^ L) * (D1 * w L) := by ac_rfl
      omega
    rw [h_exp, hs, Int.mul_add]
  have hbez_b1 : IsBezout (a1 ^ L) b1 :=
    IsBezout.pow_left (isBezout_aTower_bTower (k + 1)) L
  exact IsBezout.dvd_of_dvd_mul_left hbez_b1 hdvd_b1

/--
  Theorem 6.2(3) (All-`(k, L)` backward Mahler tower invariant):
  If `(p, q)` realizes `w`, then for every tower level `k ≥ 0` and every prefix
  length `L ≥ 1`:
  `a_k^L ∣ (b_k^(L-1) * u_k - D_k * preS(a_k, b_k, L))`,
  and `a_k^2 ∣ Δ_k` with `a_k^2 * u_{k+1} = b_k^3 * Δ_k`.
-/
theorem tower_congruence_all {p q : Int} (hreal : RealizesWord p q w) :
    ∀ (k : Nat),
      (∀ L : Nat, L ≥ 1 →
        (aTower k) ^ L ∣
          ((bTower k) ^ (L - 1) * uTower p q k - dTower q k * preS (aTower k) (bTower k) L))
  | 0 => by
    intro L hL
    dsimp [aTower, bTower, uTower, dTower]
    refine ⟨blockQuotient p q L, ?_⟩
    exact base_tower_identity hreal L hL
  | k + 1 =>
    tower_congruence_step (tower_congruence_all hreal k)

/-- Corollary of Theorem 6.2(3): For every `k ≥ 0`, `a_k^2 ∣ Δ_k` and `a_k^2 * u_{k+1} = b_k^3 * Δ_k`. -/
theorem deltaTower_exact_div {p q : Int} (hreal : RealizesWord p q w) (k : Nat) :
    ((aTower k) ^ 2 ∣ deltaTower p q k) ∧
    ((aTower k) ^ 2) * uTower p q (k + 1) = ((bTower k) ^ 3) * deltaTower p q k :=
  deltaTower_dvd_of_level_k (tower_congruence_all hreal k 2 (by omega))

end CollatzLab
