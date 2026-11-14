/-
  CollatzLab.Prefix:
  Finite homogenised prefix sums `preS(a, b, L)`, the 4-step block-offset cocycle
  (Lemma 4.2), exact integrality and base congruence for a hypothetical rational
  2-adic seed of `w` (Theorem 6.2(1)), and the homogenised 4-block Mahler identity
  for `preS(a, b, 4L)` (Theorem 4.1 / Theorem 6.2(3)).
-/
import CollatzLab.Word

namespace CollatzLab

theorem int_pow_add (x : Int) (m : Nat) : ∀ n : Nat, x ^ (m + n) = (x ^ m) * (x ^ n)
  | 0 => by rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | n + 1 => by
    rw [Nat.add_succ, Int.pow_succ, Int.pow_succ, int_pow_add x m n]
    ac_rfl

/--
  Homogenised finite prefix sum
  `preS(a, b, L) = ∑_{j=0}^{L-1} w(j) a^j b^{L-1-j}`,
  defined structurally by `preS(a, b, 0) = 0` and
  `preS(a, b, L + 1) = b * preS(a, b, L) + w(L) * a^L`.
-/
def preS (a b : Int) : Nat → Int
  | 0 => 0
  | L + 1 => b * preS a b L + w L * (a ^ L)

@[simp]
theorem preS_zero (a b : Int) : preS a b 0 = 0 := rfl

@[simp]
theorem preS_succ (a b : Int) (L : Nat) :
    preS a b (L + 1) = b * preS a b L + w L * (a ^ L) := rfl

@[simp]
theorem preS_one (a b : Int) : preS a b 1 = 1 := by
  dsimp [preS]
  rw [Int.pow_zero]
  omega

@[simp]
theorem preS_two (a b : Int) : preS a b 2 = b + a := by
  dsimp [preS]
  have h1 : w 1 = 1 := w_mul4_add1 0
  rw [h1, Int.pow_zero, Int.pow_succ, Int.pow_zero]
  omega

/-- Explicit indexed sum `∑_{j=0}^{m-1} w(j) a^j b^{L-1-j}` for `m ≤ L`. -/
def preSPartialSum (a b : Int) (L : Nat) : Nat → Int
  | 0 => 0
  | j + 1 => preSPartialSum a b L j + w j * (a ^ j) * (b ^ (L - 1 - j))

theorem preSPartialSum_mul_b (a b : Int) (L : Nat) :
    ∀ m : Nat, m ≤ L →
      b * preSPartialSum a b L m = preSPartialSum a b (L + 1) m
  | 0, _ => by dsimp [preSPartialSum]; omega
  | m + 1, hm => by
    dsimp [preSPartialSum]
    have ih := preSPartialSum_mul_b a b L m (by omega)
    have hexp : L - m = (L - 1 - m) + 1 := by omega
    rw [Int.mul_add, ih, hexp, Int.pow_succ]
    have hterm : b * (w m * a ^ m * b ^ (L - 1 - m)) =
        w m * a ^ m * (b ^ (L - 1 - m) * b) := by ac_rfl
    omega

/-- `preS(a, b, L)` equals the explicit finite sum `∑_{j=0}^{L-1} w(j) a^j b^{L-1-j}`. -/
theorem preS_eq_partialSum (a b : Int) :
    ∀ L : Nat, preS a b L = preSPartialSum a b L L
  | 0 => rfl
  | L + 1 => by
    dsimp [preS, preSPartialSum]
    rw [preS_eq_partialSum a b L, preSPartialSum_mul_b a b L L (Nat.le_refl L)]
    have hsub : L - L = 0 := by omega
    rw [hsub, Int.pow_zero, Int.mul_one]

/--
  Theorem 6.2(1) & Lemma 4.2(1) on numerators:
  If `(p, q)` realizes `w`, then for every block index `m ≥ 0`:
  1. `11 * p_{4m} + 23 * q` is divisible by `4` in `ℤ`; and
  2. `16 * p_{4(m+1)} = 27 * p_{4m} + (23 - 4 * w(m)) * q`.
-/
theorem numIter_block4 {p q : Int} (hreal : RealizesWord p q w) (m : Nat) :
    (11 * numIter q p (4 * m) + 23 * q) % 4 = 0 ∧
    16 * numIter q p (4 * (m + 1)) =
      27 * numIter q p (4 * m) + (23 - 4 * w m) * q := by
  rcases hreal with ⟨_, hq_odd, hpar⟩
  let p0 := numIter q p (4 * m)
  let p1 := numIter q p (4 * m + 1)
  let p2 := numIter q p (4 * m + 2)
  let p3 := numIter q p (4 * m + 3)
  let p4 := numIter q p (4 * m + 4)
  have hp0_par : p0 % 2 = 1 := by
    have := hpar (4 * m)
    unfold seedParity at this
    rw [w_mul4 m] at this
    exact this
  have hp1_step : 2 * p1 = 3 * p0 + q :=
    (numIter_step_eq hq_odd (hpar (4 * m))).2 (w_mul4 m)
  have hp1_par : p1 % 2 = 1 := by
    have := hpar (4 * m + 1)
    unfold seedParity at this
    rw [w_mul4_add1 m] at this
    exact this
  have hp2_step : 2 * p2 = 3 * p1 + q :=
    (numIter_step_eq hq_odd (hpar (4 * m + 1))).2 (w_mul4_add1 m)
  have hdiv4 : (11 * p0 + 23 * q) % 4 = 0 := by omega
  refine ⟨hdiv4, ?_⟩
  have h4_eq : 4 * (m + 1) = 4 * m + 4 := by omega
  rw [h4_eq]
  change 16 * p4 = 27 * p0 + (23 - 4 * w m) * q
  have hs2 := numIter_step_eq hq_odd (hpar (4 * m + 2))
  have hs3 := numIter_step_eq hq_odd (hpar (4 * m + 3))
  rw [w_mul4_add2 m] at hs2
  rw [w_mul4_add3 m] at hs3
  rcases w_binary m with hm0 | hm1
  · have hp3_step : 2 * p3 = p2 := hs2.1 hm0
    have hp4_step : 2 * p4 = 3 * p3 + q := hs3.2 (by omega)
    rw [hm0]
    omega
  · have hp3_step : 2 * p3 = 3 * p2 + q := hs2.2 hm1
    have hp4_step : 2 * p4 = p3 := hs3.1 (by omega)
    rw [hm1]
    omega

/-- Exact integer quotient `q_m = (11 * p_{4m} + 23 * q) / 4` at block `m` (Theorem 6.2(1)). -/
def blockQuotient (p q : Int) (m : Nat) : Int :=
  (11 * numIter q p (4 * m) + 23 * q) / 4

theorem four_mul_blockQuotient {p q : Int} (hreal : RealizesWord p q w) (m : Nat) :
    4 * blockQuotient p q m = 11 * numIter q p (4 * m) + 23 * q := by
  unfold blockQuotient
  have hmod := (numIter_block4 hreal m).1
  omega

/-- Exact divisibility `4 ∣ (11 * p + 23 * q)` for any rational seed `(p, q)` realizing `w`. -/
theorem four_dvd_eleven_p_add_23_q {p q : Int} (hreal : RealizesWord p q w) :
    (4 : Int) ∣ (11 * p + 23 * q) := by
  refine ⟨blockQuotient p q 0, ?_⟩
  have h0 := four_mul_blockQuotient hreal 0
  dsimp [numIter] at h0
  omega

/-- Exact 1-block recurrence `16 * q_{m+1} = 27 * q_m - (11 * q) * w(m)`. -/
theorem blockQuotient_step {p q : Int} (hreal : RealizesWord p q w) (m : Nat) :
    16 * blockQuotient p q (m + 1) = 27 * blockQuotient p q m - (11 * q) * w m := by
  have hq0 := four_mul_blockQuotient hreal m
  have hq1 := four_mul_blockQuotient hreal (m + 1)
  have hstep := (numIter_block4 hreal m).2
  have hexp : (23 - 4 * w m) * q = 23 * q - 4 * (q * w m) := by
    rw [Int.sub_mul]
    have : 4 * w m * q = 4 * (q * w m) := by ac_rfl
    omega
  have hd0 : (11 * q) * w m = 11 * (q * w m) := by ac_rfl
  omega

/--
  Lemma 4.2(2): Closed-form 4L-step affine identity for `p_{4L}`:
  `11 * (16^L * p_{4L} - 27^L * p) = (23 * (27^L - 16^L) - 44 * preS(16, 27, L)) * q`.
-/
theorem iter4L_affine_identity {p q : Int} (hreal : RealizesWord p q w) :
    ∀ L : Nat,
      11 * ((16 : Int) ^ L * numIter q p (4 * L) - (27 : Int) ^ L * p) =
        (23 * ((27 : Int) ^ L - (16 : Int) ^ L) - 44 * preS 16 27 L) * q
  | 0 => by
    dsimp [numIter, preS]
    simp [Int.pow_zero]
  | L + 1 => by
    have ih := iter4L_affine_identity hreal L
    have hstep := (numIter_block4 hreal L).2
    dsimp [preS]
    rw [Int.pow_succ 16 L, Int.pow_succ 27 L]
    let pL := numIter q p (4 * L)
    let pL1 := numIter q p (4 * (L + 1))
    let A := (16 : Int) ^ L
    let B := (27 : Int) ^ L
    let S := preS 16 27 L
    change 11 * (A * 16 * pL1 - B * 27 * p) =
      (23 * (B * 27 - A * 16) - 44 * (27 * S + w L * A)) * q
    change 11 * (A * pL - B * p) = (23 * (B - A) - 44 * S) * q at ih
    change 16 * pL1 = 27 * pL + (23 - 4 * w L) * q at hstep
    have h1 : A * 16 * pL1 = A * (16 * pL1) := by ac_rfl
    have h2 : A * (27 * pL + (23 - 4 * w L) * q) =
        27 * (A * pL) + 23 * (A * q) - 4 * (w L * A * q) := by
      have : (23 - 4 * w L) * q = 23 * q - 4 * w L * q := Int.sub_mul 23 (4 * w L) q
      rw [this, Int.mul_add, Int.mul_sub]
      have ha1 : A * (27 * pL) = 27 * (A * pL) := by ac_rfl
      have ha2 : A * (23 * q) = 23 * (A * q) := by ac_rfl
      have ha3 : A * (4 * w L * q) = 4 * (w L * A * q) := by ac_rfl
      omega
    have h3 : (23 * (B - A) - 44 * S) * q = 23 * (B * q) - 23 * (A * q) - 44 * (S * q) := by
      rw [Int.sub_mul, Int.mul_sub, Int.sub_mul]
      have hb1 : 23 * B * q = 23 * (B * q) := by ac_rfl
      have hb2 : 23 * A * q = 23 * (A * q) := by ac_rfl
      have hb3 : 44 * S * q = 44 * (S * q) := by ac_rfl
      omega
    have h4 : (23 * (B * 27 - A * 16) - 44 * (27 * S + w L * A)) * q =
        27 * (23 * (B * q)) - 16 * (23 * (A * q)) - 27 * (44 * (S * q)) - 44 * (w L * A * q) := by
      rw [Int.sub_mul, Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul]
      have hc1 : 23 * (B * 27) * q = 27 * (23 * (B * q)) := by ac_rfl
      have hc2 : 23 * (A * 16) * q = 16 * (23 * (A * q)) := by ac_rfl
      have hc3 : 44 * (27 * S) * q = 27 * (44 * (S * q)) := by ac_rfl
      have hc4 : 44 * (w L * A) * q = 44 * (w L * A * q) := by ac_rfl
      omega
    have h5 : 11 * (A * pL - B * p) = 11 * (A * pL) - 11 * (B * p) := Int.mul_sub 11 (A * pL) (B * p)
    have h6 : 11 * (A * 16 * pL1 - B * 27 * p) =
        11 * (A * (16 * pL1)) - 27 * (11 * (B * p)) := by
      rw [h1, Int.mul_sub]
      have : 11 * (B * 27 * p) = 27 * (11 * (B * p)) := by ac_rfl
      omega
    rw [hstep, h2] at h6
    omega

/--
  Theorem 6.2(1) (Base congruence identity for all `L ≥ 1`):
  With `a_0 = 16`, `b_0 = 27`, `D_0 = 11 * q`, and `u_0 = 27 * ((11 * p + 23 * q) / 4)`,
  for every `L ≥ 1`:
  `27^(L-1) * u_0 - (11 * q) * preS(16, 27, L) = 16^L * blockQuotient p q L`.
-/
theorem base_tower_identity {p q : Int} (hreal : RealizesWord p q w) :
    ∀ (L : Nat), L ≥ 1 →
      (27 : Int) ^ (L - 1) * (27 * blockQuotient p q 0) - (11 * q) * preS 16 27 L =
        (16 : Int) ^ L * blockQuotient p q L
  | 0, hL => by omega
  | 1, _ => by
    dsimp [preS]
    have hstep := blockQuotient_step hreal 0
    rw [w_zero] at hstep
    change 16 * blockQuotient p q 1 = 27 * blockQuotient p q 0 - (11 * q) * 1 at hstep
    omega
  | L + 2, _ => by
    have ih := base_tower_identity hreal (L + 1) (by omega)
    have hstep := blockQuotient_step hreal (L + 1)
    have hsub1 : L + 2 - 1 = L + 1 := by omega
    have hsub0 : L + 1 - 1 = L := by omega
    rw [hsub1]
    rw [hsub0] at ih
    dsimp [preS]
    rw [Int.pow_succ 27 L, Int.pow_succ 16 (L + 1)]
    let u0 := 27 * blockQuotient p q 0
    let S := preS 16 27 (L + 1)
    let A := (16 : Int) ^ (L + 1)
    let B := (27 : Int) ^ L
    let qL1 := blockQuotient p q (L + 1)
    let qL2 := blockQuotient p q (L + 2)
    change (B * 27) * u0 - (11 * q) * (27 * S + w (L + 1) * A) = (A * 16) * qL2
    change B * u0 - (11 * q) * S = A * qL1 at ih
    change 16 * qL2 = 27 * qL1 - (11 * q) * w (L + 1) at hstep
    have h1 : (B * 27) * u0 = 27 * (B * u0) := by ac_rfl
    have h2 : (11 * q) * (27 * S + w (L + 1) * A) =
        27 * ((11 * q) * S) + A * ((11 * q) * w (L + 1)) := by
      rw [Int.mul_add]
      have ha : (11 * q) * (27 * S) = 27 * ((11 * q) * S) := by ac_rfl
      have hb : (11 * q) * (w (L + 1) * A) = A * ((11 * q) * w (L + 1)) := by ac_rfl
      omega
    have h3 : (A * 16) * qL2 = A * (16 * qL2) := by ac_rfl
    have h4 : A * (27 * qL1 - (11 * q) * w (L + 1)) =
        27 * (A * qL1) - A * ((11 * q) * w (L + 1)) := by
      rw [Int.mul_sub]
      have : A * (27 * qL1) = 27 * (A * qL1) := by ac_rfl
      omega
    rw [h3, hstep, h4]
    omega

theorem pow4_mul (x : Int) (L : Nat) : (x ^ 4) ^ L = x ^ (4 * L) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    have h4 : 4 * (L + 1) = 4 * L + 4 := by omega
    rw [Int.pow_succ, ih, h4, int_pow_add]

/-- 4-step expansion of `preS(a, b, 4 * (L + 1))` using Lemma 3.1. -/
theorem preS_four_step (a b : Int) (L : Nat) :
    preS a b (4 * (L + 1)) =
      (b ^ 4) * preS a b (4 * L) +
      (b ^ 3 + a * (b ^ 2) + a ^ 3) * (a ^ (4 * L)) +
      (a ^ 2) * (b - a) * w L * ((a ^ 4) ^ L) := by
  have h4 : 4 * (L + 1) = 4 * L + 4 := by omega
  rw [h4]
  dsimp [preS]
  rw [w_mul4 L, w_mul4_add1 L, w_mul4_add2 L, w_mul4_add3 L]
  have hp1 : a ^ (4 * L + 1) = (a ^ (4 * L)) * a := Int.pow_succ a (4 * L)
  have hp2 : a ^ (4 * L + 2) = (a ^ (4 * L)) * (a ^ 2) := int_pow_add a (4 * L) 2
  have hp3 : a ^ (4 * L + 3) = (a ^ (4 * L)) * (a ^ 3) := int_pow_add a (4 * L) 3
  have hp4 : (a ^ 4) ^ L = a ^ (4 * L) := pow4_mul a L
  rw [hp1, hp2, hp3, hp4]
  let S := preS a b (4 * L)
  let A := a ^ (4 * L)
  change b * (b * (b * (b * S + 1 * A) + 1 * (A * a)) + w L * (A * a ^ 2)) +
      (1 - w L) * (A * a ^ 3) =
    b ^ 4 * S + (b ^ 3 + a * b ^ 2 + a ^ 3) * A + a ^ 2 * (b - a) * w L * A
  rcases w_binary L with hL0 | hL1
  · rw [hL0]
    have h_id : b * (b * (b * (b * S + 1 * A) + 1 * (A * a)) + 0 * (A * a ^ 2)) +
        (1 - 0) * (A * a ^ 3) =
      b ^ 4 * S + (b ^ 3 + a * b ^ 2 + a ^ 3) * A + a ^ 2 * (b - a) * 0 * A := by
      simp only [Int.pow_succ, Int.pow_zero, Int.add_mul, Int.mul_add,
        Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add]
      ac_rfl
    exact h_id
  · rw [hL1]
    have h_lhs :
        b * (b * (b * (b * S + 1 * A) + 1 * (A * a)) + 1 * (A * a ^ 2)) +
        (1 - 1) * (A * a ^ 3) + (a ^ 3) * A =
        b ^ 4 * S + (b ^ 3 + a * b ^ 2 + a ^ 3) * A + (a ^ 2) * b * A := by
      have : (1 - 1 : Int) = 0 := rfl
      rw [this]
      simp only [Int.pow_succ, Int.pow_zero, Int.add_mul, Int.mul_add,
        Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add]
      ac_rfl
    have h_sub : a ^ 2 * (b - a) * 1 * A = (a ^ 2) * b * A - (a ^ 3) * A := by
      rw [Int.mul_one, Int.mul_sub, Int.sub_mul]
      have : a ^ 2 * a * A = a ^ 3 * A := by
        simp only [Int.pow_succ, Int.pow_zero]
      omega
    omega

/--
  Homogenised 4-block Mahler functional equation for `preS(a, b, 4L)` (Theorem 4.1 / 6.2(3)):
  `(b^4 - a^4) * preS(a, b, 4L) = (b^3 + a*b^2 + a^3)*(b^(4L) - a^(4L)) + a^2*(b - a)*(b^4 - a^4)*preS(a^4, b^4, L)`.
-/
theorem preS_mahler_4L (a b : Int) :
    ∀ L : Nat,
      (b ^ 4 - a ^ 4) * preS a b (4 * L) =
        (b ^ 3 + a * (b ^ 2) + a ^ 3) * (b ^ (4 * L) - a ^ (4 * L)) +
        (a ^ 2) * (b - a) * (b ^ 4 - a ^ 4) * preS (a ^ 4) (b ^ 4) L
  | 0 => by
    dsimp [preS]
    simp [Int.pow_zero]
  | L + 1 => by
    have ih := preS_mahler_4L a b L
    rw [preS_four_step a b L]
    dsimp [preS]
    rw [pow4_mul a L]
    have hb4 : b ^ (4 * (L + 1)) = (b ^ (4 * L)) * (b ^ 4) := by
      have : 4 * (L + 1) = 4 * L + 4 := by omega
      rw [this, int_pow_add]
    have ha4 : a ^ (4 * (L + 1)) = (a ^ (4 * L)) * (a ^ 4) := by
      have : 4 * (L + 1) = 4 * L + 4 := by omega
      rw [this, int_pow_add]
    rw [hb4, ha4]
    let D4 := b ^ 4 - a ^ 4
    let C := b ^ 3 + a * (b ^ 2) + a ^ 3
    let M := (a ^ 2) * (b - a)
    let A4 := a ^ 4
    let B4 := b ^ 4
    let AL := a ^ (4 * L)
    let BL := b ^ (4 * L)
    let S0 := preS a b (4 * L)
    let S1 := preS (a ^ 4) (b ^ 4) L
    change D4 * (B4 * S0 + C * AL + M * w L * AL) =
      C * (BL * B4 - AL * A4) + M * D4 * (B4 * S1 + w L * AL)
    change D4 * S0 = C * (BL - AL) + M * D4 * S1 at ih
    have h_lhs : D4 * (B4 * S0 + C * AL + M * w L * AL) =
        B4 * (D4 * S0) + D4 * (C * AL) + D4 * (M * w L * AL) := by
      rw [Int.mul_add, Int.mul_add]
      have : D4 * (B4 * S0) = B4 * (D4 * S0) := by ac_rfl
      omega
    have h_ih_sub : B4 * (C * (BL - AL) + M * D4 * S1) =
        B4 * (C * BL) - B4 * (C * AL) + B4 * (M * D4 * S1) := by
      rw [Int.mul_add, Int.mul_sub, Int.mul_sub]
    have h_d4 : D4 * (C * AL) = B4 * (C * AL) - A4 * (C * AL) := by
      dsimp [D4]
      rw [Int.sub_mul]
    have h_rhs : C * (BL * B4 - AL * A4) + M * D4 * (B4 * S1 + w L * AL) =
        B4 * (C * BL) - A4 * (C * AL) + B4 * (M * D4 * S1) + D4 * (M * w L * AL) := by
      rw [Int.mul_sub, Int.mul_add]
      have hr1 : C * (BL * B4) = B4 * (C * BL) := by ac_rfl
      have hr2 : C * (AL * A4) = A4 * (C * AL) := by ac_rfl
      have hr3 : M * D4 * (B4 * S1) = B4 * (M * D4 * S1) := by ac_rfl
      have hr4 : M * D4 * (w L * AL) = D4 * (M * w L * AL) := by ac_rfl
      omega
    rw [h_lhs, ih, h_ih_sub, h_d4, h_rhs]
    omega

end CollatzLab
