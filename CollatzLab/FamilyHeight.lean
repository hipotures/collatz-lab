import CollatzLab.FamilyApprox

/-! Archimedean estimates and an integer-only exponent gap for every `L >= 4`. -/
namespace CollatzLab.Family

def H (L : Nat) (p q : Int) (k : Nat) := absInt (u L p q k) + D L q k

def heightExponent (L : Nat) := 2 * L - 1

def formExponent (L : Nat) := L * L + L - 1

theorem geom_bound {a b : Int} (ha : 0 < a) (hb : 0 < b) (hr : 27 * a ≤ 16 * b)
    (n : Nat) (hn : 1 ≤ n) : geom a b n < 3 * b ^ (n - 1) := by
  have hab : 0 < b - a := by omega
  have hs : b < 3 * (b - a) := by omega
  have hp := pow_pos_of_pos hb (n - 1)
  have hmul := Int.mul_lt_mul_of_pos_right hs hp
  have ht := geom_identity a b n
  have hap := pow_pos_of_pos ha n
  have he : b ^ n = b * b ^ (n - 1) := by
    rw [Int.mul_comm, ← Int.pow_succ, show n - 1 + 1 = n by omega]
  have hh : (b - a) * geom a b n < (b - a) * (3 * b ^ (n - 1)) := by
    rw [he] at ht
    family_ring
  exact Int.lt_of_mul_lt_mul_left hh (by omega)

theorem C_bounds {L : Nat} (hL : 4 ≤ L) {a b : Int}
    (ha : 0 < a) (hb : 0 < b) (hr : 27 * a ≤ 16 * b) :
    0 ≤ C L a b ∧ C L a b < 3 * b ^ (L - 1) := by
  have hg := geom_bound ha hb hr L (by omega)
  have hn := geom_nonneg (by omega : 0 ≤ a) (by omega : 0 ≤ b) (L - 2)
  have ha1 := pow_pos_of_pos ha (L - 1)
  have ha2 := pow_pos_of_pos ha (L - 2)
  have hb2 := pow_pos_of_pos hb 2
  have hmul := Int.mul_nonneg (by omega : 0 ≤ b ^ 2) hn
  have hm := Int.mul_pos hb ha2
  have hsum : geom a b L = C L a b + b * a ^ (L - 2) := by
    conv => lhs; rw [show L = (L - 2) + 1 + 1 by omega, geom, geom]
    have hap : a ^ (L - 1) = a ^ (L - 2) * a := by
      rw [← Int.pow_succ, show L - 2 + 1 = L - 1 by omega]
    dsimp [C]; rw [hap]
    simp only [Int.pow_succ, Int.pow_zero]
    family_ring
  constructor
  · dsimp [C]; omega
  · omega

theorem P_bounds {L : Nat} (hL : 4 ≤ L) {a b : Int}
    (ha : 0 < a) (hb : 0 < b) (hr : 27 * a ≤ 16 * b) :
    0 ≤ P L a b ∧ P L a b < 3 * b ^ L := by
  have hg := geom_bound ha hb hr (L - 1) (by omega)
  have hn := geom_nonneg (by omega : 0 ≤ a) (by omega : 0 ≤ b) (L - 1)
  have hb2 := pow_pos_of_pos hb 2
  have hh := Int.mul_lt_mul_of_pos_left hg hb2
  have he : b ^ 2 * b ^ (L - 1 - 1) = b ^ L := by
    rw [← int_pow_add, show 2 + (L - 1 - 1) = L by omega]
  have hh' : b ^ 2 * (3 * b ^ (L - 1 - 1)) = 3 * b ^ L := by rw [← he]; ac_rfl
  rw [hh'] at hh
  exact ⟨Int.mul_nonneg (by omega) hn, hh⟩

/-- The uniform height step, under precisely the exact quotient identity. -/
theorem height_step_aux {L : Nat} (hL : 4 ≤ L) {a b v d v1 d1 : Int}
    (ha : 16 ≤ a) (hb : 27 ≤ b) (hr : 27 * a ≤ 16 * b) (hd : 0 < d)
    (hu : a ^ (L - 2) * v1 = b ^ (L - 1) * delta L a b v d)
    (hd1 : d1 = d * (b - a) * (b ^ L - a ^ L)) :
    absInt v1 + d1 ≤ b ^ (heightExponent L) * (absInt v + d) := by
  have hab : a < b := by omega
  have hap := pow_pos_of_pos (by omega : 0 < a) L
  have hbp := pow_pos_of_pos (by omega : 0 < b) L
  have hp := pow_strict (by omega : 0 < a) hab L (by omega)
  have hsA := pow_ge_self (x := a) (by omega) (n := L - 2) (by omega)
  have hsB := pow_ge_self (x := b) (by omega) (n := L - 2) (by omega)
  have hpA := pow_pos_of_pos (by omega : 0 < a) (L - 2)
  have hpB := pow_pos_of_pos (by omega : 0 < b) (L - 1)
  have hpB1 := pow_pos_of_pos (by omega : 0 < b) (L + 1)
  have hpF := pow_pos_of_pos (by omega : 0 < b) (heightExponent L)
  rcases C_bounds hL (by omega) (by omega) hr with ⟨hc0, hc⟩
  have hdelta := absInt_sub_le ((b ^ L - a ^ L) * v) (d * b * C L a b)
  rw [absInt_mul, absInt_of_nonneg (by omega : 0 ≤ b ^ L - a ^ L),
    absInt_of_nonneg (Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) hc0)] at hdelta
  have h1 := Int.mul_le_mul_of_nonneg_right (show b ^ L - a ^ L ≤ b ^ L by omega) (absInt_nonneg v)
  have h2 := Int.mul_le_mul_of_nonneg_left (show C L a b ≤ 3 * b ^ (L - 1) by omega)
    (Int.mul_nonneg (by omega : 0 ≤ d) (by omega : 0 ≤ b))
  have hbL : b * b ^ (L - 1) = b ^ L := by
    rw [Int.mul_comm, ← Int.pow_succ, show L - 1 + 1 = L by omega]
  have h2id : d * b * (3 * b ^ (L - 1)) = 3 * d * b ^ L := by rw [← hbL]; ac_rfl
  rw [h2id] at h2
  have hdelBound : absInt (delta L a b v d) ≤ b ^ L * (absInt v + 3 * d) := by
    dsimp [delta]; family_ring
  have huAbs := congrArg absInt hu
  rw [absInt_mul, absInt_mul, absInt_of_nonneg (by omega : 0 ≤ a ^ (L - 2)),
    absInt_of_nonneg (by omega : 0 ≤ b ^ (L - 1))] at huAbs
  have hum := Int.mul_le_mul_of_nonneg_left hdelBound (by omega : 0 ≤ b ^ (L - 1))
  have h4 := Int.mul_le_mul_of_nonneg_right (show (4 : Int) ≤ a ^ (L - 2) by omega) (absInt_nonneg v1)
  have hF : b ^ (L - 1) * b ^ L = b ^ (heightExponent L) := by
    rw [← int_pow_add]; congr 1; dsimp [heightExponent]; omega
  have humid : b ^ (L - 1) * (b ^ L * (absInt v + 3 * d)) =
      b ^ (heightExponent L) * (absInt v + 3 * d) := by rw [← hF]; ac_rfl
  rw [humid] at hum
  have hvBound : 4 * absInt v1 ≤ b ^ (heightExponent L) * (absInt v + 3 * d) := by omega
  have hdBound : d1 ≤ d * b ^ (L + 1) := by
    have hprod := Int.mul_le_mul (show b - a ≤ b by omega) (show b ^ L - a ^ L ≤ b ^ L by omega)
      (by omega : 0 ≤ b ^ L - a ^ L) (by omega : 0 ≤ b)
    have hdprod := Int.mul_le_mul_of_nonneg_left hprod (by omega : 0 ≤ d)
    have he : b * b ^ L = b ^ (L + 1) := by rw [Int.pow_succ]; ac_rfl
    rw [he] at hdprod
    rw [hd1]; simpa [Int.mul_assoc] using hdprod
  have hF2 : b ^ (heightExponent L) = b ^ (L + 1) * b ^ (L - 2) := by
    rw [← int_pow_add]; congr 1; dsimp [heightExponent]; omega
  have h4D := Int.mul_le_mul_of_nonneg_left (show (4 : Int) ≤ b ^ (L - 2) by omega)
    (Int.mul_nonneg (by omega : 0 ≤ d) (by omega : 0 ≤ b ^ (L + 1)))
  have hid1 : d * b ^ (L + 1) * b ^ (L - 2) = b ^ (heightExponent L) * d := by rw [hF2]; ac_rfl
  rw [hid1] at h4D
  have hvNonneg := absInt_nonneg v
  have hpos := Int.mul_nonneg (by omega : 0 ≤ b ^ (heightExponent L)) hvNonneg
  family_ring

theorem height_step {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    H L p q (k + 1) ≤ b L k ^ (heightExponent L) * H L p q k := by
  rcases ab_bounds L hL k with ⟨ha, hb, hrat, _, _⟩
  exact height_step_aux hL ha hb hrat (denominator_props hL hr.1 hr.2.1 k).1
    (tower_exact hL hr k).2 rfl

theorem height_positive {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) : 0 < H L p q k := by
  have := (denominator_props hL hr.1 hr.2.1 k).1
  have := absInt_nonneg (u L p q k)
  dsimp [H]; omega

/-- The exponent calculation for the product of the tower bases. -/
theorem height_exponent (L e k : Nat) (hL : 1 ≤ L) :
    ((L - 1) * L ^ k) * e + e * (L ^ k - 1) = e * (L ^ (k + 1) - 1) := by
  have ht := nat_power_ge_one hL k
  have htn := nat_power_ge_one hL (k + 1)
  have h1 : (L - 1) * L ^ k + L ^ k = L ^ (k + 1) := by
    calc
      _ = (L - 1 + 1) * L ^ k := by rw [Nat.add_mul, Nat.one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hL, Nat.pow_succ]; ac_rfl
  have h2 : e * (L ^ k - 1) + e = e * L ^ k := by
    calc
      _ = e * ((L ^ k - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ht]
  have h3 : e * (L ^ (k + 1) - 1) + e = e * L ^ (k + 1) := by
    calc
      _ = e * ((L ^ (k + 1) - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel htn]
  have h4 := congrArg (fun n : Nat => e * n) h1
  dsimp only at h4
  rw [Nat.mul_add] at h4
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at *
  omega

theorem height_closed_le {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) : ∀ k,
    H L p q k ≤ H L p q 0 * (3 : Int) ^ (heightExponent L * (L ^ k - 1))
  | 0 => by simp [Nat.pow_zero, Int.pow_zero]
  | k + 1 => by
    have hs := height_step hL hr k
    have hi := Int.mul_le_mul_of_nonneg_left (height_closed_le hL hr k)
      (pow_nonneg_of_nonneg (x := b L k) (by have := (ab_bounds L hL k).2.1; omega) (heightExponent L))
    rw [b_closed, int_pow_mul] at hs hi
    have he := height_exponent L (heightExponent L) k (by omega)
    have hid : (3 : Int) ^ (((L - 1) * L ^ k) * heightExponent L) *
        (H L p q 0 * (3 : Int) ^ (heightExponent L * (L ^ k - 1))) =
        H L p q 0 * (3 : Int) ^ (heightExponent L * (L ^ (k + 1) - 1)) := by
      rw [← he, int_pow_add]; ac_rfl
    rw [hid] at hi
    omega

theorem height_closed_lt {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    H L p q k < H L p q 0 * (3 : Int) ^ (heightExponent L * L ^ k) := by
  have hi := height_closed_le hL hr k
  have he : heightExponent L * L ^ k = heightExponent L * (L ^ k - 1) + heightExponent L := by
    calc
      _ = heightExponent L * ((L ^ k - 1) + 1) := by
        rw [Nat.sub_add_cancel (nat_power_ge_one (by omega) k)]
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  have hp := pow_pos_of_pos (x := 3) (by decide) (heightExponent L * (L ^ k - 1))
  have hq := pow_ge_self (x := 3) (by decide) (n := heightExponent L) (by dsimp [heightExponent]; omega)
  have ht := Int.mul_pos (height_positive hL hr 0) hp
  have hm := Int.mul_lt_mul_of_pos_left (show (1 : Int) < 3 ^ heightExponent L by omega) ht
  rw [he, int_pow_add]
  have hid : H L p q 0 * ((3 : Int) ^ (heightExponent L * (L ^ k - 1)) * (3 : Int) ^ heightExponent L) =
      (H L p q 0 * (3 : Int) ^ (heightExponent L * (L ^ k - 1))) * (3 : Int) ^ heightExponent L := by ac_rfl
  rw [hid]; omega

theorem form_bound_aux {L : Nat} (hL : 4 ≤ L) {a b v d : Int}
    (ha : 0 < a) (hb : 0 < b) (hr : 27 * a ≤ 16 * b) (hd : 0 < d) :
    absInt (d * P L a b - v * (b ^ L - a ^ L)) ≤ 3 * b ^ L * (absInt v + d) := by
  have hab : a < b := by omega
  have hpow := pow_strict ha hab L (by omega)
  have hapos := pow_pos_of_pos ha L
  have hbpos := pow_pos_of_pos hb L
  rcases P_bounds hL ha hb hr with ⟨hp0, hp⟩
  have hh := absInt_sub_le (d * P L a b) (v * (b ^ L - a ^ L))
  rw [absInt_mul, absInt_mul, absInt_of_nonneg (by omega : 0 ≤ d), absInt_of_nonneg hp0,
    absInt_of_nonneg (by omega : 0 ≤ b ^ L - a ^ L)] at hh
  have h1 := Int.mul_le_mul_of_nonneg_left (show P L a b ≤ 3 * b ^ L by omega) (by omega : 0 ≤ d)
  have h2 := Int.mul_le_mul_of_nonneg_left (show b ^ L - a ^ L ≤ 3 * b ^ L by omega) (absInt_nonneg v)
  family_ring

/-- The claimed archimedean upper bound, uniformly in `L` and `k`. -/
theorem form_upper {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    absInt (E L p q k) < 3 * H L p q 0 * (3 : Int) ^ (formExponent L * L ^ k) := by
  rcases ab_bounds L hL k with ⟨ha, hb, hrat, _, _⟩
  have hf := form_bound_aux hL (v := u L p q k) (by omega) (by omega) hrat
    (denominator_props hL hr.1 hr.2.1 k).1
  have hh := Int.mul_lt_mul_of_pos_left (height_closed_lt hL hr k)
    (by have := pow_pos_of_pos (by omega : 0 < b L k) L; omega : 0 < 3 * b L k ^ L)
  change absInt (E L p q k) ≤ 3 * b L k ^ L * H L p q k at hf
  rw [b_closed, int_pow_mul] at hf hh
  have he : (L - 1) * L ^ k * L + heightExponent L * L ^ k = formExponent L * L ^ k := by
    have h1 : (L - 1) * L + heightExponent L = formExponent L := by
      dsimp [heightExponent, formExponent]
      have hmul := congrArg (fun n : Nat => n * L) (show L - 1 + 1 = L by omega)
      dsimp only at hmul; rw [Nat.add_mul] at hmul; omega
    rw [← h1, Nat.add_mul]; ac_rfl
  have hid : 3 * (3 : Int) ^ ((L - 1) * L ^ k * L) *
      (H L p q 0 * (3 : Int) ^ (heightExponent L * L ^ k)) =
      3 * H L p q 0 * (3 : Int) ^ (formExponent L * L ^ k) := by
    rw [← he, int_pow_add]; ac_rfl
  rw [hid] at hh
  omega

end CollatzLab.Family
