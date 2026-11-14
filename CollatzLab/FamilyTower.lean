import CollatzLab.FamilyPrefix

/-! Exact cancellation and the congruence invariant at every tower level and prefix length. -/
namespace CollatzLab.Family

theorem pow_ge_one {x : Int} (hx : 1 ≤ x) : ∀ n, 1 ≤ x ^ n
  | 0 => by rw [Int.pow_zero]; decide
  | n + 1 => by
    rw [Int.pow_succ]
    have := Int.mul_le_mul (pow_ge_one hx n) hx (by decide : (0 : Int) ≤ 1)
      (by have := pow_ge_one hx n; omega : 0 ≤ x ^ n)
    simpa using this

theorem pow_ge_self {x : Int} (hx : 1 ≤ x) {n : Nat} (hn : 1 ≤ n) : x ≤ x ^ n := by
  have he : n = (n - 1) + 1 := by omega
  rw [he, Int.pow_succ]
  have := Int.mul_le_mul_of_nonneg_right (pow_ge_one hx (n - 1)) (by omega : 0 ≤ x)
  simpa using this

theorem pow_strict {x y : Int} (hx : 0 < x) (hxy : x < y) : ∀ n, 1 ≤ n → x ^ n < y ^ n
  | 0, hn => by omega
  | n + 1, _ => by
    have hle := pow_le_pow_of_le (by omega : 0 ≤ x) (by omega : x ≤ y) n
    have hp := pow_pos_of_pos hx n
    have h := Int.mul_lt_mul hxy hle hp (by omega : 0 ≤ y)
    rw [Int.pow_succ, Int.pow_succ]
    simpa [Int.mul_comm] using h

theorem even_mul {x : Int} (hx : x % 2 = 0) (y : Int) : (x * y) % 2 = 0 := by
  rw [Int.mul_emod, hx]; simp

theorem even_pow {x : Int} (hx : x % 2 = 0) {n : Nat} (hn : 1 ≤ n) : (x ^ n) % 2 = 0 := by
  have he : n = (n - 1) + 1 := by omega
  rw [he, Int.pow_succ, Int.mul_comm]
  exact even_mul hx _

theorem nat_power_ge_one {L : Nat} (hL : 1 ≤ L) : ∀ k, 1 ≤ L ^ k
  | 0 => by simp
  | k + 1 => by
    rw [Nat.pow_succ]
    have := Nat.mul_le_mul (nat_power_ge_one hL k) hL
    simpa using this

theorem bases (L : Nat) (hL : 4 ≤ L) :
    16 ≤ A L ∧ 27 ≤ B L ∧ 27 * A L ≤ 16 * B L ∧ A L % 2 = 0 ∧ B L % 2 = 1 := by
  have hA : A L = 16 * (2 : Int) ^ (L - 4) := by
    dsimp [A]
    conv => lhs; rw [show L = 4 + (L - 4) by omega, int_pow_add]
    rfl
  have hB : B L = 27 * (3 : Int) ^ (L - 4) := by
    dsimp [B]
    conv => lhs; rw [show L - 1 = 3 + (L - 4) by omega, int_pow_add]
    rfl
  have ha := pow_ge_one (x := 2) (by decide) (L - 4)
  have hb := pow_ge_one (x := 3) (by decide) (L - 4)
  have hr := Int.mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le (x := 2) (y := 3) (by decide) (by decide) (L - 4))
    (by decide : (0 : Int) ≤ 432)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hA]; omega
  · rw [hB]; omega
  · rw [hA, hB]; omega
  · exact even_pow (x := 2) (by decide) (by omega)
  · exact odd_pow (x := 3) (by decide) _

def a (L : Nat) : Nat → Int
  | 0 => A L
  | k + 1 => a L k ^ L

def b (L : Nat) : Nat → Int
  | 0 => B L
  | k + 1 => b L k ^ L

def D (L : Nat) (q : Int) : Nat → Int
  | 0 => (B L - A L) * q
  | k + 1 => D L q k * (b L k - a L k) * (b L k ^ L - a L k ^ L)

def delta (L : Nat) (a b u d : Int) := (b ^ L - a ^ L) * u - d * b * C L a b

def u (L : Nat) (p q : Int) : Nat → Int
  | 0 => B L * quotient L p q 0
  | k + 1 => b L k ^ (L - 1) * (delta L (a L k) (b L k) (u L p q k) (D L q k) / a L k ^ (L - 2))

theorem a_closed (L k : Nat) : a L k = (2 : Int) ^ (L * L ^ k) := by
  induction k with
  | zero => simp [a, A]
  | succ k hi =>
    dsimp [a]; rw [hi, int_pow_mul, Nat.pow_succ, Nat.mul_assoc]

theorem b_closed (L k : Nat) : b L k = (3 : Int) ^ ((L - 1) * L ^ k) := by
  induction k with
  | zero => simp [b, B]
  | succ k hi =>
    dsimp [b]; rw [hi, int_pow_mul, Nat.pow_succ, Nat.mul_assoc]

theorem ab_coprime (L : Nat) : ∀ k, IsBezout (a L k) (b L k)
  | 0 => IsBezout.pow (show IsBezout 2 3 from ⟨-1, 1, rfl⟩) L (L - 1)
  | k + 1 => IsBezout.pow (ab_coprime L k) L L

theorem ab_bounds (L : Nat) (hL : 4 ≤ L) : ∀ k,
    16 ≤ a L k ∧ 27 ≤ b L k ∧ 27 * a L k ≤ 16 * b L k ∧
    a L k % 2 = 0 ∧ b L k % 2 = 1
  | 0 => bases L hL
  | k + 1 => by
    rcases ab_bounds L hL k with ⟨ha, hb, hr, he, ho⟩
    have hab : a L k ≤ b L k := by omega
    have hp := pow_le_pow_of_le (by omega : 0 ≤ a L k) hab (L - 1)
    have hm := Int.mul_le_mul hr hp (pow_nonneg_of_nonneg (by omega) (L - 1)) (by omega : 0 ≤ 16 * b L k)
    refine ⟨Int.le_trans ha (pow_ge_self (by omega) (by omega)),
      Int.le_trans hb (pow_ge_self (by omega) (by omega)), ?_,
      even_pow he (by omega), odd_pow ho L⟩
    change 27 * a L k ^ L ≤ 16 * b L k ^ L
    have hpa : a L k ^ L = a L k ^ (L - 1) * a L k := by
      rw [← Int.pow_succ, show L - 1 + 1 = L by omega]
    have hpb : b L k ^ L = b L k ^ (L - 1) * b L k := by
      rw [← Int.pow_succ, show L - 1 + 1 = L by omega]
    rw [hpa, hpb]
    simpa [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hm

theorem denominator_props {L : Nat} (hL : 4 ≤ L) {q : Int} (hq : 0 < q) (ho : q % 2 = 1) :
    ∀ k, 0 < D L q k ∧ D L q k % 2 = 1
  | 0 => by
    rcases bases L hL with ⟨ha, hb, hr, he, hoB⟩
    have hba : 0 < B L - A L := by omega
    have hod : (B L - A L) % 2 = 1 := by omega
    exact ⟨Int.mul_pos hba hq, odd_mul_odd hod ho⟩
  | k + 1 => by
    rcases denominator_props hL hq ho k with ⟨hd, hod⟩
    rcases ab_bounds L hL k with ⟨ha, hb, hr, he, hoB⟩
    have hab : a L k < b L k := by omega
    have hp := pow_strict (by omega : 0 < a L k) hab L (by omega)
    have hep := even_pow he (n := L) (by omega)
    have hop := odd_pow hoB L
    have hod1 : (b L k - a L k) % 2 = 1 := by omega
    have hod2 : (b L k ^ L - a L k ^ L) % 2 = 1 := by omega
    exact ⟨Int.mul_pos (Int.mul_pos hd (by omega)) (by omega),
      odd_mul_odd (odd_mul_odd hod hod1) hod2⟩

/-- One exact cancellation, extracted from the congruence at length `L`. -/
theorem delta_exact {L : Nat} (hL : 4 ≤ L) (a b v d : Int)
    (hc : a ^ L ∣ b ^ (L - 1) * v - d * pre L a b L) :
    a ^ (L - 2) ∣ delta L a b v d ∧
    a ^ (L - 2) * (b ^ (L - 1) * (delta L a b v d / a ^ (L - 2))) =
      b ^ (L - 1) * delta L a b v d := by
  rcases hc with ⟨r, hr⟩
  have hpre : pre L a b L = C L a b + a ^ (L - 2) * (b - a) := by
    have hh := prefix_block L (by omega) a b 0
    simpa [pre, sum, word_zero, Int.pow_zero] using hh
  have he : a ^ L = a ^ (L - 2) * a ^ 2 := by
    conv => lhs; rw [show L = (L - 2) + 2 by omega, int_pow_add]
  have hb : b * b ^ (L - 1) = b ^ L := by
    conv => rhs; rw [show L = (L - 1) + 1 by omega, Int.pow_succ]
    ac_rfl
  have hh := congrArg (fun t : Int => b * t) hr
  rw [hpre, he] at hh
  have hid : delta L a b v d = a ^ (L - 2) *
      (b * a ^ 2 * r + d * b * (b - a) - a ^ 2 * v) := by
    dsimp [delta]; rw [he]
    have hbr : b * (b ^ (L - 1) * v) = b ^ L * v := by rw [← hb]; ac_rfl
    simp only [Int.mul_sub, Int.mul_add] at hh
    rw [hbr] at hh
    family_ring
  have hd : a ^ (L - 2) ∣ delta L a b v d := ⟨_, hid⟩
  refine ⟨hd, ?_⟩
  have hdiv := Int.ediv_mul_cancel hd
  calc
    a ^ (L - 2) * (b ^ (L - 1) * (delta L a b v d / a ^ (L - 2))) =
        b ^ (L - 1) * ((delta L a b v d / a ^ (L - 2)) * a ^ (L - 2)) := by ac_rfl
    _ = _ := by rw [hdiv]

/-- Transport uses length `L*(n+1)` before cancellation, preserving the full target modulus. -/
theorem congruence_step {L : Nat} (hL : 4 ≤ L) (a b v d : Int) (ha : 0 < a)
    (hbez : IsBezout a b)
    (hc : ∀ n, 1 ≤ n → a ^ n ∣ b ^ (n - 1) * v - d * pre L a b n) :
    let v1 := b ^ (L - 1) * (delta L a b v d / a ^ (L - 2))
    let d1 := d * (b - a) * (b ^ L - a ^ L)
    ∀ n, 1 ≤ n → (a ^ L) ^ n ∣
      (b ^ L) ^ (n - 1) * v1 - d1 * pre L (a ^ L) (b ^ L) n := by
  let v1 := b ^ (L - 1) * (delta L a b v d / a ^ (L - 2))
  let d1 := d * (b - a) * (b ^ L - a ^ L)
  change ∀ n, 1 ≤ n → (a ^ L) ^ n ∣ (b ^ L) ^ (n - 1) * v1 - d1 * pre L (a ^ L) (b ^ L) n
  have hv : a ^ (L - 2) * v1 = b ^ (L - 1) * delta L a b v d :=
    (delta_exact hL a b v d (hc L (by omega))).2
  intro n hn
  let M := L * (n + 1)
  rcases hc M (by dsimp [M]; have := Nat.mul_le_mul hL (show 1 ≤ n + 1 by omega); omega) with ⟨r, hr⟩
  have hm := prefix_mahler L (by omega) a b (n + 1)
  have hhr := congrArg (fun t : Int => b * (b ^ L - a ^ L) * t) hr
  have hbM : b * b ^ (M - 1) = b ^ M := by
    have hpos : 1 ≤ M := by dsimp [M]; have := Nat.mul_le_mul hL (show 1 ≤ n + 1 by omega); omega
    conv => rhs; rw [show M = (M - 1) + 1 by omega, Int.pow_succ]
    ac_rfl
  have hbM2 : b * b ^ (L - 1) * (b ^ L) ^ n = b ^ M := by
    have hbL : b * b ^ (L - 1) = b ^ L := by
      conv => rhs; rw [show L = (L - 1) + 1 by omega, Int.pow_succ]
      ac_rfl
    rw [hbL, int_pow_mul]
    dsimp [M]; rw [Nat.mul_succ, int_pow_add]; ac_rfl
  have ht : a ^ (L - 2) * b * ((b ^ L) ^ n * v1 - d1 * pre L (a ^ L) (b ^ L) (n + 1)) =
      a ^ M * (b * (b ^ L - a ^ L) * r - d * b * C L a b) := by
    have hhr' : b ^ M * (b ^ L - a ^ L) * v - d * b * ((b ^ L - a ^ L) * pre L a b M) =
        a ^ M * (b * (b ^ L - a ^ L) * r) := by
      have hx : b * (b ^ L - a ^ L) * (b ^ (M - 1) * v) = b ^ M * (b ^ L - a ^ L) * v := by
        rw [← hbM]; ac_rfl
      dsimp only at hhr
      rw [Int.mul_sub (b * (b ^ L - a ^ L))] at hhr
      rw [hx] at hhr
      family_ring
    have hhv' : a ^ (L - 2) * b * ((b ^ L) ^ n * v1) = b ^ M * delta L a b v d := by
      calc
        _ = b * (b ^ L) ^ n * (a ^ (L - 2) * v1) := by ac_rfl
        _ = b * (b ^ L) ^ n * (b ^ (L - 1) * delta L a b v d) := by rw [hv]
        _ = _ := by rw [← hbM2]; ac_rfl
    dsimp [delta] at hhv'
    change (b ^ L - a ^ L) * pre L a b M = C L a b * (b ^ M - a ^ M) +
      a ^ (L - 2) * (b - a) * (b ^ L - a ^ L) * pre L (a ^ L) (b ^ L) (n + 1) at hm
    have hm' := congrArg (fun t : Int => d * b * t) hm
    dsimp [d1]
    rw [Int.mul_sub, hhv']
    family_ring
  have haM : a ^ M = a ^ (L - 2) * (a ^ L) ^ n * a ^ 2 := by
    dsimp [M]; rw [Nat.mul_succ, int_pow_add, int_pow_mul]
    have he : a ^ L = a ^ (L - 2) * a ^ 2 := by
      conv => lhs; rw [show L = (L - 2) + 2 by omega, int_pow_add]
    rw [he]; ac_rfl
  have hd : a ^ (L - 2) * (a ^ L) ^ n ∣ a ^ (L - 2) *
      (b * ((b ^ L) ^ n * v1 - d1 * pre L (a ^ L) (b ^ L) (n + 1))) := by
    refine ⟨a ^ 2 * (b * (b ^ L - a ^ L) * r - d * b * C L a b), ?_⟩
    rw [← Int.mul_assoc, ht, haM]; ac_rfl
  have hd1 := dvd_cancel_left_of_pos (pow_pos_of_pos ha (L - 2)) hd
  have hbbez : IsBezout ((a ^ L) ^ n) b := by
    rw [int_pow_mul]; exact IsBezout.pow_left hbez _
  have hd2 := IsBezout.dvd_of_dvd_mul_left hbbez hd1
  have hd3 : (a ^ L) ^ n ∣ b ^ L * ((b ^ L) ^ (n - 1) * v1 - d1 * pre L (a ^ L) (b ^ L) n) := by
    rcases hd2 with ⟨s, hs⟩
    refine ⟨s + d1 * familyWord L n, ?_⟩
    have hbN : (b ^ L) ^ n = b ^ L * (b ^ L) ^ (n - 1) := by
      conv => lhs; rw [show n = (n - 1) + 1 by omega, Int.pow_succ]
      ac_rfl
    change (b ^ L) ^ n * v1 - d1 *
      (b ^ L * pre L (a ^ L) (b ^ L) n + familyWord L n * (a ^ L) ^ n) = _ at hs
    rw [hbN] at hs
    family_ring
  have hbez1 : IsBezout ((a ^ L) ^ n) (b ^ L) := by
    rw [int_pow_mul]; exact IsBezout.pow hbez (L * n) L
  exact IsBezout.dvd_of_dvd_mul_left hbez1 hd3

/-- Congruences for every level and every positive finite length. -/
theorem tower_congruence {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) : ∀ k n, 1 ≤ n →
    a L k ^ n ∣ b L k ^ (n - 1) * u L p q k - D L q k * pre L (a L k) (b L k) n
  | 0, n, hn => ⟨quotient L p q n, base_identity (by omega) hr n hn⟩
  | k + 1, n, hn => congruence_step hL (a L k) (b L k) (u L p q k) (D L q k)
      (by have := (ab_bounds L hL k).1; omega) (ab_coprime L k) (tower_congruence hL hr k) n hn

/-- Divisibility and the exact quotient recurrence at all levels. -/
theorem tower_exact {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    a L k ^ (L - 2) ∣ delta L (a L k) (b L k) (u L p q k) (D L q k) ∧
    a L k ^ (L - 2) * u L p q (k + 1) =
      b L k ^ (L - 1) * delta L (a L k) (b L k) (u L p q k) (D L q k) :=
  delta_exact hL _ _ _ _
    (tower_congruence hL hr k L (by omega))

end CollatzLab.Family
