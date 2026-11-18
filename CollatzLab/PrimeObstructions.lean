import CollatzLab.ShadowCancellation

/-!
# Power-residue obstructions and the post-identity abelian trap for `frontierSix`

This module kernel-verifies Theorems 1 and 2 of `research/phase13/prime-obstructions.md`
for the Phase 12/13 unequal-weight substitution `1 -> 100111, 0 -> 111110` (`frontierSix`):

1. **Exact weight formula and 2-adic / 3-adic valuations:**
   For every `k : Nat`,
   `7 * weight (word frontierSix) (6 ^ k) = 5 * 6 ^ k + 2 * (-1) ^ k`.
   Consequently `weight (word frontierSix) (6 ^ k) % 4 = 2` for all `k >= 2`
   (`v_2(r_k) = 1`), and `weight (word frontierSix) (6 ^ k) % 3 ≠ 0` for all `k >= 1`
   (`v_3(r_k) = 0`).

2. **Theorem 1 (2-primary and 3-primary power-residue obstructions):**
   For any `p >= 5` with `2^(p-1) % p = 1` and `3^(p-1) % p = 1`:
   - If `2^s ∣ (p - 1)` (`s >= 2`) and `k >= max 2 s` and `(p : Int) ∣ tailDen k`,
     then `3^((p - 1) / 2^(s - 1)) % p = 1`.
   - If `3^u ∣ (p - 1)` (`u >= 1`) and `k >= max 1 u` and `(p : Int) ∣ tailDen k`,
     then `3^((p - 1) / 3^u) % p = 1`.
   - **Exact Corollary:** If `4 ∣ (p - 1)` and `3^((p - 1) / 2) % p = p - 1`
     (which holds for every prime `p ≡ 5 (mod 12)`), then
     `¬ (p ∣ Int.gcd (shadowNum k) (shadowDen k))` for **every** `k >= 1`.

3. **Theorem 2 (Post-identity abelian trap in `Aff(Z/mZ)`):**
   On the affine-map substitution step
   `(z, o) ↦ (o^5 ∘ z, o ∘ z^2 ∘ o^3)` modulo any `m >= 1`, once `o = id`,
   every subsequent iterate `j >= 0` is trapped in the cyclic abelian subgroup `<z>`:
   `subIter (z, id) j = (z ^ uSeq j, z ^ vSeq j)` where
   `7 * uSeq j = 2 * 6^j + 5 * (-1)^j` and `7 * vSeq j = 2 * (6^j - (-1)^j)`.
   In particular, whenever `z^d = id` and `d ∣ vSeq j`, the second component returns
   to `id` at step `j`.
-/
namespace CollatzLab.PrimeObstructions
open CollatzLab Morphism RationalHeight FrontierHeight ShadowCancellation

/-! ## Part 1: Exact periodic-tail weight formula and valuations -/

theorem neg_one_pow_cases : ∀ n : Nat, (-1 : Int) ^ n = 1 ∨ (-1 : Int) ^ n = -1
  | 0 => Or.inl rfl
  | n + 1 => by
    rcases neg_one_pow_cases n with h | h
    · right; rw [Int.pow_succ, h]; decide
    · left; rw [Int.pow_succ, h]; decide

theorem weight_pow_six_formula (k : Nat) :
    7 * ((weight (word frontierSix) (6 ^ k) : Nat) : Int) =
      5 * (6 ^ k : Nat) + 2 * (-1 : Int) ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hstep := frontierSix_prefix_step (6 ^ k) 0
    simp only [weight, Nat.add_zero, Int.natCast_mul] at hstep
    have heq : 6 ^ (k + 1) = 6 * 6 ^ k := by rw [Nat.pow_succ]; omega
    rw [heq]
    have hpow : ((6 * 6 ^ k : Nat) : Int) = 6 * ((6 ^ k : Nat) : Int) := by
      simp [Int.natCast_mul]
    rw [hpow, Int.pow_succ]
    omega

theorem four_dvd_pow_six (k : Nat) (hk : 2 ≤ k) : (4 : Int) ∣ ((6 ^ k : Nat) : Int) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨9 * ((6 ^ m : Nat) : Int), ?_⟩
  rw [Nat.pow_add]
  have : 6 ^ 2 = 36 := by decide
  rw [this]
  simp only [Int.natCast_mul]
  omega

theorem weight_pow_six_mod_four (k : Nat) (hk : 2 ≤ k) :
    weight (word frontierSix) (6 ^ k) % 4 = 2 := by
  have hf := weight_pow_six_formula k
  obtain ⟨t, ht⟩ := four_dvd_pow_six k hk
  rw [ht] at hf
  rcases neg_one_pow_cases k with h | h <;> rw [h] at hf <;> omega

theorem weight_pow_six_mod_three_ne_zero (k : Nat) (hk : 1 ≤ k) :
    weight (word frontierSix) (6 ^ k) % 3 ≠ 0 := by
  have hf := weight_pow_six_formula k
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h3 : ((6 ^ (1 + m) : Nat) : Int) = 6 * ((6 ^ m : Nat) : Int) := by
    rw [Nat.pow_add]; simp [Int.natCast_mul]
  rw [h3] at hf
  rcases neg_one_pow_cases (1 + m) with h | h <;> rw [h] at hf <;> omega

/-! ## Part 2: Elementary modular arithmetic helpers -/

theorem int_pow_mod_eq_one_of_dvd {a m d n : Nat} (hm : 1 < m)
    (ha : ((a : Int) ^ d) % (m : Int) = 1) (hd : d ∣ n) :
    ((a : Int) ^ n) % (m : Int) = 1 := by
  obtain ⟨q, rfl⟩ := hd
  induction q with
  | zero =>
    simp only [Nat.mul_zero, Int.pow_zero]
    exact Int.emod_eq_of_lt (by decide) (by omega)
  | succ q ih =>
    rw [Nat.mul_succ, int_pow_add, Int.mul_emod, ih, ha]
    exact Int.emod_eq_of_lt (by decide) (by omega)

theorem int_pow_congr_mod {x y m : Int} (h : x % m = y % m) :
    ∀ n : Nat, (x ^ n) % m = (y ^ n) % m
  | 0 => rfl
  | n + 1 => by
    rw [Int.pow_succ, Int.pow_succ, Int.mul_emod, int_pow_congr_mod h n, h, ← Int.mul_emod]

theorem int_dvd_sub_iff_emod_eq {a b m : Int} :
    m ∣ (a - b) ↔ a % m = b % m := by
  constructor
  · intro ⟨q, hq⟩
    have ha : a = b + m * q := by omega
    rw [ha, Int.add_emod, Int.mul_emod_right, Int.add_zero, Int.emod_emod]
  · intro h
    refine ⟨a / m - b / m, ?_⟩
    have h1 := Int.ediv_add_emod a m
    have h2 := Int.ediv_add_emod b m
    rw [Int.mul_sub]
    omega

theorem pow_two_dvd_pow_six (s k : Nat) (hsk : s ≤ k) : 2 ^ s ∣ 6 ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsk
  refine ⟨3 ^ s * 6 ^ d, ?_⟩
  rw [Nat.pow_add]
  have h23 : 2 ^ s * 3 ^ s = 6 ^ s := by rw [← Nat.mul_pow]
  calc
    6 ^ s * 6 ^ d = (2 ^ s * 3 ^ s) * 6 ^ d := by rw [h23]
    _ = 2 ^ s * (3 ^ s * 6 ^ d) := by rw [Nat.mul_assoc]

theorem pow_three_dvd_pow_six (u k : Nat) (huk : u ≤ k) : 3 ^ u ∣ 6 ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huk
  refine ⟨2 ^ u * 6 ^ d, ?_⟩
  rw [Nat.pow_add]
  have h32 : 3 ^ u * 2 ^ u = 6 ^ u := by rw [← Nat.mul_pow]
  calc
    6 ^ u * 6 ^ d = (3 ^ u * 2 ^ u) * 6 ^ d := by rw [h32]
    _ = 3 ^ u * (2 ^ u * 6 ^ d) := by rw [Nat.mul_assoc]

theorem int_pow_one (x : Int) : x ^ 1 = x := by
  rw [Int.pow_succ, Int.pow_zero, Int.one_mul]

theorem int_one_pow : ∀ n : Nat, (1 : Int) ^ n = 1
  | 0 => rfl
  | n + 1 => by rw [Int.pow_succ, int_one_pow n]; rfl

theorem nat_gcd_sub_left {a b : Nat} (h : b ≤ a) : Nat.gcd a b = Nat.gcd (a - b) b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.dvd_sub h (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    · exact Nat.gcd_dvd_right a b
  · apply Nat.dvd_gcd
    · have hadd := Nat.dvd_add (Nat.gcd_dvd_left (a - b) b) (Nat.gcd_dvd_right (a - b) b)
      rwa [Nat.sub_add_cancel h] at hadd
    · exact Nat.gcd_dvd_right (a - b) b

/-- Pure Euclidean descent: if `x^a ≡ 1 (mod m)` and `x^b ≡ 1 (mod m)` with `gcd(a, b) = 1`,
then `x ≡ 1 (mod m)`. -/
theorem mod_eq_one_of_pow_coprime {x : Int} {m : Nat} :
    ∀ (s a b : Nat), a + b ≤ s →
      (x ^ a) % (m : Int) = 1 →
      (x ^ b) % (m : Int) = 1 →
      Nat.gcd a b = 1 →
      x % (m : Int) = 1
  | 0, a, b, hs, _, _, hcop => by
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0; subst hb0
    simp at hcop
  | s + 1, a, b, hs, ha, hb, hcop => by
    by_cases ha0 : a = 0
    · subst ha0
      simp only [Nat.gcd_zero_left] at hcop
      subst hcop
      simpa only [int_pow_one] using hb
    · by_cases hb0 : b = 0
      · subst hb0
        simp only [Nat.gcd_zero_right] at hcop
        subst hcop
        simpa only [int_pow_one] using ha
      · by_cases hab : a ≤ b
        · have hsub : x ^ b = x ^ a * x ^ (b - a) := by
            rw [← int_pow_add, Nat.add_sub_cancel' hab]
          have hba : (x ^ (b - a)) % (m : Int) = 1 := by
            rw [hsub, Int.mul_emod, ha, Int.one_mul, Int.emod_emod] at hb
            exact hb
          have hgcd : Nat.gcd a (b - a) = 1 := by
            have h1 : Nat.gcd a b = Nat.gcd a (b - a) := by
              rw [Nat.gcd_comm a b, nat_gcd_sub_left hab, Nat.gcd_comm]
            rw [← h1, hcop]
          exact mod_eq_one_of_pow_coprime s a (b - a) (by omega) ha hba hgcd
        · have hba_le : b ≤ a := by omega
          have hsub : x ^ a = x ^ b * x ^ (a - b) := by
            rw [← int_pow_add, Nat.add_sub_cancel' hba_le]
          have hab' : (x ^ (a - b)) % (m : Int) = 1 := by
            rw [hsub, Int.mul_emod, hb, Int.one_mul, Int.emod_emod] at ha
            exact ha
          have hgcd : Nat.gcd (a - b) b = 1 := by
            have h1 : Nat.gcd a b = Nat.gcd (a - b) b := nat_gcd_sub_left hba_le
            rw [← h1, hcop]
          exact mod_eq_one_of_pow_coprime s (a - b) b (by omega) hab' hb hgcd

theorem mod_eq_one_of_pow_odd_and_pow_two {x : Int} {m u : Nat} (hodd : u % 2 = 1) :
    ∀ e : Nat,
      (x ^ u) % (m : Int) = 1 →
      (x ^ (2 ^ e)) % (m : Int) = 1 →
      x % (m : Int) = 1
  | 0, _, h2 => by simpa only [Nat.pow_zero, int_pow_one] using h2
  | e + 1, hu, h2 => by
    have hgcd2 : Nat.gcd u 2 = 1 := by
      have hd := Nat.gcd_dvd_right u 2
      have hle := Nat.le_of_dvd (by decide) hd
      have hne0 : Nat.gcd u 2 ≠ 0 := by
        intro h0; rw [h0] at hd; exact absurd (Nat.eq_zero_of_zero_dvd hd) (by decide)
      have hne2 : Nat.gcd u 2 ≠ 2 := by
        intro h2eq
        have := Nat.gcd_dvd_left u 2
        rw [h2eq] at this
        omega
      omega
    have hstep1 : ((x ^ (2 ^ e)) ^ 2) % (m : Int) = 1 := by
      rw [int_pow_mul, ← Nat.pow_succ]; exact h2
    have hstep2 : ((x ^ (2 ^ e)) ^ u) % (m : Int) = 1 := by
      rw [int_pow_mul, Nat.mul_comm, ← int_pow_mul]
      have h1m : (1 : Int) % (m : Int) = 1 := by
        have h := congrArg (fun z => z % (m : Int)) hu
        dsimp only at h
        rw [Int.emod_emod] at h
        exact h.symm.trans hu
      have hcongr := int_pow_congr_mod (hu.trans h1m.symm) (2 ^ e)
      rw [int_one_pow, h1m] at hcongr
      exact hcongr
    have hred : (x ^ (2 ^ e)) % (m : Int) = 1 :=
      mod_eq_one_of_pow_coprime (u + 2) u 2 (Nat.le_refl _) hstep2 hstep1 hgcd2
    exact mod_eq_one_of_pow_odd_and_pow_two hodd e hu hred

theorem mod_eq_one_of_pow_not_three_and_pow_three {x : Int} {m u : Nat} (h3 : u % 3 ≠ 0) :
    ∀ e : Nat,
      (x ^ u) % (m : Int) = 1 →
      (x ^ (3 ^ e)) % (m : Int) = 1 →
      x % (m : Int) = 1
  | 0, _, h3e => by simpa only [Nat.pow_zero, int_pow_one] using h3e
  | e + 1, hu, h3e => by
    have hgcd3 : Nat.gcd u 3 = 1 := by
      have hd := Nat.gcd_dvd_right u 3
      have hle := Nat.le_of_dvd (by decide) hd
      have hne0 : Nat.gcd u 3 ≠ 0 := by
        intro h0; rw [h0] at hd; exact absurd (Nat.eq_zero_of_zero_dvd hd) (by decide)
      have hne2 : Nat.gcd u 3 ≠ 2 := by
        intro h2eq; rw [h2eq] at hd; omega
      have hne3 : Nat.gcd u 3 ≠ 3 := by
        intro h3eq
        have := Nat.gcd_dvd_left u 3
        rw [h3eq] at this
        omega
      omega
    have hstep1 : ((x ^ (3 ^ e)) ^ 3) % (m : Int) = 1 := by
      rw [int_pow_mul, ← Nat.pow_succ]; exact h3e
    have hstep2 : ((x ^ (3 ^ e)) ^ u) % (m : Int) = 1 := by
      rw [int_pow_mul, Nat.mul_comm, ← int_pow_mul]
      have h1m : (1 : Int) % (m : Int) = 1 := by
        have h := congrArg (fun z => z % (m : Int)) hu
        dsimp only at h
        rw [Int.emod_emod] at h
        exact h.symm.trans hu
      have hcongr := int_pow_congr_mod (hu.trans h1m.symm) (3 ^ e)
      rw [int_one_pow, h1m] at hcongr
      exact hcongr
    have hred : (x ^ (3 ^ e)) % (m : Int) = 1 :=
      mod_eq_one_of_pow_coprime (u + 3) u 3 (Nat.le_refl _) hstep2 hstep1 hgcd3
    exact mod_eq_one_of_pow_not_three_and_pow_three h3 e hu hred

/-! ## Part 3: Theorem 1 — 2-primary and 3-primary power-residue obstructions -/

/-- Theorem 1 (2-primary obstruction): if `2^s ∣ (p - 1)` (`s >= 2`) and `k >= max 2 s`,
then `(p : Int) ∣ tailDen k` forces `3 ^ ((p - 1) / 2^(s - 1)) ≡ 1 (mod p)`. -/
theorem two_primary_obstruction {p s k : Nat} (hp : 5 ≤ p) (hs : 2 ≤ s)
    (hs_dvd : 2 ^ s ∣ p - 1) (hk2 : 2 ≤ k) (hks : s ≤ k)
    (hF2 : ((2 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hF3 : ((3 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hdvd : (p : Int) ∣ tailDen k) :
    ((3 : Int) ^ ((p - 1) / 2 ^ (s - 1))) % (p : Int) = 1 := by
  have hcongr : ((3 : Int) ^ weight (word frontierSix) (6 ^ k)) % (p : Int) =
      ((2 : Int) ^ (6 ^ k)) % (p : Int) :=
    int_dvd_sub_iff_emod_eq.1 hdvd
  let e := (p - 1) / 2 ^ s
  have he_mul : 2 ^ s * e = p - 1 := Nat.mul_div_cancel' hs_dvd
  have hpow := int_pow_congr_mod hcongr e
  rw [int_pow_mul, int_pow_mul] at hpow
  have h2_dvd : p - 1 ∣ 6 ^ k * e := by
    rw [← he_mul]
    exact Nat.mul_dvd_mul_right (pow_two_dvd_pow_six s k hks) e
  have hrhs : ((2 : Int) ^ (6 ^ k * e)) % (p : Int) = 1 :=
    int_pow_mod_eq_one_of_dvd (by omega) hF2 h2_dvd
  rw [hrhs] at hpow
  have hrmod := weight_pow_six_mod_four k hk2
  let u := weight (word frontierSix) (6 ^ k) / 2
  have hu_odd : u % 2 = 1 := by dsimp [u]; omega
  have hr_eq : weight (word frontierSix) (6 ^ k) = 2 * u := by dsimp [u]; omega
  let q := (p - 1) / 2 ^ (s - 1)
  have h2s : 2 ^ s = 2 ^ (s - 1) * 2 := by
    have : s = (s - 1) + 1 := by omega
    conv => lhs; rw [this, Nat.pow_succ]
  have hq_eq : q = 2 * e := by
    have hq_mul : 2 ^ (s - 1) * q = p - 1 :=
      Nat.mul_div_cancel' (Nat.dvd_trans ⟨2, h2s⟩ hs_dvd)
    have h2e : 2 ^ (s - 1) * (2 * e) = p - 1 := by
      calc
        2 ^ (s - 1) * (2 * e) = (2 ^ (s - 1) * 2) * e := by rw [Nat.mul_assoc]
        _ = 2 ^ s * e := by rw [← h2s]
        _ = p - 1 := he_mul
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) (hq_mul.trans h2e.symm)
  have hlhs_exp : weight (word frontierSix) (6 ^ k) * e = q * u := by
    rw [hr_eq, hq_eq]
    calc
      2 * u * e = 2 * (u * e) := by rw [Nat.mul_assoc]
      _ = 2 * (e * u) := by rw [Nat.mul_comm u e]
      _ = 2 * e * u := by rw [← Nat.mul_assoc]
  rw [hlhs_exp, ← int_pow_mul] at hpow
  have hq_fermat : (((3 : Int) ^ q) ^ (2 ^ (s - 1))) % (p : Int) = 1 := by
    rw [int_pow_mul, Nat.mul_comm, Nat.mul_div_cancel' (Nat.dvd_trans ⟨2, h2s⟩ hs_dvd)]
    exact hF3
  exact mod_eq_one_of_pow_odd_and_pow_two hu_odd (s - 1) hpow hq_fermat

/-- Theorem 1 (3-primary obstruction): if `3^u ∣ (p - 1)` and `k >= max 1 u`,
then `(p : Int) ∣ tailDen k` forces `3 ^ ((p - 1) / 3^u) ≡ 1 (mod p)`. -/
theorem three_primary_obstruction {p u k : Nat} (hp : 5 ≤ p)
    (hu_dvd : 3 ^ u ∣ p - 1) (hk1 : 1 ≤ k) (hku : u ≤ k)
    (hF2 : ((2 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hF3 : ((3 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hdvd : (p : Int) ∣ tailDen k) :
    ((3 : Int) ^ ((p - 1) / 3 ^ u)) % (p : Int) = 1 := by
  have hcongr : ((3 : Int) ^ weight (word frontierSix) (6 ^ k)) % (p : Int) =
      ((2 : Int) ^ (6 ^ k)) % (p : Int) :=
    int_dvd_sub_iff_emod_eq.1 hdvd
  let e := (p - 1) / 3 ^ u
  have he_mul : 3 ^ u * e = p - 1 := Nat.mul_div_cancel' hu_dvd
  have hpow := int_pow_congr_mod hcongr e
  rw [int_pow_mul, int_pow_mul] at hpow
  have h2_dvd : p - 1 ∣ 6 ^ k * e := by
    rw [← he_mul]
    exact Nat.mul_dvd_mul_right (pow_three_dvd_pow_six u k hku) e
  have hrhs : ((2 : Int) ^ (6 ^ k * e)) % (p : Int) = 1 :=
    int_pow_mod_eq_one_of_dvd (by omega) hF2 h2_dvd
  rw [hrhs] at hpow
  rw [Nat.mul_comm, ← int_pow_mul] at hpow
  have he_fermat : (((3 : Int) ^ e) ^ (3 ^ u)) % (p : Int) = 1 := by
    rw [int_pow_mul, Nat.mul_comm, he_mul]
    exact hF3
  exact mod_eq_one_of_pow_not_three_and_pow_three (weight_pow_six_mod_three_ne_zero k hk1)
    u hpow he_fermat

theorem shadow_gcd_level_one : Int.gcd (shadowNum 1) (shadowDen 1) = 1 := by
  decide

/-- Exact Corollary of Theorem 1: if `4 ∣ (p - 1)`, `2^(p-1) ≡ 1 (mod p)`, `3^(p-1) ≡ 1 (mod p)`,
and `3^((p-1)/2) ≡ p - 1 (mod p)` (true for every prime `p ≡ 5 (mod 12)`), then `p` NEVER
divides `Int.gcd (shadowNum k) (shadowDen k)` for any `k >= 1`. -/
theorem shadow_gcd_not_dvd_of_mod_four_nonresidue {p k : Nat} (hp : 5 ≤ p) (hk : 1 ≤ k)
    (h4 : 4 ∣ p - 1)
    (hF2 : ((2 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hF3 : ((3 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hnonres : ((3 : Int) ^ ((p - 1) / 2)) % (p : Int) = (p : Int) - 1) :
    ¬ (p ∣ Int.gcd (shadowNum k) (shadowDen k)) := by
  intro hdvd
  by_cases hk1 : k = 1
  · subst hk1
    rw [shadow_gcd_level_one] at hdvd
    have hle := Nat.le_of_dvd (by decide) hdvd
    omega
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have htd_int : (p : Int) ∣ tailDen (m + 1) :=
      Int.dvd_trans (Int.ofNat_dvd.mpr hdvd) (shadow_gcd_dvd_tailDen m)
    have h1 := two_primary_obstruction (s := 2) hp (by decide) h4 hk2 hk2 hF2 hF3 htd_int
    change ((3 : Int) ^ ((p - 1) / 2)) % (p : Int) = 1 at h1
    omega

/-! ## Part 4: Theorem 2 — Post-identity abelian trap in `Aff(Z/mZ)` -/

/-- An affine map `x ↦ a * x + b (mod m)` on `Z/mZ`. -/
structure AffMap (m : Nat) where
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

namespace AffMap

def Reduced {m : Nat} (f : AffMap m) : Prop :=
  f.a < m ∧ f.b < m

def id (m : Nat) : AffMap m :=
  ⟨1 % m, 0⟩

def comp {m : Nat} (f g : AffMap m) : AffMap m :=
  ⟨(f.a * g.a) % m, (f.a * g.b + f.b) % m⟩

def pow {m : Nat} (f : AffMap m) : Nat → AffMap m
  | 0 => id m
  | n + 1 => comp (pow f n) f

theorem id_reduced {m : Nat} (hm : 0 < m) : (id m).Reduced :=
  ⟨Nat.mod_lt _ hm, hm⟩

theorem comp_reduced {m : Nat} (hm : 0 < m) (f g : AffMap m) : (comp f g).Reduced :=
  ⟨Nat.mod_lt _ hm, Nat.mod_lt _ hm⟩

theorem pow_reduced {m : Nat} (hm : 0 < m) (f : AffMap m) : ∀ n, (pow f n).Reduced
  | 0 => id_reduced hm
  | _ + 1 => comp_reduced hm _ _

theorem comp_id_left {m : Nat} (f : AffMap m) (hf : f.Reduced) :
    comp (id m) f = f := by
  cases f with
  | mk a b =>
    rcases hf with ⟨ha, hb⟩
    simp only [comp, id]
    congr 1
    · rw [Nat.mod_mul_mod, Nat.one_mul, Nat.mod_eq_of_lt ha]
    · rw [Nat.add_zero, Nat.mod_mul_mod, Nat.one_mul, Nat.mod_eq_of_lt hb]

theorem comp_id_right {m : Nat} (f : AffMap m) (hf : f.Reduced) :
    comp f (id m) = f := by
  cases f with
  | mk a b =>
    rcases hf with ⟨ha, hb⟩
    simp only [comp, id]
    congr 1
    · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_one, Nat.mod_eq_of_lt ha]
    · rw [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hb]

theorem comp_assoc {m : Nat} (f g h : AffMap m) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f with | mk fa fb =>
  cases g with | mk ga gb =>
  cases h with | mk ha hb =>
  simp only [comp]
  congr 1
  · calc
      ((fa * ga) % m * ha) % m = (fa * ga * ha) % m := by rw [Nat.mod_mul_mod]
      _ = (fa * (ga * ha)) % m := by rw [Nat.mul_assoc]
      _ = (fa * ((ga * ha) % m)) % m := by
            rw [Nat.mul_mod fa (ga * ha), Nat.mul_mod fa ((ga * ha) % m), Nat.mod_mod]
  · calc
      ((fa * ga) % m * hb + (fa * gb + fb) % m) % m
          = ((fa * ga) % m * hb % m + (fa * gb + fb) % m) % m := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      _ = (fa * ga * hb % m + (fa * gb + fb) % m) % m := by rw [Nat.mod_mul_mod]
      _ = (fa * ga * hb + (fa * gb + fb)) % m := by rw [← Nat.add_mod]
      _ = (fa * (ga * hb + gb) + fb) % m := by
            congr 1
            rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      _ = (fa * (ga * hb + gb) % m + fb % m) % m := by rw [Nat.add_mod]
      _ = (fa * ((ga * hb + gb) % m) % m + fb % m) % m := by
            rw [Nat.mul_mod fa (ga * hb + gb), Nat.mul_mod fa ((ga * hb + gb) % m), Nat.mod_mod]
      _ = (fa * ((ga * hb + gb) % m) + fb) % m := by rw [← Nat.add_mod]

theorem pow_one {m : Nat} (f : AffMap m) (hf : f.Reduced) : pow f 1 = f := by
  simp only [pow, comp_id_left f hf]

theorem pow_add {m : Nat} (hm : 0 < m) (f : AffMap m) (hf : f.Reduced) (i : Nat) :
    ∀ j : Nat, pow f (i + j) = comp (pow f i) (pow f j)
  | 0 => by
    simp only [Nat.add_zero, pow]
    exact (comp_id_right (pow f i) (pow_reduced hm f i)).symm
  | j + 1 => by
    rw [Nat.add_succ, pow, pow_add hm f hf i j, pow, comp_assoc]

theorem pow_mul {m : Nat} (hm : 0 < m) (f : AffMap m) (hf : f.Reduced) (i : Nat) :
    ∀ j : Nat, pow (pow f i) j = pow f (i * j)
  | 0 => rfl
  | j + 1 => by
    rw [pow, pow_mul hm f hf i j, Nat.mul_succ, pow_add hm f hf]

theorem pow_id {m : Nat} (hm : 0 < m) : ∀ q : Nat, pow (id m) q = id m
  | 0 => rfl
  | q + 1 => by rw [pow, pow_id hm q, comp_id_left _ (id_reduced hm)]

end AffMap

/-- One substitution step of `frontierSix` on `(f_0, f_1) ∈ Aff(Z/mZ)^2`. -/
def subStep {m : Nat} (p : AffMap m × AffMap m) : AffMap m × AffMap m :=
  (AffMap.comp (AffMap.pow p.2 5) p.1,
   AffMap.comp p.2 (AffMap.comp (AffMap.pow p.1 2) (AffMap.pow p.2 3)))

/-- `j`-th iterate of `subStep`. -/
def subIter {m : Nat} (p : AffMap m × AffMap m) : Nat → AffMap m × AffMap m
  | 0 => p
  | j + 1 => subStep (subIter p j)

/-- Joint post-identity exponent sequence `(u_j, v_j)`. -/
def uvSeq : Nat → Nat × Nat
  | 0 => (1, 0)
  | j + 1 =>
    let (u, v) := uvSeq j
    (u + 5 * v, 2 * u + 4 * v)

def uSeq (j : Nat) : Nat := (uvSeq j).1
def vSeq (j : Nat) : Nat := (uvSeq j).2

theorem uSeq_vSeq_closed_form (j : Nat) :
    7 * ((uSeq j : Nat) : Int) = 2 * (6 ^ j : Nat) + 5 * (-1 : Int) ^ j ∧
    7 * ((vSeq j : Nat) : Int) = 2 * ((6 ^ j : Nat) - (-1 : Int) ^ j) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rcases ih with ⟨hu, hv⟩
    simp only [uSeq, vSeq, uvSeq, Int.natCast_add, Int.natCast_mul] at hu hv ⊢
    have h6 : ((6 ^ (j + 1) : Nat) : Int) = 6 * ((6 ^ j : Nat) : Int) := by
      rw [Nat.pow_succ]; simp [Int.natCast_mul, Int.mul_comm]
    rw [h6, Int.pow_succ]
    constructor <;> omega

/-- Theorem 2 (Post-identity abelian trap): once `f_1 = id (mod m)`, every subsequent
iterate `j >= 0` lies in the cyclic subgroup `<f_0>` with exact exponents `(uSeq j, vSeq j)`. -/
theorem abelian_trap {m : Nat} (hm : 0 < m) (f : AffMap m) (hf : f.Reduced) :
    ∀ j : Nat, subIter (f, AffMap.id m) j = (AffMap.pow f (uSeq j), AffMap.pow f (vSeq j))
  | 0 => by
    simp only [subIter, uSeq, vSeq, uvSeq, AffMap.pow_one f hf, AffMap.pow]
  | j + 1 => by
    rw [subIter, abelian_trap hm f hf j]
    simp only [subStep, uSeq, vSeq, uvSeq]
    congr 1
    · rw [AffMap.pow_mul hm f hf, ← AffMap.pow_add hm f hf]
      congr 1; omega
    · rw [AffMap.pow_mul hm f hf, AffMap.pow_mul hm f hf,
          ← AffMap.pow_add hm f hf, ← AffMap.pow_add hm f hf]
      congr 1; omega

/-- Corollary of Theorem 2: if `f ^ d = id` and `d ∣ vSeq j`, then the second coordinate
of `subIter (f, id) j` is `id`. -/
theorem abelian_trap_id_of_dvd {m d j : Nat} (hm : 0 < m) (f : AffMap m) (hf : f.Reduced)
    (hord : AffMap.pow f d = AffMap.id m) (hdvd : d ∣ vSeq j) :
    (subIter (f, AffMap.id m) j).2 = AffMap.id m := by
  rw [abelian_trap hm f hf j]
  dsimp only
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, ← AffMap.pow_mul hm f hf, hord, AffMap.pow_id hm q]

end CollatzLab.PrimeObstructions
