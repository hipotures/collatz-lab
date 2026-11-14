import CollatzLab.FamilyHeight

/-! The universal irrationality theorem and inverse-branch corollaries. -/
set_option maxRecDepth 4096

namespace CollatzLab.Family

/-- The exponent gap uses integer inequalities only, at every `L >= 4`. -/
theorem exponent_gap (L : Nat) (hL : 4 ≤ L) :
    125 + 8 * formExponent L ≤ 5 * (L * N L) := by
  have hsq : 4 * L ≤ L * L := Nat.mul_le_mul_right L hL
  have hcub : 4 * (L * L) ≤ L * (L * L) := Nat.mul_le_mul_right (L * L) hL
  have hn : N L + 2 = L * L := by dsimp [N]; omega
  have hy : formExponent L + 1 = L * L + L := by dsimp [formExponent]; omega
  have hx := congrArg (fun n : Nat => L * n) hn
  dsimp only at hx
  rw [Nat.mul_add, Nat.mul_comm L 2] at hx
  omega

theorem pow_mono_exp {x : Int} (hx : 1 ≤ x) {n m : Nat} (hnm : n ≤ m) : x ^ n ≤ x ^ m := by
  have hp := Int.mul_le_mul_of_nonneg_left (pow_ge_one hx (m - n))
    (pow_nonneg_of_nonneg (by omega : 0 ≤ x) n)
  have he : x ^ m = x ^ n * x ^ (m - n) := by
    rw [← int_pow_add, show n + (m - n) = m by omega]
  rw [he]; simpa using hp

/-- Uniform comparison of the two exponential bases. Fifth powers avoid logarithms. -/
theorem base_gap (L : Nat) (hL : 4 ≤ L) :
    (2 : Int) ^ 25 * (3 : Int) ^ (formExponent L) ≤ (2 : Int) ^ (L * N L) := by
  let x := (2 : Int) ^ 25 * (3 : Int) ^ (formExponent L)
  let y := (2 : Int) ^ (L * N L)
  have h3 := pow_le_pow_of_le (x := (3 : Int) ^ 5) (y := (2 : Int) ^ 8)
    (by decide) (by decide) (formExponent L)
  rw [int_pow_mul, int_pow_mul] at h3
  have hmul := Int.mul_le_mul_of_nonneg_left h3 (by decide : (0 : Int) ≤ (2 : Int) ^ 125)
  have hexp := pow_mono_exp (x := 2) (by decide) (exponent_gap L hL)
  have hxy : x ^ 5 ≤ y ^ 5 := by
    have hx : x ^ 5 = (2 : Int) ^ 125 * (3 : Int) ^ (5 * formExponent L) := by
      dsimp only [x]; simp only [mul_pow, int_pow_mul]
      rw [Nat.mul_comm (formExponent L) 5]
    have hy : y ^ 5 = (2 : Int) ^ (5 * (L * N L)) := by
      dsimp only [y]; simp only [int_pow_mul, Nat.mul_comm]
    rw [hx, hy]
    rw [← int_pow_add] at hmul
    omega
  by_cases hle : x ≤ y
  · exact hle
  · have hyp : 0 < y := pow_pos_of_pos (by decide) _
    have hgt := pow_strict hyp (show y < x by omega) 5 (by decide)
    omega

/-- Raise the uniform comparison to an arbitrary natural exponent. -/
theorem powered_gap (L : Nat) (hL : 4 ≤ L) (n : Nat) :
    (2 : Int) ^ (25 * n) * (3 : Int) ^ (formExponent L * n) ≤
      (2 : Int) ^ (L * N L * n) := by
  have hh := pow_le_pow_of_le
    (Int.mul_nonneg (pow_nonneg_of_nonneg (by decide : (0 : Int) ≤ 2) 25)
      (pow_nonneg_of_nonneg (by decide : (0 : Int) ≤ 3) (formExponent L))) (base_gap L hL) n
  rw [mul_pow, int_pow_mul, int_pow_mul, int_pow_mul] at hh
  exact hh

/-- A hypothetical rational realization would bound an unbounded exponential for every `k`. -/
theorem exponential_bound {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    (2 : Int) ^ (25 * L ^ k) < 3 * H L p q 0 := by
  have hlo := (valuation hL hr k).2.2.2
  have hhi := form_upper hL hr k
  have hgap := powered_gap L hL (L ^ k)
  have he : L * N L * L ^ k = N L * L ^ (k + 1) := by rw [Nat.pow_succ]; ac_rfl
  rw [he] at hgap
  have hh : (2 : Int) ^ (25 * L ^ k) * (3 : Int) ^ (formExponent L * L ^ k) <
      (3 * H L p q 0) * (3 : Int) ^ (formExponent L * L ^ k) := by omega
  have hp := pow_pos_of_pos (x := 3) (by decide) (formExponent L * L ^ k)
  by_cases h : (2 : Int) ^ (25 * L ^ k) < 3 * H L p q 0
  · exact h
  · have hm := Int.mul_le_mul_of_nonneg_right (show 3 * H L p q 0 ≤ (2 : Int) ^ (25 * L ^ k) by omega)
      (by omega : 0 ≤ (3 : Int) ^ (formExponent L * L ^ k))
    omega

theorem nat_lt_family_power (L : Nat) (hL : 4 ≤ L) (k : Nat) : k < L ^ k := by
  have hh := Nat.pow_le_pow_left hL k
  have hi := nat_lt_pow4 k
  omega

end Family

/-- Theorem 4.1: every block length `L >= 4`, with the original rational parity predicate. -/
theorem no_rational_seed_realizes_family (L : Nat) (hL : 4 ≤ L) (p q : Int) :
    ¬ RealizesWord p q (familyWord L) := by
  intro hr
  let K := (3 * Family.H L p q 0).toNat
  have hb := Family.exponential_bound hL hr K
  have hk : K < 2 ^ (25 * L ^ K) := by
    have h1 := Family.nat_lt_family_power L hL K
    have h2 := nat_lt_pow2 (25 * L ^ K)
    omega
  have hpow : (K : Int) < (2 : Int) ^ (25 * L ^ K) := by
    have hh := Int.ofNat_lt.mpr hk
    rw [int_ofNat_pow] at hh
    exact hh
  have hpos := Family.height_positive hL hr 0
  have hK : (K : Int) = 3 * Family.H L p q 0 := Int.toNat_of_nonneg (by omega)
  omega

/-- Corollary 9.1: exclude every finite shift by the already verified inverse parity branches. -/
theorem no_rational_seed_realizes_shifted_family (L : Nat) (hL : 4 ≤ L) :
    ∀ (t : Nat) (p q : Int), ¬ RealizesWord p q (shiftWord (familyWord L) t)
  | 0, p, q, hr => by
    apply no_rational_seed_realizes_family L hL p q
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro j
    simpa [shiftWord] using hr.2.2 j
  | t + 1, p, q, hr =>
    no_rational_seed_realizes_shifted_family L hL t
      (invBranchNum (familyWord L t) p q) (invBranchDen (familyWord L t) q)
      (realizes_shiftWord_pred (Family.word_binary L t) hr)

/-- No rational orbit can eventually equal a shifted family word. -/
theorem no_eventually_shifted_family_itinerary (L : Nat) (hL : 4 ≤ L)
    (s t : Nat) (p q : Int) (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = familyWord L (t + j)) := by
  intro ht
  apply no_rational_seed_realizes_shifted_family L hL t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

/-- In particular, no integer realizes any family word or shifted tail. -/
theorem no_int_seed_realizes_shifted_family (L : Nat) (hL : 4 ≤ L) (t : Nat) (p : Int) :
    ¬ RealizesWord p 1 (shiftWord (familyWord L) t) :=
  no_rational_seed_realizes_shifted_family L hL t p 1

end CollatzLab
