import CollatzLab.Family

/-! A strict integer base gap beats any singly exponential factor. -/
namespace CollatzLab
open Family

theorem homogeneous_bernoulli (B : Int) (hB : 1 ≤ B) : ∀ n : Nat,
    B ^ (n + 1) + ((n : Int) + 1) * B ^ n ≤ (B + 1) ^ (n + 1)
  | 0 => by simp [Int.pow_zero, int_pow_one]
  | n + 1 => by
    have hi := homogeneous_bernoulli B hB n
    have hm := Int.mul_le_mul_of_nonneg_right hi (show 0 ≤ B + 1 by omega)
    have hextra := Int.mul_nonneg (show 0 ≤ (n : Int) + 1 by omega)
      (pow_nonneg_of_nonneg (show 0 ≤ B by omega) n)
    simp only [Int.ofNat_add, Int.ofNat_one]
    rw [Int.pow_succ (B + 1), Int.pow_succ B]
    have hpow : B ^ (n + 1) = B ^ n * B := Int.pow_succ B n
    rw [hpow] at hm ⊢
    family_ring

theorem amplify_integer_gap (A B D : Int) (hAB : B < A) (hB : 1 ≤ B) (_hD : 1 ≤ D)
    (n : Nat) (hn : 1 ≤ n) (hsize : B * D ≤ (n : Int)) :
    (D + 1) * B ^ n ≤ A ^ n := by
  have hbern := homogeneous_bernoulli B hB (n - 1)
  rw [show n - 1 + 1 = n by omega] at hbern
  have hncast : (((n - 1 : Nat) : Int) + 1) = (n : Int) := by omega
  rw [hncast] at hbern
  have hm := Int.mul_le_mul_of_nonneg_right hsize
    (pow_nonneg_of_nonneg (show 0 ≤ B by omega) (n - 1))
  have hpow : B ^ n = B ^ (n - 1) * B := by rw [← Int.pow_succ, show n - 1 + 1 = n by omega]
  have hmono := pow_le_pow_of_le (show 0 ≤ B + 1 by omega) (show B + 1 ≤ A by omega) n
  rw [hpow] at hbern ⊢
  family_ring

theorem two_mul_le_pow_two : ∀ n : Nat, 2 * n ≤ 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have hi := two_mul_le_pow_two n
    by_cases hn : n = 0
    · subst n; decide
    · rw [Nat.pow_succ]; omega

/-- Entirely integer arithmetic; the bases may be arbitrarily close. -/
theorem no_doubly_exponential_bound (L : Nat) (hL : 2 ≤ L)
    (A B K D : Int) (hB : 1 ≤ B) (hAB : B < A) (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hbound : ∀ k : Nat, A ^ (L ^ k) ≤ K * D ^ k * B ^ (L ^ k)) : False := by
  let J := (B * D).toNat
  have hBD : 1 ≤ B * D := by
    have hh := Int.mul_le_mul hB hD (by decide : (0 : Int) ≤ 1) (by omega : 0 ≤ B)
    simpa using hh
  have hJ : (J : Int) = B * D := Int.toNat_of_nonneg (by omega)
  have hLpow : J < L ^ J := by
    have h0 := nat_lt_pow2 J
    have h1 := Nat.pow_le_pow_left hL J
    omega
  have hsize : B * D ≤ ((L ^ J : Nat) : Int) := by omega
  have hamp := amplify_integer_gap A B D hAB hB hD (L ^ J)
    (nat_power_ge_one (by omega) J) hsize
  have hlarge : ∀ t : Nat, (D + 1) ^ (L ^ t) ≤ K * D ^ J * D ^ t := by
    intro t
    have hlower := pow_le_pow_of_le
      (Int.mul_nonneg (show 0 ≤ D + 1 by omega) (pow_nonneg_of_nonneg (show 0 ≤ B by omega) _))
      hamp (L ^ t)
    rw [mul_pow, int_pow_mul, int_pow_mul] at hlower
    have hupper := hbound (J + t)
    rw [Nat.pow_add, int_pow_add] at hupper
    have hpos := pow_pos_of_pos (show 0 < B by omega) (L ^ J * L ^ t)
    apply Int.le_of_mul_le_mul_right (a := B ^ (L ^ J * L ^ t))
    · exact Int.le_trans hlower (by simpa [Int.mul_assoc] using hupper)
    · exact hpos
  have hsmall : ∀ t : Nat, (2 : Int) ^ t ≤ K * D ^ J := by
    intro t
    have hexp : 2 * t ≤ L ^ t := Nat.le_trans (two_mul_le_pow_two t) (Nat.pow_le_pow_left hL t)
    have hm := pow_mono_exp (x := D + 1) (by omega) hexp
    have hbase : (2 : Int) * D ≤ (D + 1) ^ 2 := by
      have hh := Int.mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ D by omega)
      simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]
      family_ring
    have hp := pow_le_pow_of_le (show 0 ≤ 2 * D by omega) hbase t
    rw [mul_pow, int_pow_mul] at hp
    have hh := Int.le_trans (Int.le_trans hp hm) (hlarge t)
    have hpos := pow_pos_of_pos (show 0 < D by omega) t
    exact Int.le_of_mul_le_mul_right hh hpos
  let T := (K * D ^ J).toNat
  have hnonneg := Int.mul_nonneg (show 0 ≤ K by omega) (pow_nonneg_of_nonneg (show 0 ≤ D by omega) J)
  have hT : (T : Int) = K * D ^ J := Int.toNat_of_nonneg hnonneg
  have hlt := Int.ofNat_lt.mpr (nat_lt_pow2 T)
  rw [int_ofNat_pow] at hlt
  have hlt' : (T : Int) < (2 : Int) ^ T := hlt
  have hh := hsmall T
  omega

/-- Strict order of positive bases is retained at every positive integer exponent. -/
theorem positive_pow_strict (A B : Int) (hB : 1 ≤ B) (hAB : B < A) :
    ∀ n : Nat, 1 ≤ n → B ^ n < A ^ n
  | 0, hn => by omega
  | n + 1, _ => by
    have hm := pow_le_pow_of_le (show 0 ≤ B by omega) (show B ≤ A by omega) n
    have h0 := Int.mul_le_mul_of_nonneg_right hm (show 0 ≤ B by omega)
    have h1 := Int.mul_lt_mul_of_pos_left hAB (pow_pos_of_pos (show 0 < A by omega) n)
    rw [Int.pow_succ, Int.pow_succ]
    exact Int.lt_of_le_of_lt h0 h1

/-- Discarding any fixed finite initial segment does not weaken the contradiction. -/
theorem no_eventual_doubly_exponential_bound (L : Nat) (hL : 2 ≤ L)
    (A B K D : Int) (hB : 1 ≤ B) (hAB : B < A) (hK : 1 ≤ K) (hD : 1 ≤ D)
    (k0 : Nat)
    (hbound : ∀ k : Nat, k0 ≤ k → A ^ (L ^ k) ≤ K * D ^ k * B ^ (L ^ k)) : False := by
  let A' := A ^ (L ^ k0)
  let B' := B ^ (L ^ k0)
  let K' := K * D ^ k0
  have hn := nat_power_ge_one (show 1 ≤ L by omega) k0
  have hB' : 1 ≤ B' := pow_ge_one hB _
  have hAB' : B' < A' := positive_pow_strict A B hB hAB _ hn
  have hK' : 1 ≤ K' := by
    have hp := pow_ge_one hD k0
    have hm := Int.mul_le_mul hK hp (by decide : (0 : Int) ≤ 1) (by omega : 0 ≤ K)
    exact hm
  apply no_doubly_exponential_bound L hL A' B' K' D hB' hAB' hK' hD
  intro k
  have hh := hbound (k0 + k) (by omega)
  dsimp [A', B', K']
  rw [Nat.pow_add, int_pow_add] at hh
  rw [int_pow_mul, int_pow_mul]
  simpa [Int.mul_assoc] using hh

end CollatzLab
