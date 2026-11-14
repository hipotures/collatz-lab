import CollatzLab.Family

/-! Semantic regressions: literal morphism images, first disagreement, and actual Collatz witnesses. -/
namespace CollatzLab.Family

/-- At valid offsets, the two block images are exactly the stated binary words. -/
theorem block_images (L : Nat) (hL : 3 ≤ L) (r : Nat) (hr : r < L) :
    familyBlock L 1 r = (if r < L - 1 then 1 else 0) ∧
    familyBlock L 0 r = (if r < L - 2 ∨ r = L - 1 then 1 else 0) := by
  dsimp [familyBlock]
  by_cases hs : r < L - 2
  · simp [hs, show r < L - 1 by omega]
  · by_cases he : r = L - 2
    · subst r; simp [show L - 2 < L - 1 by omega,
        show L - 2 ≠ L - 1 by omega]
    · have he1 : r = L - 1 := by omega
      subst r
      simp [show ¬ L - 1 < L - 2 by omega, show L - 1 ≠ L - 2 by omega]

/-- Function equality expressing `w_L = mu_L(w_L)`. -/
theorem fixed_point (L : Nat) (hL : 3 ≤ L) :
    familyWord L = fun n => familyBlock L (familyWord L (n / L)) (n % L) := by
  funext n; exact word_rec hL n

/-- All symbols strictly before `N=L^2-2` coincide with the periodic approximant. -/
theorem before_first_difference (L : Nat) (hL : 3 ≤ L) (n : Nat) (hn : n < N L) :
    familyWord L n = (if n % L = L - 1 then 0 else 1) := by
  have hd : n / L < L := (Nat.div_lt_iff_lt_mul (by omega)).2 (by dsimp [N] at hn; omega)
  have hm : n % L < L := Nat.mod_lt n (by omega)
  have he : L * (n / L) + n % L = n := by have := Nat.mod_add_div n L; omega
  conv => lhs; rw [← he, word_block hL _ _ hm]
  by_cases hq : n / L < L - 1
  · rw [first_block L hL _ hq]
    have hb := (block_images L hL (n % L) hm).1
    rw [hb]
    by_cases hl : n % L = L - 1
    · simp [hl]
    · simp [hl, show n % L < L - 1 by omega]
  · have hqeq : n / L = L - 1 := by omega
    rw [hqeq] at he
    have hsplit := order_split L hL
    have hs : n % L < L - 2 := by omega
    simp [familyBlock, hs, show n % L ≠ L - 1 by omega]

/-- The initial numerator agrees with the normalized formula, with exact division. -/
theorem initial_normalization {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) :
    (2 : Int) ^ (L - 2) * u L p q 0 = B L * ((B L - A L) * p + c0 L * q) := by
  have hi := congrArg (fun t : Int => B L * t) (quotient_exact (by omega) hr 0)
  change (2 : Int) ^ (L - 2) * (B L * quotient L p q 0) = _
  simp only [Nat.mul_zero, numIter] at hi
  family_ring

/-- The closed tower formulas in the statement of Theorem 4.1. -/
theorem tower_bases (L k : Nat) :
    a L k = A L ^ (L ^ k) ∧ b L k = B L ^ (L ^ k) := by
  rw [a_closed, b_closed, A, B, int_pow_mul, int_pow_mul]
  exact ⟨rfl, rfl⟩

end CollatzLab.Family

namespace CollatzLab

set_option maxRecDepth 100000 in
/-- A positive integer matches all 25 symbols of the `L=5` regression prefix and grows. -/
theorem family_five_positive_prefix_witness :
    (0 : Int) < 25850607 ∧
    (∀ j : Nat, j < 25 → seedParity 1 25850607 j = familyWord 5 j) ∧
    tIterInt 25850607 25 > 25850607 := by decide

/-- The rational parity predicate also has an infinite realization independent of the family. -/
theorem realizes_all_zero : RealizesWord 0 1 (fun _ => 0) := by
  refine ⟨by decide, by decide, ?_⟩
  have hi : ∀ n, numIter 1 0 n = 0 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => change numStep 1 (numIter 1 0 n) = 0; rw [ih]; rfl
  intro n; simp [seedParity, hi]

end CollatzLab
