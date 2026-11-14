import CollatzLab.BoundedLinear
import CollatzLab.UniversalEqualWeight

/-! Explicit coefficient and leading-valuation bounds, uniform across all admissible morphisms. -/
namespace CollatzLab.PolynomialPair
open CollatzLab.Family CollatzLab.FiniteLinear

theorem convolution_abs_bound_general (p v : Nat → Int) (d : Nat) (H X : Int)
    (hH : 0 ≤ H) (hX : 0 ≤ X) (hp : ∀ j, j ≤ d → absInt (p j) ≤ X)
    (hv : ∀ n, absInt (v n) ≤ H) (n : Nat) :
    absInt (convolution p v (d + 1) n) ≤ ((d : Int) + 1) * H * X := by
  rw [convolution_dot]
  have hs : ∀ j, j < d + 1 → absInt (shift v j n) ≤ H := by
    intro j hj
    unfold shift
    split
    · simpa [absInt] using hH
    · exact hv _
  have hh := dot_abs_bound (fun j => shift v j n) p H X hH hX (d + 1) hs
    (by intro j hj; exact hp j (by omega))
  simpa using hh

theorem bounded_polynomial_pair_exists (d : Nat) (H : Int) (hH : 1 ≤ H)
    (v : Nat → Int) (hv : ∀ n, absInt (v n) ≤ H) :
    ∃ P : PolynomialPair, P.degree = d ∧ (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧
      (∀ j, j ≤ P.degree → absInt (P.p0 j) ≤ ((d : Int) + 1) * H * nullBound d H) ∧
      (∀ j, j ≤ P.degree → absInt (P.p1 j) ≤ nullBound d H) ∧
      (∀ n, n < 2 * d + 1 → P.residual v n = 0) := by
  let A := fun i j => v (d + 1 + i - j)
  rcases integer_null_vector_bounded d H hH A (by intro i hi j hj; exact hv _) with
    ⟨x, hx, hrows, hbound⟩
  let P : PolynomialPair := ⟨d, fun n => -convolution x v (d + 1) n, x⟩
  refine ⟨P, rfl, ?_, ?_, ?_, ?_⟩
  · rcases hx with ⟨j, hj, hxj⟩
    exact ⟨j, by change j ≤ d; omega, hxj⟩
  · intro j hj
    change absInt (-convolution x v (d + 1) j) ≤ ((d : Int) + 1) * H * nullBound d H
    rw [absInt_neg_eq]
    exact convolution_abs_bound_general x v d H (nullBound d H) (by omega)
      (by have := nullBound_positive d H hH; omega)
      (by intro i hi; exact hbound i (by omega)) hv j
  · intro j hj
    exact hbound j (by change j ≤ d at hj; omega)
  · intro n hn
    by_cases hlow : n ≤ d
    · change cutoff d (fun n => -convolution x v (d + 1) n) n + convolution x v (d + 1) n = 0
      simp only [cutoff, if_pos hlow]
      omega
    · have hr := hrows (n - (d + 1)) (by omega)
      have he : convolution x v (d + 1) n = dot (A (n - (d + 1))) x (d + 1) := by
        rw [convolution_dot]
        unfold dot
        apply total_ext
        intro j hj
        dsimp [A, shift]
        rw [if_neg (by omega : ¬ n < j), show d + 1 + (n - (d + 1)) = n by omega]
      change cutoff d (fun n => -convolution x v (d + 1) n) n + convolution x v (d + 1) n = 0
      rw [cutoff, if_neg hlow, Int.zero_add, he, hr]

theorem convolution_abs_bound (p v : Nat → Int) (d : Nat) (X : Int) (hX : 0 ≤ X)
    (hp : ∀ j, j ≤ d → absInt (p j) ≤ X) (hv : ∀ n, v n = 0 ∨ v n = 1) (n : Nat) :
    absInt (convolution p v (d + 1) n) ≤ ((d : Int) + 1) * X := by
  rw [convolution_dot]
  have hs : ∀ j, j < d + 1 → absInt (shift v j n) ≤ 1 := by
    intro j hj
    unfold shift
    split
    · decide
    · rcases hv (n - j) with h | h <;> rw [h] <;> decide
  have hh := dot_abs_bound (fun j => shift v j n) p 1 X (by decide) hX (d + 1) hs
    (by intro j hj; exact hp j (by omega))
  simpa using hh

set_option maxRecDepth 100000 in
theorem degree_six_coefficient_bound : nullBound 6 1 = 103762935414616227840 ∧
    nullBound 6 1 = 720 * (2 : Int) ^ 57 ∧
    7 * nullBound 6 1 < (2 : Int) ^ 70 := by decide

theorem coefficientNorm_upper (p : Nat → Int) (C : Int) : ∀ n,
    (∀ j, j < n → absInt (p j) ≤ C) → coefficientNorm p n ≤ 1 + (n : Int) * C
  | 0, _ => by simp [coefficientNorm]
  | n + 1, hp => by
    have hi := coefficientNorm_upper p C n (by intro j hj; exact hp j (by omega))
    have hc := hp n (by omega)
    rw [coefficientNorm]
    simp only [Int.ofNat_add, Int.ofNat_one]
    family_ring

set_option maxRecDepth 100000 in
theorem degree_six_height_cap : (7 : Int) * (2 + 56 * nullBound 6 1) < (2 : Int) ^ 76 := by decide

theorem degree_six_norm_bound (P : PolynomialPair) (hdeg : P.degree = 6)
    (h0 : ∀ j, j ≤ P.degree → absInt (P.p0 j) ≤ 7 * nullBound 6 1)
    (h1 : ∀ j, j ≤ P.degree → absInt (P.p1 j) ≤ nullBound 6 1) :
    P.norm ≤ 2 + 56 * nullBound 6 1 ∧ P.heightConstant < (2 : Int) ^ 76 := by
  have hn0 := coefficientNorm_upper P.p0 (7 * nullBound 6 1) 7 (by
    intro j hj; exact h0 j (by omega))
  have hn1 := coefficientNorm_upper P.p1 (nullBound 6 1) 7 (by
    intro j hj; exact h1 j (by omega))
  have hn : P.norm ≤ 2 + 56 * nullBound 6 1 := by
    unfold norm
    rw [hdeg]
    change coefficientNorm P.p0 7 + coefficientNorm P.p1 7 ≤ _
    family_ring
  have hh := Int.mul_le_mul_of_nonneg_left hn (by decide : (0 : Int) ≤ 7)
  refine ⟨hn, ?_⟩
  unfold heightConstant
  rw [hdeg]
  exact Int.lt_of_le_of_lt hh degree_six_height_cap

/-- A nonzero first residual of a bounded degree-six pair has valuation strictly below 70. -/
theorem degree_six_leading_bound (P : PolynomialPair) (hdeg : P.degree = 6)
    (hp : ∀ j, j ≤ P.degree → absInt (P.p1 j) ≤ nullBound 6 1)
    (v : Nat → Int) (hv : ∀ n, v n = 0 ∨ v n = 1) (N : Nat) (hN : 13 ≤ N)
    (hfirst : P.residual v N ≠ 0) :
    ∃ val : Nat, ∃ c : Int, val < 70 ∧ c % 2 = 1 ∧
      P.residual v N = (2 : Int) ^ val * c := by
  have hpositive := nullBound_positive 6 1 (by decide)
  have hconv := convolution_abs_bound P.p1 v P.degree (nullBound 6 1) (by omega) hp hv N
  have hr : P.residual v N = convolution P.p1 v (P.degree + 1) N := by
    unfold residual cutoff
    rw [if_neg (by omega), Int.zero_add]
  have hupper : absInt (P.residual v N) < (2 : Int) ^ 70 := by
    rw [hr, hdeg]
    rw [hdeg] at hconv
    exact Int.lt_of_le_of_lt hconv degree_six_coefficient_bound.2.2
  rcases int_two_power_factorization _ hfirst with ⟨val, c, hc, he⟩
  have hlower := (odd_multiple_bounds _ val ⟨c, hc, he⟩).2.2.2
  have hval : val < 70 := by
    by_cases hh : val < 70
    · exact hh
    · have hm := pow_mono_exp (x := (2 : Int)) (by decide) (show 70 ≤ val by omega)
      omega
  exact ⟨val, c, hval, hc, he⟩

theorem uniform_safe_level (L : Nat) (hL : 2 ≤ L) (val : Nat) (hv : val < 70)
    (k : Nat) (hk : 6 ≤ k) : val < L ^ (k + 1) := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ k + 1 by omega)
  have hmono := Nat.pow_le_pow_left hL (k + 1)
  change 128 ≤ 2 ^ (k + 1) at hp
  omega

end CollatzLab.PolynomialPair

namespace CollatzLab.Morphism
open CollatzLab.FiniteLinear CollatzLab.PolynomialPair

/-- A single safe level 6 works for the chosen bounded certificate of every admissible morphism. -/
theorem universal_bounded_degree_six_certificate {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) :
    ∃ P : PolynomialPair, ∃ N val : Nat, ∃ c : Int,
      P.degree = 6 ∧ 13 ≤ N ∧ (∃ j, j ≤ 6 ∧ P.p1 j ≠ 0) ∧
      (∀ j, j ≤ 6 → absInt (P.p1 j) ≤ 103762935414616227840) ∧
      P.heightConstant < (2 : Int) ^ 76 ∧ P.First (parityWord M) N ∧ P.Gap M N ∧
      val < 70 ∧ c % 2 = 1 ∧ P.residual (parityWord M) N = (2 : Int) ^ val * c ∧
      (∀ k, 6 ≤ k → val < L ^ (k + 1)) := by
  have hbinary := parity_binary M
  have habs : ∀ n, absInt (parityWord M n) ≤ 1 := by
    intro n
    rcases hbinary n with h | h <;> rw [h] <;> decide
  rcases bounded_polynomial_pair_exists 6 1 (by decide) (parityWord M) habs with
    ⟨P, hdeg, hp, hnum, hbound, hz⟩
  rcases RationalSeries.nonzero_residual _ hbinary (not_eventually_periodic hL M h1 hw hd) P hp with ⟨n, hn⟩
  rcases RationalSeries.first_nonzero_coefficient (P.residual (parityWord M)) n
    ⟨n, Nat.le_refl _, hn⟩ with ⟨N, _, hlead, hbefore⟩
  have hN : 13 ≤ N := by
    by_cases h : N < 13
    · have hh := hz N h
      contradiction
    · omega
  have hnum' : ∀ j, j ≤ P.degree → absInt (P.p0 j) ≤ 7 * nullBound 6 1 := by
    simpa using hnum
  have hnorm := degree_six_norm_bound P hdeg hnum' hbound
  rcases degree_six_leading_bound P hdeg hbound (parityWord M) hbinary N hN hlead with ⟨val, c, hv, hc, he⟩
  have hgap : P.Gap M N := by
    unfold Gap
    rw [hdeg]
    have hm := CollatzLab.Family.pow_mono_exp (x := (2 : Int)) (by decide)
      (Nat.mul_le_mul_left (L * (L - 1)) hN)
    exact Int.lt_of_lt_of_le (degree_six_ledger hL M hw hd) hm
  have hp' : ∃ j, j ≤ 6 ∧ P.p1 j ≠ 0 := by rw [hdeg] at hp; exact hp
  have hbound' : ∀ j, j ≤ 6 → absInt (P.p1 j) ≤ 103762935414616227840 := by
    rw [hdeg, degree_six_coefficient_bound.1] at hbound
    exact hbound
  exact ⟨P, N, val, c, hdeg, hN, hp', hbound', hnorm.2, ⟨hbefore, hlead⟩, hgap, hv, hc, he,
    fun k hk => uniform_safe_level L hL val hv k hk⟩

/-- Uniform coefficient bounds give the exact valuation at every level k>=6 for the chosen certificate. -/
theorem universal_degree_six_valuation {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) :
    ∃ P : PolynomialPair, ∃ N val : Nat, P.degree = 6 ∧ 13 ≤ N ∧ val < 70 ∧
      P.heightConstant < (2 : Int) ^ 76 ∧ P.First (parityWord M) N ∧ P.Gap M N ∧
      (∀ p q : Int, ∀ k : Nat, RealizesWord p q (parityWord M) → 6 ≤ k →
        let exponent := N * L ^ (k + 1) + val
        PolynomialPair.E M P p q k ≠ 0 ∧ (2 : Int) ^ exponent ∣ PolynomialPair.E M P p q k ∧
          ¬ (2 : Int) ^ (exponent + 1) ∣ PolynomialPair.E M P p q k ∧
            (2 : Int) ^ exponent ≤ absInt (PolynomialPair.E M P p q k)) := by
  rcases universal_bounded_degree_six_certificate hL M h1 hw hd with
    ⟨P, N, val, c, hdeg, hN, _, _, hheight, hfirst, hgap, hv, hc, he, hsafe⟩
  refine ⟨P, N, val, hdeg, hN, hv, hheight, hfirst, hgap, ?_⟩
  intro p q k hr hk
  exact PolynomialPair.valuation hL M h1 hw hd P N val (by omega) hfirst.1 c hc he hr k (hsafe k hk)

end CollatzLab.Morphism
