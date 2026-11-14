import CollatzLab.PolynomialPair
import CollatzLab.FiniteLinear

/-! Uniform raw polynomial approximants from division-free integer linear algebra. -/
namespace CollatzLab.PolynomialPair
open CollatzLab.FiniteLinear

/-- Finite convolution is a dot product, with the zero extension made explicit. -/
theorem convolution_dot (p v : Nat → Int) (n : Nat) : ∀ count,
    convolution p v count n = dot (fun j => shift v j n) p count
  | 0 => rfl
  | count + 1 => by
    rw [convolution, convolution_dot]
    change dot (fun j => shift v j n) p count + p count * shift v count n =
      dot (fun j => shift v j n) p count + shift v count n * p count
    rw [Int.mul_comm (p count)]

/-- `d` homogeneous constraints in `d+1` unknowns give order at least `2*d+1`.
This holds for all integer coefficient sequences, without any binary restriction. -/
theorem polynomial_pair_exists (d : Nat) (v : Nat → Int) :
    ∃ P : PolynomialPair, P.degree = d ∧
      (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧
      (∀ n, n < 2 * d + 1 → P.residual v n = 0) := by
  let A := fun i j => v (d + 1 + i - j)
  rcases integer_null_vector d A with ⟨x, hx, hrows⟩
  let P : PolynomialPair := ⟨d, fun n => -convolution x v (d + 1) n, x⟩
  refine ⟨P, rfl, ?_, ?_⟩
  · rcases hx with ⟨j, hj, hxj⟩
    exact ⟨j, by change j ≤ d; omega, hxj⟩
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

/-- One universally quantified existence theorem; no finite catalogue is used. -/
theorem degree_six_pair_exists (v : Nat → Int) :
    ∃ P : PolynomialPair, P.degree = 6 ∧
      (∃ j, j ≤ 6 ∧ P.p1 j ≠ 0) ∧
      (∀ n, n < 13 → P.residual v n = 0) := by
  rcases polynomial_pair_exists 6 v with ⟨P, hd, hp, hz⟩
  rw [hd] at hp
  exact ⟨P, hd, hp, hz⟩

end CollatzLab.PolynomialPair
