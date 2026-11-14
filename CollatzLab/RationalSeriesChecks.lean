import CollatzLab.RationalSeries
import CollatzLab.MorphismAperiodic

/-! Independent examples for degree zero, common powers of z, negative coefficients and aperiodicity. -/
namespace CollatzLab.RationalSeries

def impulse (n : Nat) : Int := if n = 0 then 1 else 0

def impulsePair : PolynomialPair where
  degree := 0
  p0 := fun _ => 3
  p1 := fun _ => -3

theorem impulse_identity : (∀ n, impulsePair.residual impulse n = 0) ∧
    (∃ j, j ≤ impulsePair.degree ∧ impulsePair.p1 j ≠ 0) := by
  refine ⟨?_, ⟨0, by decide, by decide⟩⟩
  intro n
  simp [PolynomialPair.residual, PolynomialPair.cutoff, PolynomialPair.convolution,
    PolynomialPair.shift, impulsePair, impulse]
  split <;> omega

theorem impulse_eventually_periodic : EventuallyPeriodic impulse :=
  rational_binary_eventually_periodic impulse
    (by intro n; unfold impulse; split <;> simp) impulsePair impulse_identity.2 impulse_identity.1

def alternating (n : Nat) : Int := if n % 2 = 0 then 1 else 0

/-- Both polynomials have a common factor `z^2`; the denominator starts with -1 after it. -/
def shiftedAlternatingPair : PolynomialPair where
  degree := 4
  p0 := fun j => if j = 2 then 1 else 0
  p1 := fun j => if j = 2 then -1 else if j = 4 then 1 else 0

theorem shifted_alternating_identity :
    (∀ n, shiftedAlternatingPair.residual alternating n = 0) ∧
    (∃ j, j ≤ shiftedAlternatingPair.degree ∧ shiftedAlternatingPair.p1 j ≠ 0) := by
  refine ⟨?_, ⟨2, by decide, by decide⟩⟩
  intro n
  have hterm : shiftedAlternatingPair.residual alternating n =
      (if n = 2 then 1 else 0) - PolynomialPair.shift alternating 2 n +
        PolynomialPair.shift alternating 4 n := by
    simp [PolynomialPair.residual, shiftedAlternatingPair, PolynomialPair.cutoff, PolynomialPair.convolution]
    split <;> split <;> omega
  rw [hterm]
  unfold PolynomialPair.shift alternating
  repeat (first | omega | split)

theorem shifted_alternating_eventually_periodic : EventuallyPeriodic alternating :=
  rational_binary_eventually_periodic alternating
    (by intro n; unfold alternating; split <;> simp) shiftedAlternatingPair
    shifted_alternating_identity.2 shifted_alternating_identity.1

/-- The nonzero-residual conclusion uses word aperiodicity, not Collatz rational exclusion. -/
theorem thueMorse_residual_nonzero (P : PolynomialPair)
    (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) :
    ∃ n, P.residual (Morphism.parityWord Morphism.thueMorse) n ≠ 0 :=
  nonzero_residual _ (Morphism.parity_binary Morphism.thueMorse)
    (Morphism.not_eventually_periodic (by decide) Morphism.thueMorse
      Morphism.thueMorse_admissible.1 Morphism.thueMorse_admissible.2.1
      Morphism.thueMorse_admissible.2.2) P hp

end CollatzLab.RationalSeries
