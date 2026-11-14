import CollatzLab.BoundedRationalSeries

/-! Signed alphabets, singleton encodings, and the necessary boundedness hypothesis. -/
namespace CollatzLab.RationalSeries
open PolynomialPair

def signedWave (n : Nat) : Int := if n % 2 = 0 then 3 else -2

def signedWavePair : PolynomialPair where
  degree := 2
  p0 := fun j => if j = 0 then -3 else if j = 1 then 2 else 0
  p1 := fun j => if j = 0 then 1 else if j = 2 then -1 else 0

theorem signedWave_identity : ∀ n, signedWavePair.residual signedWave n = 0 := by
  intro n
  simp [residual, cutoff, convolution, shift, signedWavePair, signedWave]
  repeat (first | omega | split)

theorem signedWave_periodic : EventuallyPeriodic signedWave :=
  rational_bounded_integer_eventually_periodic signedWave
    ⟨-2, 3, by intro n; unfold signedWave; split <;> omega⟩ signedWavePair
    ⟨0, by decide, by decide⟩ signedWave_identity

def singletonPair : PolynomialPair where
  degree := 1
  p0 := fun j => if j = 0 then 7 else 0
  p1 := fun j => if j = 0 then 1 else -1

theorem singleton_identity : ∀ n, singletonPair.residual (fun _ => -7) n = 0 := by
  intro n
  simp [residual, cutoff, convolution, shift, singletonPair]
  repeat (first | omega | split)

/-- Base one is valid for an alphabet containing exactly one symbol. -/
theorem singleton_base_one : EventuallyPeriodic (fun _ => (-7 : Int)) :=
  rational_interval_eventually_periodic (fun _ => -7) (-7) 1 (by decide)
    (by intro n; dsimp only; decide) singletonPair ⟨0, by decide, by decide⟩ singleton_identity

def countingPair : PolynomialPair where
  degree := 2
  p0 := fun j => if j = 1 then -1 else 0
  p1 := fun j => if j = 0 then 1 else if j = 1 then -2 else 1

/-- The unbounded sequence n has rational generating function z/(1-z)^2. -/
theorem counting_identity : ∀ n, countingPair.residual (fun n => (n : Int)) n = 0 := by
  intro n
  simp [residual, cutoff, convolution, shift, countingPair]
  repeat (first | omega | split)

theorem counting_not_eventually_periodic : ¬ EventuallyPeriodic (fun n => (n : Int)) := by
  rintro ⟨start, p, hp, hper⟩
  have hh := hper start (Nat.le_refl _)
  change ((start + p : Nat) : Int) = (start : Int) at hh
  omega

theorem counting_not_bounded : ¬ (∃ lo hi : Int, ∀ n : Nat, lo ≤ (n : Int) ∧ (n : Int) ≤ hi) := by
  rintro ⟨lo, hi, hb⟩
  have hpos : 0 ≤ hi := (hb 0).2
  have hcast : (((hi.toNat : Nat) : Int)) = hi := Int.toNat_of_nonneg hpos
  have hh := (hb (hi.toNat + 1)).2
  omega

end CollatzLab.RationalSeries
