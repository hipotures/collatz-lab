import CollatzLab.SpectralThreshold
import CollatzLab.RepeatedPrefix
import CollatzLab.SignedContraction

/-! A supercritical exclusion from partial repetitions, with initial word 101. -/
namespace CollatzLab.Morphism

def nonContracting1011 : Images 4 where
  zero := fun _ => true
  one := fun j => decide (j.val ≠ 1)

theorem nonContracting1011_images :
    List.ofFn nonContracting1011.one = [true, false, true, true] ∧
    List.ofFn nonContracting1011.zero = [true, true, true, true] ∧
    image nonContracting1011 true 0 = true ∧
    frequencyDen nonContracting1011 = 5 ∧ weightDelta nonContracting1011 = -1 ∧
    weight (image nonContracting1011 false) 4 = 4 := by decide

theorem nonContracting1011_columns (n : Nat) :
    parityWord nonContracting1011 (4 * n) = 1 ∧
    parityWord nonContracting1011 (4 * n + 1) = 1 - parityWord nonContracting1011 n ∧
    parityWord nonContracting1011 (4 * n + 2) = 1 ∧
    parityWord nonContracting1011 (4 * n + 3) = 1 := by
  have h := word_block (by decide) nonContracting1011 nonContracting1011_images.2.2.1 n
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  change word nonContracting1011 (4 * n) = _ at h0
  simp only [parityWord, h0, h1, h2, h3]
  cases hb : word nonContracting1011 n <;> decide

theorem nonContracting1011_not_periodic_from (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → parityWord nonContracting1011 (n + p) = parityWord nonContracting1011 n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    let d := p / 4
    have hz : parityWord nonContracting1011 (4 * (4 * start) + 1) = 0 := by
      rw [(nonContracting1011_columns _).2.1, (nonContracting1011_columns _).1]
      omega
    rcases (show p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 by omega) with h0 | h1 | h2 | h3
    · apply ih d (by dsimp [d]; omega) start (by dsimp [d]; omega)
      intro n hn
      have hh := hper (4 * n + 1) (by omega)
      rw [show 4 * n + 1 + p = 4 * (n + d) + 1 by dsimp [d]; omega,
        (nonContracting1011_columns _).2.1, (nonContracting1011_columns _).2.1] at hh
      omega
    · have hh := hper (4 * (4 * start) + 1) (by omega)
      rw [hz, show 4 * (4 * start) + 1 + p = 4 * (4 * start + d) + 2 by dsimp [d]; omega,
        (nonContracting1011_columns _).2.2.1] at hh
      omega
    · have hh := hper (4 * (4 * start) + 1) (by omega)
      rw [hz, show 4 * (4 * start) + 1 + p = 4 * (4 * start + d) + 3 by dsimp [d]; omega,
        (nonContracting1011_columns _).2.2.2] at hh
      omega
    · have hh := hper (4 * (4 * start) + 1) (by omega)
      rw [hz, show 4 * (4 * start) + 1 + p = 4 * (4 * start + d + 1) by dsimp [d]; omega,
        (nonContracting1011_columns _).1] at hh
      omega

theorem nonContracting1011_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord nonContracting1011) := by
  rintro ⟨start, p, hp, hper⟩
  exact nonContracting1011_not_periodic_from p start hp hper

/-- The initial 101 gives a return of length 4^k at position 2*4^k. -/
theorem nonContracting1011_partial_return (k j : Nat) (hj : j < 4 ^ k) :
    word nonContracting1011 (2 * 4 ^ k + j) = word nonContracting1011 j := by
  have hh := word_power_congr (by decide) nonContracting1011 nonContracting1011_images.2.2.1
    k 2 0 (by decide) j hj
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.mul_comm (4 ^ k) 2] using hh

/-- The transient in the actual prefix of length 2*4^k is bounded by three. -/
theorem nonContracting1011_prefix_weight (k : Nat) :
    8 * (4 ^ k : Nat) - 3 ≤ 5 * (weight (word nonContracting1011) (2 * 4 ^ k) : Int) ∧
    5 * (weight (word nonContracting1011) (2 * 4 ^ k) : Int) ≤ 8 * (4 ^ k : Nat) + 3 := by
  have hh := balance_power (by decide) nonContracting1011 nonContracting1011_images.2.2.1 k 0 2
  simp only [Nat.mul_zero, balance, Nat.zero_add, nonContracting1011_images.2.2.2.1,
    nonContracting1011_images.2.2.2.2.1, nonContracting1011_images.2.2.2.2.2] at hh
  have hw : weight (word nonContracting1011) 2 = 1 := by decide
  rw [hw, Nat.mul_comm (4 ^ k) 2, Int.natCast_mul] at hh
  change 5 * (weight (word nonContracting1011) (2 * 4 ^ k) : Int) -
    4 * (2 * (4 ^ k : Nat)) = (-1 : Int) ^ k * (5 * 1 - 4 * 2) at hh
  have habs : absInt ((-1 : Int) ^ k) = 1 := by
    rw [absInt_pow_eq]
    have hunit : ∀ n : Nat, (1 : Int) ^ n = 1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Int.pow_succ, ih]; rfl
    exact hunit k
  unfold absInt at habs
  split at habs <;> omega

theorem nonContracting1011_no_uniform_chunks (t k R : Nat) (hk : 1 ≤ k)
    (hb : ∀ n, weight (fun j => word nonContracting1011 (t + k * n + j)) k ≤ R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ k :=
  spectral_no_uniform_contraction (by decide) nonContracting1011 nonContracting1011_images.2.2.1
    5 (by decide) nonContracting1011_images.2.2.2.1 (by decide) t k R hk hb

end CollatzLab.Morphism

namespace CollatzLab

/-- A second noncontracting exclusion uses only partial repetitions. The initial
10 means the initial-double theorem does not directly apply to this fixed word. -/
theorem no_rational_seed_realizes_nonContracting1011 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.nonContracting1011) := by
  intro hr
  let C := absInt p + q
  have hC : 1 ≤ C := by have := absInt_nonneg p; have := hr.1; dsimp [C]; omega
  have hC5 := Family.pow_ge_one hC 5
  apply no_doubly_exponential_bound 4 (by decide) 8192 6561 (216 * C ^ 5) 1
    (by decide) (by decide) (by omega) (by decide)
  intro k
  let S := 4 ^ k
  let r := Morphism.weight (Morphism.word Morphism.nonContracting1011) (2 * S)
  have hS : 1 ≤ S := Nat.pow_pos (by decide)
  have hb := rational_matching_prefix_weight_bound (Morphism.word Morphism.nonContracting1011)
    (2 * S) S (by omega) hr Morphism.nonContracting1011_not_eventually_periodic
    (Morphism.nonContracting1011_partial_return k)
  have hw := Morphism.nonContracting1011_prefix_weight k
  have hexp : 13 * S ≤ (S + r) * 5 + 3 := by dsimp [S, r]; omega
  have hcap : r * 5 ≤ 8 * S + 3 := by dsimp [S, r]; omega
  have hp := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) (S + r)) hb 5
  rw [mul_pow, int_pow_mul, int_pow_mul] at hp
  have hp8 := Int.mul_le_mul_of_nonneg_left hp (show (0 : Int) ≤ 8 by decide)
  have hlo := Family.pow_mono_exp (x := (2 : Int)) (by decide) hexp
  have hhi := Family.pow_mono_exp (x := (3 : Int)) (by decide) hcap
  have hhi' := Int.mul_le_mul_of_nonneg_left hhi (show 0 ≤ C ^ 5 by omega)
  rw [int_pow_add] at hlo hhi'
  have h2 : (8192 : Int) ^ S = (2 : Int) ^ (13 * S) := by rw [← int_pow_mul]; rfl
  have h3 : (6561 : Int) ^ S = (3 : Int) ^ (8 * S) := by rw [← int_pow_mul]; rfl
  have hunit : ∀ n : Nat, (1 : Int) ^ n = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Int.pow_succ, ih]; rfl
  rw [hunit k, Int.mul_one, h2, h3]
  dsimp [C, S, r] at *
  family_ring

theorem no_rational_seed_shifted_nonContracting1011 (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.nonContracting1011) t) :=
  no_rational_seed_shifts_of_exclusion _ (Morphism.parity_binary _)
    no_rational_seed_realizes_nonContracting1011 t p q

theorem no_eventually_shifted_nonContracting1011_signed (s t : Nat) (p q : Int)
    (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.nonContracting1011 (t + j)) :=
  no_eventually_shifted_itinerary_odd_denominator _ (Morphism.parity_binary _)
    no_rational_seed_realizes_nonContracting1011 s t p q ho

end CollatzLab

namespace CollatzLab.NonContractingPartialChecks
open Morphism

def literalStep (xs : List Int) : List Int :=
  xs.flatMap (fun b => if b = 1 then [1, 0, 1, 1] else [1, 1, 1, 1])

def literalIter : Nat → List Int
  | 0 => [1]
  | k + 1 => literalStep (literalIter k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem literal_semantics :
    word nonContracting1011 1 = false ∧
    (List.range 4).map (parityWord nonContracting1011) = literalIter 1 ∧
    (List.range 16).map (parityWord nonContracting1011) = literalIter 2 ∧
    (List.range 64).map (parityWord nonContracting1011) = literalIter 3 ∧
    (List.range 256).map (parityWord nonContracting1011) = literalIter 4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem signed_finite_semantics :
    (List.range 81).map (seedParity 1 475541435535248609609897) = (literalIter 4).take 81 ∧
    numIter 1 475541435535248609609897 81 = 2026003878711805313935167780941 ∧
    (List.range 81).map (seedParity 5 (-40144461553015301362867)) = (literalIter 4).take 81 ∧
    numIter 5 (-40144461553015301362867) 81 = -171032067318510884297708363138 ∧
    (List.range 81).map (seedParity 15 (-120433384659045904088601)) = (literalIter 4).take 81 := by decide

end CollatzLab.NonContractingPartialChecks
