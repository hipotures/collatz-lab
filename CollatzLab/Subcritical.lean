import CollatzLab.VariableContraction

/-! Bounded rational dynamics under a uniformly contracting block multiplier. -/
namespace CollatzLab

/-- A bounded natural sequence takes a value twice. -/
theorem bounded_nat_collision : ∀ K : Nat, ∀ f : Nat → Nat,
    (∀ n, f n ≤ K) → ∃ i j, i < j ∧ f i = f j
  | 0, f, hf => ⟨0, 1, by omega, by have := hf 0; have := hf 1; omega⟩
  | K + 1, f, hf => by
    classical
    by_cases hh : ∃ i, f i = K + 1
    · rcases hh with ⟨i, hi⟩
      by_cases hn : ∃ n, f (i + n + 1) = K + 1
      · rcases hn with ⟨n, hn⟩
        exact ⟨i, i + n + 1, by omega, hi.trans hn.symm⟩
      · have ht : ∀ n, f (i + n + 1) ≤ K := by
          intro n
          have := hf (i + n + 1)
          by_cases he : f (i + n + 1) = K + 1
          · exact False.elim (hn ⟨n, he⟩)
          · omega
        rcases bounded_nat_collision K (fun n => f (i + n + 1)) ht with ⟨a, b, hab, he⟩
        exact ⟨i + a + 1, i + b + 1, by omega, he⟩
    · have ht : ∀ n, f n ≤ K := by
        intro n
        have := hf n
        by_cases he : f n = K + 1
        · exact False.elim (hh ⟨n, he⟩)
        · omega
      exact bounded_nat_collision K f ht

theorem repeated_numIter_periodic (q p : Int) (s t : Nat) (hst : s < t)
    (he : numIter q p s = numIter q p t) : EventuallyPeriodic (seedParity q p) := by
  have hi : ∀ k, numIter q p (s + k) = numIter q p (t + k) := by
    intro k
    induction k with
    | zero => simpa using he
    | succ k ih =>
      change numStep q (numIter q p (s + k)) = numStep q (numIter q p (t + k))
      rw [ih]
  refine ⟨s, t - s, by omega, ?_⟩
  intro m hm
  have hh := hi (m - s)
  rw [show s + (m - s) = m by omega, show t + (m - s) = m + (t - s) by omega] at hh
  exact congrArg (fun x : Int => x % 2) hh.symm

/-- Only block-boundary states need to be bounded. No density conjecture is used. -/
theorem bounded_blocks_periodic (L : Nat) (hL : 1 ≤ L) (p q K : Int) (hK : 0 ≤ K)
    (hb : ∀ n, -K ≤ numIter q p (L * n) ∧ numIter q p (L * n) ≤ K) :
    EventuallyPeriodic (seedParity q p) := by
  let f := fun n => (numIter q p (L * n) + K).toNat
  have hf : ∀ n, f n ≤ (2 * K).toNat := by
    intro n
    have hh := hb n
    have h0 : 0 ≤ numIter q p (L * n) + K := by omega
    have h1 : (f n : Int) = numIter q p (L * n) + K := Int.toNat_of_nonneg h0
    have h2 : (((2 * K).toNat : Nat) : Int) = 2 * K := Int.toNat_of_nonneg (by omega)
    omega
  rcases bounded_nat_collision (2 * K).toNat f hf with ⟨i, j, hij, he⟩
  have hi : (f i : Int) = numIter q p (L * i) + K := Int.toNat_of_nonneg (by have := hb i; omega)
  have hj : (f j : Int) = numIter q p (L * j) + K := Int.toNat_of_nonneg (by have := hb j; omega)
  have heq : numIter q p (L * i) = numIter q p (L * j) := by
    have hh := congrArg (fun n : Nat => (n : Int)) he
    omega
  exact repeated_numIter_periodic q p (L * i) (L * j)
    (Nat.mul_lt_mul_of_pos_left hij (by omega)) heq

/-- An integer recurrence with bounded forcing and `0<=B<A` stays bounded. -/
theorem contracting_recurrence_bounded (A B C : Int) (hB : 0 ≤ B) (hBA : B < A)
    (hC : 0 ≤ C) (y d : Nat → Int) (hd : ∀ n, -C ≤ d n ∧ d n ≤ C)
    (hr : ∀ n, A * y (n + 1) = B * y n + d n) :
    ∀ n, -(absInt (y 0) + C) ≤ y n ∧ y n ≤ absInt (y 0) + C :=
  variable_contracting_recurrence_bounded A B C hBA hC (fun _ => B) y d
    (fun _ => ⟨hB, Int.le_refl _⟩) hd hr

namespace Morphism

theorem offset_nonneg (v : Nat → Bool) : ∀ n, 0 ≤ offset v n
  | 0 => Int.le_refl _
  | n + 1 => by
    have hi := offset_nonneg v n
    have hp := pow_nonneg_of_nonneg (x := 2) (by decide) n
    rw [offset]
    split <;> omega

/-- A separate sufficient condition: subcritical equal-weight blocks and aperiodicity. -/
theorem no_rational_seed_subcritical {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hBA : B M < A L) (haper : ¬ EventuallyPeriodic (parityWord M)) (p q : Int) :
    ¬ RealizesWord p q (parityWord M) := by
  intro hr
  have hq := hr.1
  let y := fun n => numIter q p (L * n)
  let d := fun n => (c M false + (c M true - c M false) * parityWord M n) * q
  let C := (c M false + c M true) * q
  have hc0 : 0 ≤ c M false := offset_nonneg _ _
  have hc1 : 0 ≤ c M true := offset_nonneg _ _
  have h0q := Int.mul_nonneg hc0 (show 0 ≤ q by omega)
  have h1q := Int.mul_nonneg hc1 (show 0 ≤ q by omega)
  have hC : 0 ≤ C := by dsimp [C]; rw [Int.add_mul]; omega
  have hd : ∀ n, -C ≤ d n ∧ d n ≤ C := by
    intro n
    dsimp [C, d, parityWord, bit]
    cases word M n <;> simp only [Bool.false_eq_true, if_false, if_true, Int.mul_zero,
      Int.add_zero, Int.mul_one]
    all_goals constructor <;> family_ring
  have hb := contracting_recurrence_bounded (A L) (B M) C
    (pow_nonneg_of_nonneg (x := 3) (by decide) _) hBA hC y d hd
    (fun n => numIter_block hL M h1 hw hr n)
  have hK : 0 ≤ absInt (y 0) + C := by have := absInt_nonneg (y 0); omega
  have hper := bounded_blocks_periodic L (by omega) p q (absInt (y 0) + C) hK hb
  have he : seedParity q p = parityWord M := funext hr.2.2
  rw [he] at hper
  exact haper hper

end Morphism
end CollatzLab
