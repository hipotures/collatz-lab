import CollatzLab.SpectralThreshold
import CollatzLab.RepeatedPrefix

/-! Literal Phase 12 candidate and structural bounds; no originality claim. -/
namespace CollatzLab.Morphism

def frontierSix : Images 6 where
  zero := fun j => decide (j.val < 5)
  one := fun j => decide (j.val = 0 ∨ 3 ≤ j.val)

theorem frontierSix_images :
    List.ofFn frontierSix.one = [true, false, false, true, true, true] ∧
    List.ofFn frontierSix.zero = [true, true, true, true, true, false] ∧
    image frontierSix true 0 = true ∧
    weight (image frontierSix true) 6 = 4 ∧
    weight (image frontierSix false) 6 = 5 ∧
    frequencyDen frontierSix = 7 ∧ weightDelta frontierSix = -1 := by decide

theorem frontierSix_columns (n : Nat) :
    parityWord frontierSix (6 * n) = 1 ∧
    parityWord frontierSix (6 * n + 1) = 1 - parityWord frontierSix n ∧
    parityWord frontierSix (6 * n + 2) = 1 - parityWord frontierSix n ∧
    parityWord frontierSix (6 * n + 3) = 1 ∧
    parityWord frontierSix (6 * n + 4) = 1 ∧
    parityWord frontierSix (6 * n + 5) = parityWord frontierSix n := by
  have h := word_block (by decide) frontierSix frontierSix_images.2.2.1 n
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  change word frontierSix (6 * n) = _ at h0
  simp only [parityWord, h0, h1, h2, h3, h4, h5]
  cases word frontierSix n <;> decide

theorem frontierSix_both_letters :
    word frontierSix 0 = true ∧ word frontierSix 1 = false := by decide

/-- All five nonzero residues contradict a zero at column 1 or 2; residue
zero descends through the identity last column. This is a word-only proof. -/
theorem frontierSix_not_periodic_from (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → parityWord frontierSix (n + p) = parityWord frontierSix n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    let d := p / 6
    have hz1 : parityWord frontierSix (6 * (6 * start) + 1) = 0 := by
      rw [(frontierSix_columns _).2.1, (frontierSix_columns _).1]; decide
    have hz2 : parityWord frontierSix (6 * (6 * start) + 2) = 0 := by
      rw [(frontierSix_columns _).2.2.1, (frontierSix_columns _).1]; decide
    rcases (show p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨
        p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 by omega) with h0 | h1 | h2 | h3 | h4 | h5
    · apply ih d (by dsimp [d]; omega) start (by dsimp [d]; omega)
      intro n hn
      have hh := hper (6 * n + 5) (by omega)
      rw [show 6 * n + 5 + p = 6 * (n + d) + 5 by dsimp [d]; omega,
        (frontierSix_columns _).2.2.2.2.2, (frontierSix_columns _).2.2.2.2.2] at hh
      exact hh
    · have hh := hper (6 * (6 * start) + 2) (by omega)
      rw [hz2, show 6 * (6 * start) + 2 + p = 6 * (6 * start + d) + 3 by dsimp [d]; omega,
        (frontierSix_columns _).2.2.2.1] at hh
      omega
    · have hh := hper (6 * (6 * start) + 1) (by omega)
      rw [hz1, show 6 * (6 * start) + 1 + p = 6 * (6 * start + d) + 3 by dsimp [d]; omega,
        (frontierSix_columns _).2.2.2.1] at hh
      omega
    · have hh := hper (6 * (6 * start) + 1) (by omega)
      rw [hz1, show 6 * (6 * start) + 1 + p = 6 * (6 * start + d) + 4 by dsimp [d]; omega,
        (frontierSix_columns _).2.2.2.2.1] at hh
      omega
    · have hh := hper (6 * (6 * start) + 2) (by omega)
      rw [hz2, show 6 * (6 * start) + 2 + p = 6 * (6 * start + d + 1) by dsimp [d]; omega,
        (frontierSix_columns _).1] at hh
      omega
    · have hh := hper (6 * (6 * start) + 1) (by omega)
      rw [hz1, show 6 * (6 * start) + 1 + p = 6 * (6 * start + d + 1) by dsimp [d]; omega,
        (frontierSix_columns _).1] at hh
      omega

theorem frontierSix_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord frontierSix) := by
  rintro ⟨start, p, hp, hper⟩
  exact frontierSix_not_periodic_from p start hp hper

theorem frontierSix_power_count (k a : Nat) :
    7 * (weight (fun j => word frontierSix (6 ^ k * a + j)) (6 ^ k) : Int) =
      5 * (6 ^ k : Nat) + (-1 : Int) ^ k * (7 * bit (word frontierSix a) - 5) := by
  simpa only [frontierSix_images.2.2.2.2.1, frontierSix_images.2.2.2.2.2.1,
    frontierSix_images.2.2.2.2.2.2] using
    power_image_count (by decide) frontierSix frontierSix_images.2.2.1 k a

theorem frontierSix_incidence (x : Int) :
    (x - 1) * (x - 4) - 10 = (x - 6) * (x + 1) := by family_ring

/-- Exact prefix recursion with an explicit short boundary block. -/
theorem frontierSix_prefix_step (n t : Nat) :
    (weight (word frontierSix) (6 * n + t) : Int) =
      5 * (n : Int) - (weight (word frontierSix) n : Int) +
        (weight (fun j => word frontierSix (6 * n + j)) t : Int) := by
  have hh := imageWeightSum_affine frontierSix 0 n
  have hs := weight_source_blocks (by decide) frontierSix frontierSix_images.2.2.1 0 n
  simp only [Nat.mul_zero, Nat.zero_add] at hh hs
  rw [frontierSix_images.2.2.2.2.1, frontierSix_images.2.2.2.2.2.2] at hh
  change (imageWeightSum frontierSix 0 n : Int) =
    5 * (n : Int) + (-1) * (weight (word frontierSix) n : Int) at hh
  rw [weight_segment, Int.natCast_add, hs]
  omega

theorem frontierSix_boundary_discrepancy (n t : Nat) (ht : t < 6) :
    -10 ≤ 7 * (weight (fun j => word frontierSix (6 * n + j)) t : Int) - 5 * (t : Int) ∧
      7 * (weight (fun j => word frontierSix (6 * n + j)) t : Int) - 5 * (t : Int) ≤ 10 := by
  have he : ∀ j, j < t → word frontierSix (6 * n + j) = image frontierSix (word frontierSix n) j :=
    fun j hj => word_block (by decide) frontierSix frontierSix_images.2.2.1 n j (by omega)
  rw [(common_prefix _ _ t he).1]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases word frontierSix n <;> decide

/-- An effective estimate for every prefix, not just complete power images.
The real-frequency interpretation 5/7 is a separate elementary deduction. -/
theorem frontierSix_prefix_discrepancy : ∀ k n : Nat, n < 6 ^ k →
    -10 * (k : Int) ≤ 7 * (weight (word frontierSix) n : Int) - 5 * (n : Int) ∧
      7 * (weight (word frontierSix) n : Int) - 5 * (n : Int) ≤ 10 * (k : Int)
  | 0, n, hn => by
    have hn0 : n = 0 := by simpa using (show n ≤ 0 by simpa using hn)
    subst n; decide
  | k + 1, n, hn => by
    have hi := frontierSix_prefix_discrepancy k (n / 6) (by rw [Nat.pow_succ] at hn; omega)
    have hs := frontierSix_prefix_step (n / 6) (n % 6)
    have hb := frontierSix_boundary_discrepancy (n / 6) (n % 6) (by omega)
    rw [show 6 * (n / 6) + n % 6 = n by omega] at hs
    omega

/-- Reuse the full iff, retaining every shift and every positive chunk size. -/
theorem frontierSix_no_uniform_contraction :
    ¬ ∃ t k R : Nat, 1 ≤ k ∧
      (∀ n, weight (fun j => word frontierSix (t + k * n + j)) k ≤ R) ∧
      (3 : Int) ^ R < (2 : Int) ^ k := by
  intro h
  have hh := (uniform_contraction_iff_subcritical (by decide) frontierSix
    frontierSix_images.2.2.1 7 (by decide) frontierSix_images.2.2.2.2.2.1).1 h
  have hw : weight (image frontierSix false) 6 = 5 := by decide
  rw [hw] at hh
  have hg : ¬ (3 : Int) ^ 5 < (2 : Int) ^ 7 := by decide
  exact hg hh

/-- A global limitation of the Phase 11 single-return weight ledger, obtained
from the six exact columns, rather than extrapolated from a bounded scan. -/
theorem frontierSix_return_bound (m : Nat) : ∀ ell, 1 ≤ m →
    (∀ j, j < ell → parityWord frontierSix (m + j) = parityWord frontierSix j) →
    5 * ell + 1 ≤ 2 * m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro ell hm hmatch
    have hw0 : parityWord frontierSix 0 = 1 := by decide
    have hw1 : parityWord frontierSix 1 = 0 := by decide
    have hw2 : parityWord frontierSix 2 = 0 := by decide
    by_cases hsmall : m < 6
    · rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 by omega) with
        rfl | rfl | rfl | rfl | rfl
      · by_cases h : ell = 0
        · omega
        · have hh := hmatch 0 (by omega); simp only [Nat.add_zero, hw1, hw0] at hh
          contradiction
      · by_cases h : ell = 0
        · omega
        · have hh := hmatch 0 (by omega); simp only [Nat.add_zero, hw2, hw0] at hh
          contradiction
      all_goals
        by_cases h : ell ≤ 1
        · omega
        · have hh := hmatch 1 (by omega)
          have hval : parityWord frontierSix (3 + 1) = 1 ∧
              parityWord frontierSix (4 + 1) = 1 ∧ parityWord frontierSix (5 + 1) = 1 := by decide
          simp only [hval.1, hval.2.1, hval.2.2, hw1] at hh
          contradiction
    by_cases hshort : ell ≤ 2
    · omega
    rcases (show m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨
        m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 by omega) with h0 | h1 | h2 | h3 | h4 | h5
    · let d := m / 6
      let t := (ell + 4) / 6
      have hp : ∀ j, j < t → parityWord frontierSix (d + j) = parityWord frontierSix j := by
        intro j hj
        have hh := hmatch (6 * j + 1) (by dsimp [t] at hj; omega)
        rw [show m + (6 * j + 1) = 6 * (d + j) + 1 by dsimp [d]; omega,
          (frontierSix_columns _).2.1, (frontierSix_columns _).2.1] at hh
        omega
      have hi := ih d (by dsimp [d]; omega) t (by dsimp [d]; omega) hp
      dsimp [d, t] at hi
      omega
    · have ha := hmatch 0 (by omega)
      have hb := hmatch 1 (by omega)
      rw [show m + 0 = 6 * (m / 6) + 1 by omega, (frontierSix_columns _).2.1, hw0] at ha
      rw [show m + 1 = 6 * (m / 6) + 2 by omega, (frontierSix_columns _).2.2.1, hw1] at hb
      omega
    · have hh := hmatch 1 (by omega)
      rw [show m + 1 = 6 * (m / 6) + 3 by omega, (frontierSix_columns _).2.2.2.1, hw1] at hh
      omega
    · have hh := hmatch 1 (by omega)
      rw [show m + 1 = 6 * (m / 6) + 4 by omega, (frontierSix_columns _).2.2.2.2.1, hw1] at hh
      omega
    · have hh := hmatch 2 (by omega)
      rw [show m + 2 = 6 * (m / 6 + 1) by omega, (frontierSix_columns _).1, hw2] at hh
      omega
    · have hh := hmatch 1 (by omega)
      rw [show m + 1 = 6 * (m / 6 + 1) by omega, (frontierSix_columns _).1, hw1] at hh
      omega

/-- Initial 10 alone would not establish this global absence of squares. -/
theorem frontierSix_no_square_prefix (m : Nat) (hm : 1 ≤ m) :
    ¬ (∀ j, j < m → parityWord frontierSix (m + j) = parityWord frontierSix j) := by
  intro h
  have := frontierSix_return_bound m m hm h
  omega

end CollatzLab.Morphism
