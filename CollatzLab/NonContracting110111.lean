import CollatzLab.MorphismBalance
import CollatzLab.ExponentialGap

/-! An aperiodic supercritical word, with exact obstructions to uniform contraction. -/
namespace CollatzLab.Morphism

def nonContracting110111 : Images 3 where
  zero := fun _ => true
  one := fun j => decide (j.val < 2)

theorem nonContracting_images :
    List.ofFn nonContracting110111.one = [true, true, false] ∧
    List.ofFn nonContracting110111.zero = [true, true, true] ∧
    image nonContracting110111 true 0 = true ∧
    weight (image nonContracting110111 true) 3 = 2 ∧
    weight (image nonContracting110111 false) 3 = 3 := by decide

theorem nonContracting_columns (n : Nat) :
    word nonContracting110111 (3 * n) = true ∧
    word nonContracting110111 (3 * n + 1) = true ∧
    word nonContracting110111 (3 * n + 2) = !(word nonContracting110111 n) := by
  have h := word_block (by decide) nonContracting110111 nonContracting_images.2.2.1 n
  constructor
  · simpa [image, nonContracting110111] using h 0 (by decide)
  constructor
  · simpa [image, nonContracting110111] using h 1 (by decide)
  · rw [h 2 (by decide)]
    cases word nonContracting110111 n <;> decide

theorem nonContracting_parity_columns (n : Nat) :
    parityWord nonContracting110111 (3 * n) = 1 ∧
    parityWord nonContracting110111 (3 * n + 1) = 1 ∧
    parityWord nonContracting110111 (3 * n + 2) = 1 - parityWord nonContracting110111 n := by
  have h := nonContracting_columns n
  simp only [parityWord, h.1, h.2.1, h.2.2]
  cases word nonContracting110111 n <;> decide

theorem nonContracting_both_bits :
    word nonContracting110111 0 = true ∧ word nonContracting110111 2 = false := by decide

/-- Unlike opposite-forced-column certificates, this proof uses a forced parent
at the shifted variable column to eliminate each nonzero period residue. -/
theorem nonContracting_not_periodic_from (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → parityWord nonContracting110111 (n + p) =
      parityWord nonContracting110111 n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    let d := p / 3
    rcases (show p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 by omega) with h0 | h1 | h2
    · apply ih d (by dsimp [d]; omega) start (by dsimp [d]; omega)
      intro n hn
      have hh := hper (3 * n + 2) (by omega)
      rw [show 3 * n + 2 + p = 3 * (n + d) + 2 by dsimp [d]; omega,
        (nonContracting_parity_columns _).2.2, (nonContracting_parity_columns _).2.2] at hh
      omega
    · have hh := hper (3 * (3 * start + 2 * d) + 1) (by omega)
      rw [show 3 * (3 * start + 2 * d) + 1 + p = 3 * (3 * (start + d)) + 2 by
        dsimp [d]; omega,
        (nonContracting_parity_columns _).2.2, (nonContracting_parity_columns _).1,
        (nonContracting_parity_columns _).2.1] at hh
      omega
    · have hh := hper (3 * (3 * start + 2 * d)) (by omega)
      rw [show 3 * (3 * start + 2 * d) + p = 3 * (3 * (start + d)) + 2 by
        dsimp [d]; omega,
        (nonContracting_parity_columns _).2.2, (nonContracting_parity_columns _).1,
        (nonContracting_parity_columns _).1] at hh
      omega

theorem nonContracting_not_eventually_periodic :
    ¬ EventuallyPeriodic (parityWord nonContracting110111) := by
  rintro ⟨start, p, hp, hper⟩
  exact nonContracting_not_periodic_from p start hp hper

theorem nonContracting_group_weight (a h : Nat) :
    2 * h ≤ weight (fun j => word nonContracting110111 (3 * a + j)) (3 * h) := by
  rw [weight_source_blocks (by decide) _ nonContracting_images.2.2.1]
  have hh := imageWeightSum_affine nonContracting110111 a h
  have hle := weight_le (fun j => word nonContracting110111 (a + j)) h
  have hp : weightDelta nonContracting110111 = -1 := by decide
  rw [nonContracting_images.2.2.2.2, hp] at hh
  omega

/-- Any three consecutive bits contain the two forced ones, even across images. -/
theorem nonContracting_three_weight (a : Nat) :
    2 ≤ weight (fun j => word nonContracting110111 (a + j)) 3 := by
  rcases (show a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 by omega) with h | h | h
  · have h0 : word nonContracting110111 a = true := by
      rw [show a = 3 * (a / 3) by omega]; exact (nonContracting_columns _).1
    have h1 : word nonContracting110111 (a + 1) = true := by
      rw [show a + 1 = 3 * (a / 3) + 1 by omega]; exact (nonContracting_columns _).2.1
    simp only [weight, Nat.add_zero, h0, h1, if_true]
    split <;> omega
  · have h0 : word nonContracting110111 a = true := by
      rw [show a = 3 * (a / 3) + 1 by omega]; exact (nonContracting_columns _).2.1
    have h2 : word nonContracting110111 (a + 2) = true := by
      rw [show a + 2 = 3 * (a / 3 + 1) by omega]; exact (nonContracting_columns _).1
    simp only [weight, Nat.add_zero, h0, h2, if_true]
    split <;> omega
  · have h1 : word nonContracting110111 (a + 1) = true := by
      rw [show a + 1 = 3 * (a / 3 + 1) by omega]; exact (nonContracting_columns _).1
    have h2 : word nonContracting110111 (a + 2) = true := by
      rw [show a + 2 = 3 * (a / 3 + 1) + 1 by omega]; exact (nonContracting_columns _).2.1
    simp only [weight, Nat.add_zero, h1, h2, if_true]
    split <;> omega

theorem nonContracting_window_lower (a : Nat) : ∀ h,
    2 * h ≤ weight (fun j => word nonContracting110111 (a + j)) (3 * h)
  | 0 => by simp [weight]
  | h + 1 => by
    rw [show 3 * (h + 1) = 3 * h + 3 from Nat.mul_succ 3 h, weight_segment]
    have hi := nonContracting_window_lower a h
    have ht := nonContracting_three_weight (a + 3 * h)
    simpa only [Nat.add_assoc] using (show 2 * (h + 1) ≤
      weight (fun j => word nonContracting110111 (a + j)) (3 * h) +
      weight (fun j => word nonContracting110111 (a + 3 * h + j)) 3 by omega)

/-- Exact expansion for every positive group; the inequality is strictly in the
opposite direction to the Phase 10 sufficient condition. -/
theorem nonContracting_group_expands (h R : Nat) (hh : 1 ≤ h) (hR : 2 * h ≤ R) :
    (2 : Int) ^ (3 * h) < (3 : Int) ^ R := by
  have hs := positive_pow_strict 9 8 (by decide) (by decide) h hh
  have hm := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) hR)
  simp only [Int.natCast_pow] at hm
  have h9 : (9 : Int) ^ h = (3 : Int) ^ (2 * h) := by rw [← int_pow_mul]; rfl
  have h8 : (8 : Int) ^ h = (2 : Int) ^ (3 * h) := by rw [← int_pow_mul]; rfl
  rw [h9, h8] at hs
  exact Int.lt_of_lt_of_le hs hm

/-- No fixed positive chunk length works, even with an arbitrary initial shift. -/
theorem nonContracting_no_uniform_chunks (t k R : Nat) (hk : 1 ≤ k)
    (hw : ∀ n, weight (fun j => word nonContracting110111 (t + k * n + j)) k ≤ R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ k := by
  have hb : ∀ m n, weight (fun j => word nonContracting110111 (t + k * n + j))
      (k * m) ≤ m * R := by
    intro m
    induction m with
    | zero => intro n; simp [weight]
    | succ m ih =>
      intro n
      rw [Nat.mul_succ, weight_segment]
      have he : (fun j => word nonContracting110111 (t + k * n + (k * m + j))) =
          (fun j => word nonContracting110111 (t + k * (n + m) + j)) := by
        funext j; congr 1; rw [Nat.mul_add]; omega
      rw [he, Nat.succ_mul]
      have := ih n
      have := hw (n + m)
      omega
  have hl := nonContracting_window_lower t k
  have hu := hb 3 0
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_comm k 3] at hu
  have hR : 2 * k ≤ 3 * R := by omega
  have hs := nonContracting_group_expands k (3 * R) hk hR
  intro hg
  have hh := positive_pow_strict ((2 : Int) ^ k) ((3 : Int) ^ R)
    (Family.pow_ge_one (by decide) _) hg 3 (by decide)
  rw [int_pow_mul, int_pow_mul, Nat.mul_comm R 3, Nat.mul_comm k 3] at hh
  omega

end CollatzLab.Morphism

namespace CollatzLab.Morphism

/-- Reuse of the Phase 10 balance identity, specialized without a limit argument. -/
theorem nonContracting_power_count (k a : Nat) :
    4 * (weight (fun j => word nonContracting110111 (3 ^ k * a + j)) (3 ^ k) : Int) =
      3 * (3 ^ k : Nat) + (-1 : Int) ^ k *
        (4 * bit (word nonContracting110111 a) - 3) := by
  have hh := balance_power (by decide) nonContracting110111 nonContracting_images.2.2.1 k a 1
  have hD : frequencyDen nonContracting110111 = 4 := by decide
  have hd : weightDelta nonContracting110111 = -1 := by decide
  simp only [Nat.mul_one, balance, hD, hd, nonContracting_images.2.2.2.2] at hh
  have hb : (weight (fun j => word nonContracting110111 (a + j)) 1 : Int) =
      bit (word nonContracting110111 a) := by
    cases hb : word nonContracting110111 a <;> simp [weight, bit, hb]
  rw [hb] at hh
  simp at hh
  omega

/-- Exact recurrence at every prefix length, not only at powers of three. -/
theorem nonContracting_prefix_step (n r : Nat) (hr : r < 3) :
    weight (word nonContracting110111) (3 * n + r) +
      weight (word nonContracting110111) n = 3 * n + r := by
  have hh := imageWeightSum_affine nonContracting110111 0 n
  have hs := weight_source_blocks (by decide) nonContracting110111
    nonContracting_images.2.2.1 0 n
  have hd : weightDelta nonContracting110111 = -1 := by decide
  simp only [Nat.mul_zero, Nat.zero_add] at hh hs
  change weight (word nonContracting110111) (3 * n) = imageWeightSum nonContracting110111 0 n at hs
  rw [nonContracting_images.2.2.2.2, hd] at hh
  change (imageWeightSum nonContracting110111 0 n : Int) = 3 * (n : Int) + (-1) * (weight (word nonContracting110111) n : Int) at hh
  rw [weight_segment]
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  all_goals
    simp only [weight, Nat.add_zero, (nonContracting_columns _).1,
      (nonContracting_columns _).2.1, if_true]
    omega

/-- All prefixes below 3^k have discrepancy at most 2k from frequency 3/4.
Thus this is an explicit integer frequency estimate for every prefix. -/
theorem nonContracting_prefix_discrepancy : ∀ (k n : Nat), n < 3 ^ k →
    -2 * (k : Int) ≤ 4 * (weight (word nonContracting110111) n : Int) - 3 * (n : Int) ∧
    4 * (weight (word nonContracting110111) n : Int) - 3 * (n : Int) ≤ 2 * (k : Int)
  | 0, n, hn => by
    have hz : n = 0 := by simpa using (show n ≤ 0 by simpa using hn)
    subst n
    decide
  | k + 1, n, hn => by
    have hdiv : n / 3 < 3 ^ k := by
      rw [Nat.pow_succ] at hn
      omega
    have hi := nonContracting_prefix_discrepancy k (n / 3) hdiv
    have hs := nonContracting_prefix_step (n / 3) (n % 3) (by omega)
    have he : 3 * (n / 3) + n % 3 = n := by omega
    rw [he] at hs
    omega

end CollatzLab.Morphism
