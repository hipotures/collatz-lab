import CollatzLab.MorphismWord

/-! Aperiodicity from two forced ternary columns and an injective middle column. -/
namespace CollatzLab

theorem ternary_columns_not_periodic_from (v : Nat → Int) (f : Int → Int)
    (hf : ∀ a b, f a = f b → a = b)
    (hfirst : ∀ n, v (3 * n) = 1) (hmiddle : ∀ n, v (3 * n + 1) = f (v n))
    (hlast : ∀ n, v (3 * n + 2) = 0) (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → v (n + p) = v n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    rcases (show p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 by omega) with h0 | h1 | h2
    · let d := p / 3
      apply ih d (by dsimp [d]; omega) start (by dsimp [d]; omega)
      intro n hn
      have hh := hper (3 * n + 1) (by omega)
      rw [show 3 * n + 1 + p = 3 * (n + d) + 1 by dsimp [d]; omega,
        hmiddle, hmiddle] at hh
      exact hf _ _ hh
    · have hh := hper (3 * start + 2) (by omega)
      rw [show 3 * start + 2 + p = 3 * (start + p / 3 + 1) by omega,
        hfirst, hlast] at hh
      omega
    · have hh := hper (3 * start) (by omega)
      rw [show 3 * start + p = 3 * (start + p / 3) + 2 by omega,
        hlast, hfirst] at hh
      omega

theorem ternary_columns_not_eventually_periodic (v : Nat → Int) (f : Int → Int)
    (hf : ∀ a b, f a = f b → a = b)
    (hfirst : ∀ n, v (3 * n) = 1) (hmiddle : ∀ n, v (3 * n + 1) = f (v n))
    (hlast : ∀ n, v (3 * n + 2) = 0) : ¬ EventuallyPeriodic v := by
  rintro ⟨start, p, hp, hper⟩
  exact ternary_columns_not_periodic_from v f hf hfirst hmiddle hlast p start hp hper

/-- Forced endpoints and complement middle columns exclude eventual periods
at every length at least three, without a primality assumption on the length. -/
theorem complement_columns_not_periodic_from (L : Nat) (hL : 3 ≤ L) (v : Nat → Int)
    (hfirst : ∀ n, v (L * n) = 1)
    (hmiddle : ∀ n j, 1 ≤ j → j < L - 1 → v (L * n + j) = 1 - v n)
    (hlast : ∀ n, v (L * n + (L - 1)) = 0) (p : Nat) : ∀ start, 1 ≤ p →
    (∀ n, start ≤ n → v (n + p) = v n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    let d := p / L
    let r := p % L
    have hr : r < L := Nat.mod_lt p (by omega)
    have hd : L * d + r = p := by dsimp [d, r]; have := Nat.mod_add_div p L; omega
    have hmul : ∀ n, n ≤ L * n := by
      intro n
      have hh := Nat.mul_le_mul_right n (show 1 ≤ L by omega)
      simpa using hh
    by_cases hz : r = 0
    · have hdiv : L ∣ p := Nat.dvd_of_mod_eq_zero hz
      have hdp : 1 ≤ d := Nat.div_pos (Nat.le_of_dvd hp hdiv) (by omega)
      apply ih d (Nat.div_lt_self hp (by omega)) start hdp
      intro n hn
      have hh := hper (L * n + 1) (by have := hmul n; omega)
      rw [show L * n + 1 + p = L * (n + d) + 1 by rw [Nat.mul_add]; omega,
        hmiddle _ 1 (by decide) (by omega), hmiddle _ 1 (by decide) (by omega)] at hh
      omega
    · by_cases hm : r < L - 1
      · let n := L * start + (L - 1) * d
        have hs : start ≤ n := by have := hmul start; dsimp [n]; omega
        have he : n + d = L * (start + d) := by
          have hh : (L - 1) * d + d = L * d := by
            rw [← Nat.succ_mul, show (L - 1).succ = L by omega]
          dsimp [n]
          rw [Nat.mul_add]
          omega
        have hh := hper (L * n) (by have := hmul n; omega)
        rw [show L * n + p = L * (n + d) + r by have := Nat.mul_add L n d; omega,
          hmiddle _ r (by omega) hm, hfirst, he, hfirst] at hh
        omega
      · have he : r = L - 1 := by omega
        have hh := hper (L * start) (hmul start)
        rw [show L * start + p = L * (start + d) + (L - 1) by
          rw [Nat.mul_add]; omega, hlast, hfirst] at hh
        omega

theorem complement_columns_not_eventually_periodic (L : Nat) (hL : 3 ≤ L) (v : Nat → Int)
    (hfirst : ∀ n, v (L * n) = 1)
    (hmiddle : ∀ n j, 1 ≤ j → j < L - 1 → v (L * n + j) = 1 - v n)
    (hlast : ∀ n, v (L * n + (L - 1)) = 0) : ¬ EventuallyPeriodic v := by
  rintro ⟨start, p, hp, hper⟩
  exact complement_columns_not_periodic_from L hL v hfirst hmiddle hlast p start hp hper

end CollatzLab
