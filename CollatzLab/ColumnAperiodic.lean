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

end CollatzLab
