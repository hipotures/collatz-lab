import CollatzLab.Subcritical

/-! Excluding the `1 -> 10, 0 -> 01` word by contracting rational dynamics. -/
namespace CollatzLab

namespace Morphism

theorem thueMorse_even (n : Nat) :
    parityWord thueMorse (2 * n) = parityWord thueMorse n := by
  have hh := word_block (by decide) thueMorse thueMorse_admissible.1 n 0 (by decide)
  simp only [Nat.add_zero] at hh
  unfold parityWord
  rw [hh]
  cases word thueMorse n <;> rfl

theorem thueMorse_odd (n : Nat) :
    parityWord thueMorse (2 * n + 1) = 1 - parityWord thueMorse n := by
  have hh := word_block (by decide) thueMorse thueMorse_admissible.1 n 1 (by decide)
  unfold parityWord
  rw [hh]
  cases word thueMorse n <;> rfl

theorem thueMorse_not_periodic_from (p : Nat) : ∀ M : Nat, 1 ≤ p →
    (∀ n, M ≤ n → parityWord thueMorse (n + p) = parityWord thueMorse n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro M hp hper
    by_cases he : p % 2 = 0
    · let d := p / 2
      have hd : d < p := by dsimp [d]; omega
      have hpos : 1 ≤ d := by dsimp [d]; omega
      apply ih d hd M hpos
      intro n hn
      have hh := hper (2 * n) (by omega)
      rw [show 2 * n + p = 2 * (n + d) by dsimp [d]; omega,
        thueMorse_even, thueMorse_even] at hh
      exact hh
    · let d := p / 2
      let n := 2 * M + d
      have hp' : p = 2 * d + 1 := by dsimp [d]; omega
      have h0 := hper (2 * n) (by dsimp [n]; omega)
      have h1 := hper (2 * n + 1) (by dsimp [n]; omega)
      rw [show 2 * n + p = 2 * (n + d) + 1 by omega,
        thueMorse_odd, thueMorse_even] at h0
      rw [show 2 * n + 1 + p = 2 * (n + d + 1) by omega,
        thueMorse_even, thueMorse_odd] at h1
      have hh : parityWord thueMorse (n + d + 1) = parityWord thueMorse (n + d) := by omega
      rw [show n + d = 2 * (M + d) by dsimp [n]; omega,
        thueMorse_odd, thueMorse_even] at hh
      omega

theorem thueMorse_not_eventually_periodic : ¬ EventuallyPeriodic (parityWord thueMorse) := by
  rintro ⟨M, p, hp, hper⟩
  exact thueMorse_not_periodic_from p M hp hper

theorem thueMorse_prefix :
    (List.range 16).map (parityWord thueMorse) =
      [1,0,0,1,0,1,1,0,0,1,1,0,1,0,0,1] := by decide

set_option maxRecDepth 100000 in
theorem thueMorse_positive_prefix :
    (List.range 32).map (seedParity 1 1895344877) =
      (List.range 32).map (parityWord thueMorse) ∧
    tIterInt 1895344877 32 = 18996277 := by decide

end Morphism

/-- Failure of (C) does not obstruct this separate contraction argument. -/
theorem no_rational_seed_realizes_thueMorse (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord Morphism.thueMorse) :=
  Morphism.no_rational_seed_subcritical (by decide) Morphism.thueMorse
    Morphism.thueMorse_admissible.1 Morphism.thueMorse_admissible.2.1
    (by decide) Morphism.thueMorse_not_eventually_periodic p q

theorem no_rational_seed_realizes_shifted_thueMorse :
    ∀ (t : Nat) (p q : Int),
      ¬ RealizesWord p q (shiftWord (Morphism.parityWord Morphism.thueMorse) t)
  | 0, p, q, hr => by
    apply no_rational_seed_realizes_thueMorse p q
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro j
    simpa [shiftWord] using hr.2.2 j
  | t + 1, p, q, hr =>
    no_rational_seed_realizes_shifted_thueMorse t
      (invBranchNum (Morphism.parityWord Morphism.thueMorse t) p q)
      (invBranchDen (Morphism.parityWord Morphism.thueMorse t) q)
      (realizes_shiftWord_pred (Morphism.parity_binary Morphism.thueMorse t) hr)

theorem no_eventually_shifted_thueMorse_itinerary (s t : Nat) (p q : Int)
    (hq : 0 < q) (ho : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = Morphism.parityWord Morphism.thueMorse (t + j)) := by
  intro ht
  apply no_rational_seed_realizes_shifted_thueMorse t (numIter q p s) q
  refine ⟨hq, ho, ?_⟩
  intro j
  rw [← seedParity_add]
  exact ht j

end CollatzLab
