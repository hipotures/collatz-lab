import CollatzLab.RationalSeries

/-! The standalone rational-series bridge extends to every bounded integer alphabet. -/
namespace CollatzLab.RationalSeries

def boundedWindow (v : Nat → Int) (lo : Int) (base start : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => base * boundedWindow v lo base start d + (v (start + d) - lo).toNat

theorem digit_range (x lo : Int) (base : Nat) (hx : lo ≤ x ∧ x < lo + (base : Int)) :
    (x - lo).toNat < base ∧ (((x - lo).toNat : Nat) : Int) = x - lo := by
  have hc : (((x - lo).toNat : Nat) : Int) = x - lo := Int.toNat_of_nonneg (by omega)
  exact ⟨by omega, hc⟩

/-- Positional encoding is injective for any alphabet size, including a singleton. -/
theorem radix_pair_injective (base x y r s : Nat) (hr : r < base) (hs : s < base)
    (he : base * x + r = base * y + s) : x = y ∧ r = s := by
  have hxy : x = y := by
    by_cases hx : x < y
    · have hm := Nat.mul_le_mul_left base (show x + 1 ≤ y by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    · by_cases hy : y < x
      · have hm := Nat.mul_le_mul_left base (show y + 1 ≤ x by omega)
        rw [Nat.mul_add, Nat.mul_one] at hm
        omega
      · omega
  exact ⟨hxy, by rw [hxy] at he; omega⟩

theorem boundedWindow_bound (v : Nat → Int) (lo : Int) (base : Nat) (hb : 1 ≤ base)
    (hv : ∀ n, lo ≤ v n ∧ v n < lo + (base : Int)) (start : Nat) :
    ∀ d, boundedWindow v lo base start d < base ^ d
  | 0 => by simp [boundedWindow]
  | d + 1 => by
    have hi := boundedWindow_bound v lo base hb hv start d
    have hd := (digit_range (v (start + d)) lo base (hv (start + d))).1
    have hm := Nat.mul_le_mul_left base (show boundedWindow v lo base start d + 1 ≤ base ^ d by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    rw [boundedWindow, Nat.pow_succ, Nat.mul_comm (base ^ d) base]
    omega

theorem boundedWindow_injective (v : Nat → Int) (lo : Int) (base : Nat)
    (hv : ∀ n, lo ≤ v n ∧ v n < lo + (base : Int)) (a b : Nat) :
    ∀ d, boundedWindow v lo base a d = boundedWindow v lo base b d →
      ∀ j, j < d → v (a + j) = v (b + j)
  | 0, _, _, hj => by omega
  | d + 1, he, j, hj => by
    have ha := digit_range (v (a + d)) lo base (hv (a + d))
    have hb := digit_range (v (b + d)) lo base (hv (b + d))
    change base * boundedWindow v lo base a d + (v (a + d) - lo).toNat =
      base * boundedWindow v lo base b d + (v (b + d) - lo).toNat at he
    have hp := radix_pair_injective base _ _ _ _ ha.1 hb.1 he
    by_cases hlast : j = d
    · subst j
      have hc := congrArg (fun n : Nat => (n : Int)) hp.2
      omega
    · exact boundedWindow_injective v lo base hv a b d hp.1 j (by omega)

/-- Coefficientwise rationality forces periodicity for every finite integer interval. -/
theorem rational_interval_eventually_periodic (v : Nat → Int) (lo : Int) (base : Nat) (hb : 1 ≤ base)
    (hv : ∀ n, lo ≤ v n ∧ v n < lo + (base : Int)) (P : PolynomialPair)
    (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0)
    (hres : ∀ n, P.residual v n = 0) : EventuallyPeriodic v := by
  rcases first_nonzero_coefficient P.p1 P.degree hp with ⟨s, hs, hps, hbefore⟩
  apply deterministic_window_periodic v (P.degree + 1) P.degree (base ^ P.degree)
    (fun n => boundedWindow v lo base n P.degree)
  · intro n
    change boundedWindow v lo base n P.degree ≤ base ^ P.degree
    have := boundedWindow_bound v lo base hb hv n P.degree
    omega
  · intro a b he
    exact boundedWindow_injective v lo base hv a b P.degree he
  · intro a b ha hb he
    exact recurrence_determines P v s hs hps hbefore hres a b ha hb he

/-- No binary or automatic hypothesis is needed for the standalone algebraic bridge. -/
theorem rational_bounded_integer_eventually_periodic (v : Nat → Int)
    (hbounded : ∃ lo hi : Int, ∀ n, lo ≤ v n ∧ v n ≤ hi) (P : PolynomialPair)
    (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0)
    (hres : ∀ n, P.residual v n = 0) : EventuallyPeriodic v := by
  rcases hbounded with ⟨lo, hi, hv⟩
  have hinterval : 0 < hi - lo + 1 := by have := hv 0; omega
  let base := (hi - lo + 1).toNat
  have hcast : (base : Int) = hi - lo + 1 := Int.toNat_of_nonneg (by omega)
  have hb : 1 ≤ base := by omega
  apply rational_interval_eventually_periodic v lo base hb (by
    intro n
    have hh := hv n
    omega) P hp hres

/-- The corresponding nonzero-residual result is also uniform over all bounded alphabets. -/
theorem bounded_nonzero_residual (v : Nat → Int)
    (hbounded : ∃ lo hi : Int, ∀ n, lo ≤ v n ∧ v n ≤ hi) (haper : ¬ EventuallyPeriodic v)
    (P : PolynomialPair) (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) :
    ∃ n, P.residual v n ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro hn
  have hz : ∀ n, P.residual v n = 0 := by
    intro n
    by_cases h : P.residual v n = 0
    · exact h
    · exact False.elim (hn ⟨n, h⟩)
  exact haper (rational_bounded_integer_eventually_periodic v hbounded P hp hz)

/-- Coefficients of `1-z^p`, with `p` required positive in the following theorems. -/
def periodCoefficients (p j : Nat) : Int := if j = 0 then 1 else if j = p then -1 else 0

theorem convolution_period_denominator (v : Nat → Int) (p : Nat) (hp : 1 ≤ p) :
    ∀ d n, PolynomialPair.convolution (periodCoefficients p) v (d + 1) n =
      v n - if p < d + 1 then PolynomialPair.shift v p n else 0
  | 0, n => by
    simp [PolynomialPair.convolution, periodCoefficients, PolynomialPair.shift, show ¬ p < 1 by omega]
  | d + 1, n => by
    rw [PolynomialPair.convolution, convolution_period_denominator v p hp d n]
    simp only [periodCoefficients, show ¬ d + 1 = 0 by omega, if_false]
    by_cases he : d + 1 = p
    · rw [if_pos he, he, if_neg (by omega : ¬ p < p), if_pos (by omega : p < p + 1)]
      omega
    · rw [if_neg he, Int.zero_mul, Int.add_zero]
      by_cases hlt : p < d + 1
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- The converse is algebraic for every integer sequence, without boundedness as a separate premise. -/
theorem eventually_periodic_rational_pair (v : Nat → Int) (hper : EventuallyPeriodic v) :
    ∃ P : PolynomialPair, (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧
      (∀ n, P.residual v n = 0) := by
  rcases hper with ⟨start, p, hp, hperiod⟩
  let d := start + p
  let P : PolynomialPair := ⟨d,
    fun n => -PolynomialPair.convolution (periodCoefficients p) v (d + 1) n,
    periodCoefficients p⟩
  refine ⟨P, ⟨0, by change 0 ≤ d; omega, ?_⟩, ?_⟩
  · change periodCoefficients p 0 ≠ 0
    simp [periodCoefficients]
  · intro n
    by_cases hn : n ≤ d
    · change PolynomialPair.cutoff d
        (fun n => -PolynomialPair.convolution (periodCoefficients p) v (d + 1) n) n +
          PolynomialPair.convolution (periodCoefficients p) v (d + 1) n = 0
      rw [PolynomialPair.cutoff, if_pos hn]
      omega
    · have hpn : ¬ n < p := by dsimp [d] at hn; omega
      have hper := hperiod (n - p) (by dsimp [d] at hn; omega)
      rw [show n - p + p = n by omega] at hper
      change PolynomialPair.cutoff d
        (fun n => -PolynomialPair.convolution (periodCoefficients p) v (d + 1) n) n +
          PolynomialPair.convolution (periodCoefficients p) v (d + 1) n = 0
      rw [PolynomialPair.cutoff, if_neg hn, Int.zero_add,
        convolution_period_denominator v p hp d n, if_pos (by dsimp [d]; omega),
        PolynomialPair.shift, if_neg hpn, hper]
      omega

/-- Exact characterization for bounded integer coefficient sequences. -/
theorem bounded_rational_iff_periodic (v : Nat → Int)
    (hbounded : ∃ lo hi : Int, ∀ n, lo ≤ v n ∧ v n ≤ hi) :
    (∃ P : PolynomialPair, (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧
      (∀ n, P.residual v n = 0)) ↔ EventuallyPeriodic v := by
  constructor
  · rintro ⟨P, hp, hz⟩
    exact rational_bounded_integer_eventually_periodic v hbounded P hp hz
  · intro hp
    exact eventually_periodic_rational_pair v hp

end CollatzLab.RationalSeries
