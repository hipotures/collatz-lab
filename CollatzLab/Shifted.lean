import CollatzLab.Pade

/-!
# Shifted Parity Words and Backward Preimage Closure (Section 7.2)

This module formalizes Section 7.2 of the paper:
* The shifted parity words `w^{(t)}(n) = w(t + n)` (`shiftWord w t`).
* **Lemma 7.2 (`invBranch_realizes`, `realizes_shiftWord_pred`)**:
  The inverse parity branches `T_0^{-1}(z) = 2z` and `T_1^{-1}(z) = (2z - 1)/3`
  map any rational 2-adic seed `(p, q)` (`q > 0` odd) realizing a word `v` to a
  rational 2-adic seed `(p', q')` (`q' > 0` odd) realizing `b · v` for `b ∈ {0, 1}`.
  In particular, if `(p, q)` realizes `w^{(t+1)}`, then `(p', q')` realizes `w^{(t)}`.
* **Corollary 7.3 (`no_rational_seed_realizes_shifted_w`)**:
  For every shift `t ≥ 0` and every `p, q ∈ ℤ` with `q > 0` odd, no rational 2-adic
  seed `x = p / q` realizes the shifted parity word `w^{(t)}`. Consequently, no
  rational 2-adic trajectory or integer Collatz trajectory can ever enter `w^{(t)}`
  after any finite number of steps `s ≥ 0` (`no_eventually_shifted_w_itinerary`).
-/

namespace CollatzLab

/--
  The `t`-shifted word `v^{(t)}(n) = v(t + n)`.
-/
def shiftWord (v : Nat → Int) (t : Nat) (n : Nat) : Int :=
  v (t + n)

@[simp] theorem shiftWord_zero (v : Nat → Int) (n : Nat) :
    shiftWord v 0 n = v n := by
  simp [shiftWord]

theorem shiftWord_succ (v : Nat → Int) (t n : Nat) :
    shiftWord v (t + 1) n = shiftWord v t (n + 1) := by
  dsimp [shiftWord]
  have : (t + 1) + n = t + (n + 1) := by omega
  rw [this]

/--
  Numerator of the inverse branch `T_b^{-1}(p / q)` for `b ∈ {0, 1}`:
  * `T_0^{-1}(p / q) = (2 * p) / q`
  * `T_1^{-1}(p / q) = (2 * p - q) / (3 * q)`
-/
def invBranchNum (b p q : Int) : Int :=
  if b = 0 then 2 * p else 2 * p - q

/--
  Denominator of the inverse branch `T_b^{-1}(p / q)` for `b ∈ {0, 1}`:
  * `q' = q` if `b = 0`
  * `q' = 3 * q` if `b = 1`
-/
def invBranchDen (b q : Int) : Int :=
  if b = 0 then q else 3 * q

/-- Shifting `numIter` by one step is equivalent to starting at `numStep q p`. -/
theorem numIter_succ_shift (q p : Int) :
    ∀ j : Nat, numIter q p (j + 1) = numIter q (numStep q p) j
  | 0 => rfl
  | j + 1 => by
    change numStep q (numIter q p (j + 1)) = numStep q (numIter q (numStep q p) j)
    rw [numIter_succ_shift q p j]

/-- Shifting `numIter` by `s` steps is equivalent to starting at `numIter q p s`. -/
theorem numIter_add (q p : Int) (s : Nat) :
    ∀ j : Nat, numIter q p (s + j) = numIter q (numIter q p s) j
  | 0 => by
    have : s + 0 = s := by omega
    rw [this]
    rfl
  | j + 1 => by
    have : s + (j + 1) = (s + j) + 1 := by omega
    rw [this]
    dsimp [numIter]
    rw [numIter_add q p s j]

/-- Shifting `seedParity` by one step is `seedParity` of `numStep q p`. -/
theorem seedParity_succ_shift (q p : Int) (j : Nat) :
    seedParity q p (j + 1) = seedParity q (numStep q p) j := by
  unfold seedParity
  rw [numIter_succ_shift]

/-- Shifting `seedParity` by `s` steps is `seedParity` of `numIter q p s`. -/
theorem seedParity_add (q p : Int) (s j : Nat) :
    seedParity q p (s + j) = seedParity q (numIter q p s) j := by
  unfold seedParity
  rw [numIter_add]

/--
  Core arithmetic properties of the inverse branch `(p', q') = (invBranchNum b p q, invBranchDen b q)`
  for `b ∈ {0, 1}` and `q > 0` odd (Lemma 7.2):
  1. `q' > 0`
  2. `q' % 2 = 1`
  3. `seedParity q' p' 0 = b`
  4. `(numStep q' p') * q = p * q'`
-/
theorem invBranch_step_props {b p q : Int}
    (hb : b = 0 ∨ b = 1) (hq_pos : q > 0) (hq_odd : q % 2 = 1) :
    let p' := invBranchNum b p q
    let q' := invBranchDen b q
    q' > 0 ∧ q' % 2 = 1 ∧ seedParity q' p' 0 = b ∧ (numStep q' p') * q = p * q' := by
  have hq_decomp : q = 2 * (q / 2) + 1 := by omega
  rcases hb with rfl | rfl
  · dsimp [invBranchNum, invBranchDen, seedParity, numIter, numStep]
    have hp_even : (2 * p) % 2 = 0 := by omega
    have hp_div : (2 * p) / 2 = p := by omega
    refine ⟨hq_pos, hq_odd, hp_even, ?_⟩
    rw [if_pos hp_even, hp_div]
  · dsimp [invBranchNum, invBranchDen, seedParity, numIter, numStep]
    have hq'_pos : 3 * q > 0 := by omega
    have hq'_odd : (3 * q) % 2 = 1 := by omega
    have hp'_odd : (2 * p - q) % 2 = 1 := by omega
    have hp'_not_even : ¬ ((2 * p - q) % 2 = 0) := by omega
    refine ⟨hq'_pos, hq'_odd, hp'_odd, ?_⟩
    rw [if_neg hp'_not_even]
    have h_num : (3 * (2 * p - q) + 3 * q) / 2 = 3 * p := by omega
    rw [h_num]
    ac_rfl

/--
  Lemma 7.2 (Backward preimage step for shifted words):
  If `(p, q)` realizes `shiftWord v (t + 1)` and `v t ∈ {0, 1}`, then
  `(invBranchNum (v t) p q, invBranchDen (v t) q)` realizes `shiftWord v t`.
-/
theorem realizes_shiftWord_pred {v : Nat → Int} {t : Nat} {p q : Int}
    (hvt : v t = 0 ∨ v t = 1)
    (hreal : RealizesWord p q (shiftWord v (t + 1))) :
    RealizesWord (invBranchNum (v t) p q) (invBranchDen (v t) q) (shiftWord v t) := by
  rcases hreal with ⟨hq_pos, hq_odd, hpar⟩
  rcases invBranch_step_props hvt hq_pos hq_odd with ⟨hq'_pos, hq'_odd, hpar0, hstep_eq⟩
  refine ⟨hq'_pos, hq'_odd, ?_⟩
  intro j
  cases j with
  | zero => exact hpar0
  | succ m =>
    rw [seedParity_succ_shift]
    have hequiv := (numIter_equiv hq'_odd hq_odd hstep_eq m).2
    rw [hequiv, hpar m, shiftWord_succ]

/--
  Corollary 7.3 (Shifted parity words of `w` have no rational 2-adic realizations):
  For every shift `t ≥ 0` and every `p, q ∈ ℤ` with `q > 0` odd, no rational 2-adic
  seed `x = p / q` realizes the shifted parity word `w^{(t)}(n) = w(t + n)`.
-/
theorem no_rational_seed_realizes_shifted_w :
    ∀ (t : Nat) (p q : Int), ¬ RealizesWord p q (shiftWord w t)
  | 0, p, q, hreal => by
    apply no_rational_seed_realizes_w p q
    rcases hreal with ⟨hq_pos, hq_odd, hpar⟩
    refine ⟨hq_pos, hq_odd, ?_⟩
    intro j
    have hj := hpar j
    rw [shiftWord_zero] at hj
    exact hj
  | t + 1, p, q, hreal => by
    have hpre := realizes_shiftWord_pred (w_binary t) hreal
    exact no_rational_seed_realizes_shifted_w t
      (invBranchNum (w t) p q) (invBranchDen (w t) q) hpre

/--
  No integer `n ∈ ℤ` realizes any shifted word `w^{(t)}`.
-/
theorem no_int_seed_realizes_shifted_w (t : Nat) (n : Int) :
    ¬ RealizesWord n 1 (shiftWord w t) :=
  no_rational_seed_realizes_shifted_w t n 1

/--
  Forward-orbit corollary of Corollary 7.3:
  No rational 2-adic seed `(p, q)` (`q > 0` odd) can have its parity itinerary
  from step `s` onwards match `w` from index `t` onwards (`∀ j, seedParity q p (s + j) = w (t + j)`).
-/
theorem no_eventually_shifted_w_itinerary (s t : Nat) (p q : Int)
    (hq_pos : q > 0) (hq_odd : q % 2 = 1) :
    ¬ (∀ j : Nat, seedParity q p (s + j) = w (t + j)) := by
  intro htail
  apply no_rational_seed_realizes_shifted_w t (numIter q p s) q
  refine ⟨hq_pos, hq_odd, ?_⟩
  intro j
  rw [← seedParity_add q p s j]
  exact htail j

/--
  No integer trajectory under the accelerated Collatz map `T` can ever enter
  any shifted word `w^{(t)}` after `s` steps.
-/
theorem no_int_orbit_enters_shifted_w (s t : Nat) (n : Int) :
    ¬ RealizesWord (tIterInt n s) 1 (shiftWord w t) :=
  no_rational_seed_realizes_shifted_w t (tIterInt n s) 1

end CollatzLab
