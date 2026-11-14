import CollatzLab.PolynomialExistence
import CollatzLab.Subcritical

/-! A coefficientwise rational identity forces eventual periodicity of binary symbols. -/
namespace CollatzLab
namespace RationalSeries
open FiniteLinear PolynomialPair

/-- A binary window encoded as a natural number; no finite-set library is needed. -/
def window (v : Nat → Int) (start : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => 2 * window v start d + (v (start + d)).toNat

theorem window_bound (v : Nat → Int) (hv : ∀ n, v n = 0 ∨ v n = 1) (start : Nat) :
    ∀ d, window v start d < 2 ^ d
  | 0 => by simp [window]
  | d + 1 => by
    have hi := window_bound v hv start d
    have hb : (v (start + d)).toNat ≤ 1 := by rcases hv (start + d) with h | h <;> simp [h]
    rw [window, Nat.pow_succ]
    omega

theorem window_injective (v : Nat → Int) (hv : ∀ n, v n = 0 ∨ v n = 1) (a b : Nat) :
    ∀ d, window v a d = window v b d → ∀ j, j < d → v (a + j) = v (b + j)
  | 0, _, _, hj => by omega
  | d + 1, he, j, hj => by
    have ha : 0 ≤ v (a + d) ∧ v (a + d) ≤ 1 := by rcases hv (a + d) with h | h <;> omega
    have hb : 0 ≤ v (b + d) ∧ v (b + d) ≤ 1 := by rcases hv (b + d) with h | h <;> omega
    have hca : (((v (a + d)).toNat : Nat) : Int) = v (a + d) := Int.toNat_of_nonneg ha.1
    have hcb : (((v (b + d)).toNat : Nat) : Int) = v (b + d) := Int.toNat_of_nonneg hb.1
    change 2 * window v a d + (v (a + d)).toNat = 2 * window v b d + (v (b + d)).toNat at he
    have hprev : window v a d = window v b d := by omega
    by_cases hlast : j = d
    · subst j; omega
    · exact window_injective v hv a b d hprev j (by omega)

/-- Equal finite states determine equal next symbols, including the empty-window case. -/
theorem deterministic_binary_periodic (v : Nat → Int) (hv : ∀ n, v n = 0 ∨ v n = 1)
    (start d : Nat)
    (hdet : ∀ a b, start ≤ a → start ≤ b →
      (∀ j, j < d → v (a + j) = v (b + j)) → v (a + d) = v (b + d)) :
    EventuallyPeriodic v := by
  rcases bounded_nat_collision (2 ^ d) (fun n => window v (start + n) d)
    (by intro n; change window v (start + n) d ≤ 2 ^ d; have := window_bound v hv (start + n) d; omega) with ⟨i, j, hij, he⟩
  have hfirst := window_injective v hv (start + i) (start + j) d he
  have hall : ∀ k, v (start + i + k) = v (start + j + k) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      by_cases hk : k < d
      · exact hfirst k hk
      · have hh := hdet (start + i + (k - d)) (start + j + (k - d)) (by omega) (by omega) (by
          intro t ht
          have hi := ih (k - d + t) (by omega)
          simpa [Nat.add_assoc] using hi)
        rw [show start + i + (k - d) + d = start + i + k by omega,
          show start + j + (k - d) + d = start + j + k by omega] at hh
        exact hh
  refine ⟨start + i, j - i, by omega, ?_⟩
  intro n hn
  have hh := hall (n - (start + i))
  rw [show start + i + (n - (start + i)) = n by omega,
    show start + j + (n - (start + i)) = n + (j - i) by omega] at hh
  exact hh.symm

/-- Cancel all matching summands except a designated pivot. -/
theorem total_eq_pivot (f g : Nat → Int) : ∀ n s, s < n →
    total f n = total g n → (∀ j, j < n → j ≠ s → f j = g j) → f s = g s
  | 0, _, hs, _, _ => by omega
  | n + 1, s, hs, he, hother => by
    by_cases hlast : s = n
    · subst s
      have hpre := total_ext f g n (by intro j hj; exact hother j (by omega) (by omega))
      rw [total, total, hpre] at he
      omega
    · have hn := hother n (by omega) (by omega)
      have hepre : total f n = total g n := by rw [total, total, hn] at he; omega
      exact total_eq_pivot f g n s (by omega) hepre (by intro j hj hjs; exact hother j (by omega) hjs)

/-- The least nonzero coefficient exists in every nonzero finite coefficient list. -/
theorem first_nonzero_coefficient (p : Nat → Int) : ∀ d,
    (∃ j, j ≤ d ∧ p j ≠ 0) →
      ∃ s, s ≤ d ∧ p s ≠ 0 ∧ (∀ j, j < s → p j = 0)
  | 0, h => by
    rcases h with ⟨j, hj, hp⟩
    have he : j = 0 := by omega
    subst j
    exact ⟨0, by omega, hp, by intro j hj; omega⟩
  | d + 1, h => by
    by_cases hp : p 0 = 0
    · have ht : ∃ j, j ≤ d ∧ p (j + 1) ≠ 0 := by
        rcases h with ⟨j, hj, hne⟩
        have hjpos : 0 < j := by by_cases hz : j = 0; subst j; contradiction; omega
        exact ⟨j - 1, by omega, by rw [show j - 1 + 1 = j by omega]; exact hne⟩
      rcases first_nonzero_coefficient (fun j => p (j + 1)) d ht with ⟨s, hs, hps, hbefore⟩
      refine ⟨s + 1, by omega, hps, ?_⟩
      intro j hj
      by_cases hz : j = 0
      · subst j; exact hp
      · have hh := hbefore (j - 1) (by omega)
        simpa [show j - 1 + 1 = j by omega] using hh
    · exact ⟨0, by omega, hp, by intro j hj; omega⟩

/-- Initial zero coefficients need no division: isolate the first nonzero one. -/
theorem recurrence_determines (P : PolynomialPair) (v : Nat → Int)
    (s : Nat) (hs : s ≤ P.degree) (hps : P.p1 s ≠ 0)
    (hbefore : ∀ j, j < s → P.p1 j = 0)
    (hres : ∀ n, P.residual v n = 0) (a b : Nat)
    (ha : P.degree + 1 ≤ a) (hb : P.degree + 1 ≤ b)
    (he : ∀ j, j < P.degree → v (a + j) = v (b + j)) :
    v (a + P.degree) = v (b + P.degree) := by
  have hr (n : Nat) (hn : P.degree < n) : convolution P.p1 v (P.degree + 1) n = 0 := by
    have hh := hres n
    unfold residual cutoff at hh
    rw [if_neg (by omega), Int.zero_add] at hh
    exact hh
  have hleft := hr (a + P.degree + s) (by omega)
  have hright := hr (b + P.degree + s) (by omega)
  rw [convolution_dot] at hleft hright
  have htotal : total (fun j => shift v j (a + P.degree + s) * P.p1 j) (P.degree + 1) =
      total (fun j => shift v j (b + P.degree + s) * P.p1 j) (P.degree + 1) := hleft.trans hright.symm
  have hpivot := total_eq_pivot _ _ (P.degree + 1) s (by omega) htotal (by
    intro j hj hjs
    by_cases hlow : j < s
    · simp [hbefore j hlow]
    · have ht : P.degree + s - j < P.degree := by omega
      have hbits := he (P.degree + s - j) ht
      dsimp [shift]
      rw [if_neg (by omega : ¬ a + P.degree + s < j),
        if_neg (by omega : ¬ b + P.degree + s < j),
        show a + P.degree + s - j = a + (P.degree + s - j) by omega,
        show b + P.degree + s - j = b + (P.degree + s - j) by omega, hbits])
  dsimp [shift] at hpivot
  rw [if_neg (by omega : ¬ a + P.degree + s < s), if_neg (by omega : ¬ b + P.degree + s < s),
    show a + P.degree + s - s = a + P.degree by omega,
    show b + P.degree + s - s = b + P.degree by omega] at hpivot
  apply Int.eq_of_mul_eq_mul_left (a := P.p1 s) hps
  simpa only [Int.mul_comm] using hpivot

/-- Rationality here means an exact coefficientwise polynomial identity. -/
theorem rational_binary_eventually_periodic (v : Nat → Int)
    (hv : ∀ n, v n = 0 ∨ v n = 1) (P : PolynomialPair)
    (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0)
    (hres : ∀ n, P.residual v n = 0) : EventuallyPeriodic v := by
  rcases first_nonzero_coefficient P.p1 P.degree hp with ⟨s, hs, hps, hbefore⟩
  apply deterministic_binary_periodic v hv (P.degree + 1) P.degree
  intro a b ha hb he
  exact recurrence_determines P v s hs hps hbefore hres a b ha hb he

/-- A nonperiodic binary sequence has a nonzero residual for every nonzero denominator. -/
theorem nonzero_residual (v : Nat → Int) (hv : ∀ n, v n = 0 ∨ v n = 1)
    (haper : ¬ EventuallyPeriodic v) (P : PolynomialPair)
    (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) : ∃ n, P.residual v n ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro hn
  have hzero : ∀ n, P.residual v n = 0 := by
    intro n
    by_cases hz : P.residual v n = 0
    · exact hz
    · exact False.elim (hn ⟨n, hz⟩)
  exact haper (rational_binary_eventually_periodic v hv P hp hzero)

end RationalSeries
end CollatzLab
