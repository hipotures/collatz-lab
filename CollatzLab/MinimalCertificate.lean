import CollatzLab.DegreeTradeoff

/-! Sharpness of the implemented polynomial certificate criterion, not of all possible methods. -/
namespace CollatzLab.MinimalCertificate
open CollatzLab.Family CollatzLab.PolynomialPair

def normalPrefix (n : Nat) : Int := ([1,1,0,1,0,0,0,1,0,0,1,1] : List Int).getD n 0

/-- Six explicit small linear systems are nonsingular; all arithmetic is checked by omega. -/
theorem prefix_kernel (d : Nat) (hd : d ≤ 5) (p : Nat → Int)
    (h : ∀ i, i < d + 1 → convolution p normalPrefix (d + 1) (d + 1 + i) = 0) :
    ∀ j, j ≤ d → p j = 0 := by
  intro j hj
  have hc : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · have h0 := h 0 (by decide)
    simp [convolution, shift, normalPrefix] at h0
    have he : j = 0 := by omega
    subst j
    omega
  · have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    simp [convolution, shift, normalPrefix] at h0 h1
    have hjc : j = 0 ∨ j = 1 := by omega
    rcases hjc with rfl | rfl <;> omega
  · have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    simp [convolution, shift, normalPrefix] at h0 h1 h2
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjc with rfl | rfl | rfl <;> omega
  · have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    simp [convolution, shift, normalPrefix] at h0 h1 h2 h3
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjc with rfl | rfl | rfl | rfl <;> omega
  · have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    have h4 := h 4 (by decide)
    simp [convolution, shift, normalPrefix] at h0 h1 h2 h3 h4
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjc with rfl | rfl | rfl | rfl | rfl <;> omega
  · have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    simp [convolution, shift, normalPrefix] at h0 h1 h2 h3 h4 h5
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjc with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem convolution_word_ext (p v w : Nat → Int) (n : Nat)
    (h : ∀ j, j ≤ n → v j = w j) (count : Nat) :
    convolution p v count n = convolution p w count n := by
  rw [convolution_dot, convolution_dot]
  unfold FiniteLinear.dot
  apply FiniteLinear.total_ext
  intro j _
  unfold shift
  dsimp only
  split
  · rfl
  · rw [h (n - j) (by omega)]

/-- This particular prefix forces every nonzero degree-d denominator to have residual order at most 2d+1. -/
theorem prefix_order_bound (v : Nat → Int) (hv : ∀ n, n < 12 → v n = normalPrefix n)
    (P : PolynomialPair) (hdeg : P.degree ≤ 5)
    (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) (N : Nat)
    (hz : ∀ n, n < N → P.residual v n = 0) : N ≤ 2 * P.degree + 1 := by
  by_cases hN : N ≤ 2 * P.degree + 1
  · exact hN
  · have hker := prefix_kernel P.degree hdeg P.p1 (by
      intro i hi
      let n := P.degree + 1 + i
      have hn : n < N := by dsimp [n]; omega
      have hh := hz n hn
      unfold residual cutoff at hh
      rw [if_neg (by dsimp [n]; omega), Int.zero_add] at hh
      have he := convolution_word_ext P.p1 v normalPrefix n
        (by intro j hj; apply hv; dsimp [n] at hj; omega) (P.degree + 1)
      exact he.symm.trans hh)
    rcases hp with ⟨j, hj, hpj⟩
    exact False.elim (hpj (hker j hj))

/-- Only twelve initial symbols are needed for the small-degree order obstruction. -/
def hardOne (j : Nat) : Bool := if j < 12 then decide (normalPrefix j = 1) else decide (j ≠ 999)
def hardZero (j : Nat) : Bool := if j = 0 then false else if j = 999 then true else hardOne j

def hardImages : Morphism.Images 1000 where
  zero := fun j => hardZero j.val
  one := fun j => hardOne j.val

set_option maxRecDepth 100000 in
theorem hard_admissible : Morphism.image hardImages true 0 = true ∧
    Morphism.weight (Morphism.image hardImages false) 1000 =
      Morphism.weight (Morphism.image hardImages true) 1000 ∧
    hardImages.zero ≠ hardImages.one := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := congrArg (fun f : Fin 1000 → Bool => f ⟨0, by decide⟩) h
  change false = true at hh
  contradiction

set_option maxRecDepth 100000 in
theorem hard_parameters : Morphism.weight (Morphism.image hardImages true) 1000 = 993 ∧
    Morphism.e hardImages = 999 := by decide

theorem hard_prefix : ∀ n, n < 12 → Morphism.parityWord hardImages n = normalPrefix n := by decide

theorem hard_exponent_comparison : ∀ d : Nat, d ≤ 5 →
    ((2 * d + 1) * 1000 * 999) * 12 ≤ 19 * (993 * (d * 999 + 1999)) := by decide

/-- Reflection of a comparison of twelfth powers avoids evaluating multi-million-bit integers. -/
theorem hard_small_degree_ledger_failure (d : Nat) (hd : d ≤ 5) :
    ¬ max ((2 : Int) ^ 1000) ((3 : Int) ^ 993) ^ (d * 999 + 1999) <
      (2 : Int) ^ ((2 * d + 1) * 1000 * 999) := by
  let g := (2 * d + 1) * 1000 * 999
  let c := 993 * (d * 999 + 1999)
  have he : g * 12 ≤ 19 * c := hard_exponent_comparison d hd
  have h0 := pow_mono_exp (x := (2 : Int)) (by decide) he
  have h1 := pow_le_pow_of_le (x := (2 : Int) ^ 19) (y := (3 : Int) ^ 12) (by decide) (by decide) c
  rw [int_pow_mul, int_pow_mul] at h1
  have h12 : ((2 : Int) ^ g) ^ 12 ≤ ((3 : Int) ^ c) ^ 12 := by
    rw [int_pow_mul, int_pow_mul, Nat.mul_comm c 12]
    exact Int.le_trans h0 h1
  have hab : (2 : Int) ^ g ≤ (3 : Int) ^ c := by
    by_cases hh : (2 : Int) ^ g ≤ (3 : Int) ^ c
    · exact hh
    · have hstrict := positive_pow_strict ((2 : Int) ^ g) ((3 : Int) ^ c)
        (pow_ge_one (by decide) c) (by omega) 12 (by decide)
      omega
  have hm := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := 3) (by decide) 993)
    (Int.le_max_right ((2 : Int) ^ 1000) ((3 : Int) ^ 993)) (d * 999 + 1999)
  rw [int_pow_mul] at hm
  have hlo := Int.le_trans hab hm
  change (2 : Int) ^ ((2 * d + 1) * 1000 * 999) ≤
    max ((2 : Int) ^ 1000) ((3 : Int) ^ 993) ^ (d * 999 + 1999) at hlo
  intro hlt
  exact (by omega : False)

/-- No nonzero denominator of degree at most five can close the implemented ledger for this word. -/
theorem hard_no_small_certificate (P : PolynomialPair) (hdeg : P.degree ≤ 5)
    (hp : ∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) (N : Nat)
    (hz : ∀ n, n < N → P.residual (Morphism.parityWord hardImages) n = 0) :
    ¬ P.Gap hardImages N := by
  have hN := prefix_order_bound _ hard_prefix P hdeg hp N hz
  have hbad := hard_small_degree_ledger_failure P.degree hdeg
  have hmono := pow_mono_exp (x := (2 : Int)) (by decide)
    (Nat.mul_le_mul_left (1000 * 999) hN)
  have he : 1000 * 999 * (2 * P.degree + 1) = (2 * P.degree + 1) * 1000 * 999 := by ac_rfl
  rw [he] at hmono
  unfold Gap Morphism.m Morphism.A Morphism.B
  rw [hard_parameters.1, hard_parameters.2]
  have hc : P.degree * (1000 - 1) + 1000 + 999 = P.degree * 999 + 1999 := by omega
  rw [hc]
  intro hgap
  apply hbad
  exact Int.lt_of_lt_of_le hgap hmono

def hardSix : PolynomialPair where
  degree := 6
  p0 := fun j => ([1, 2, 0, -1, -2, -4, -1] : List Int).getD j 0
  p1 := fun j => ([-1, -1, 1, 1, 2, 1, -1] : List Int).getD j 0

theorem hard_six_first : hardSix.First (Morphism.parityWord hardImages) 13 ∧
    hardSix.residual (Morphism.parityWord hardImages) 13 = -1 := by
  unfold First
  decide

theorem hard_six_gap : hardSix.Gap hardImages 13 :=
  Morphism.degree_six_ledger (by decide) hardImages hard_admissible.2.1 hard_admissible.2.2

/-- An explicit degree-six certificate closes the same case that defeats every smaller degree. -/
theorem hard_no_rational_seed (p q : Int) : ¬ RealizesWord p q (Morphism.parityWord hardImages) :=
  no_rational_seed_with_polynomial_pair (by decide) hardImages hard_admissible.1
    hard_admissible.2.1 hard_admissible.2.2 hardSix 13 (by decide) hard_six_first.1 hard_six_gap p q

/-- Uniform degree bound for exactly the finite coefficient/height interface implemented in Phase 8. -/
def UniversalCertificateDegree (d : Nat) : Prop :=
  ∀ L : Nat, ∀ _hL : 2 ≤ L, ∀ M : Morphism.Images L,
    Morphism.image M true 0 = true →
    Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L →
    M.zero ≠ M.one →
    ∃ P : PolynomialPair, ∃ N : Nat, P.degree ≤ d ∧ P.degree ≤ N ∧
      (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧ P.First (Morphism.parityWord M) N ∧ P.Gap M N

/-- Six is the least uniform certificate degree for this specific interface, allowing arbitrary order. -/
theorem universal_certificate_degree_iff (d : Nat) : UniversalCertificateDegree d ↔ 6 ≤ d := by
  constructor
  · intro h
    by_cases hd : 6 ≤ d
    · exact hd
    · rcases h 1000 (by decide) hardImages hard_admissible.1 hard_admissible.2.1
        hard_admissible.2.2 with ⟨P, N, hpd, _, hp, hfirst, hgap⟩
      exact False.elim (hard_no_small_certificate P (by omega) hp N hfirst.1 hgap)
  · intro hd L hL M h1 hw hne
    rcases Morphism.universal_degree_six_certificate hL M h1 hw hne with
      ⟨P, N, hdeg, hN, hp, hfirst, hgap⟩
    exact ⟨P, N, by omega, by omega, hp, hfirst, hgap⟩

end CollatzLab.MinimalCertificate
