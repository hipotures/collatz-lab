import CollatzLab.UniversalEqualWeight

/-! Limits of replacing the uniform degree-six/order-thirteen ledger by a smaller degree. -/
namespace CollatzLab
open Family

/-- Real admissible images attain the worst-case parameters r=e=L-1. -/
def highWeight101 : Morphism.Images 101 where
  zero := fun j => decide (j.val ≠ 100)
  one := fun j => decide (j.val ≠ 1)

theorem highWeight101_admissible : Morphism.image highWeight101 true 0 = true ∧
    Morphism.weight (Morphism.image highWeight101 false) 101 =
      Morphism.weight (Morphism.image highWeight101 true) 101 ∧
    highWeight101.zero ≠ highWeight101.one := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := congrArg (fun f : Fin 101 → Bool => f ⟨1, by decide⟩) h
  change true = false at hh
  contradiction

theorem highWeight101_parameters :
    Morphism.weight (Morphism.image highWeight101 true) 101 = 100 ∧
    Morphism.e highWeight101 = 100 := by decide

set_option maxRecDepth 100000 in
/-- Exact small-base comparisons; this is a ledger obstruction, not a residual-order bound. -/
theorem small_degree_base_obstruction : ∀ d : Nat, d ≤ 5 →
    (2 : Int) ^ ((2 * d + 1) * 101) ≤ (3 : Int) ^ (d * 100 + 201) := by decide

/-- Degrees zero through five do not close the universal ledger using order only `2*d+1`. -/
theorem small_degree_worst_ledger_failure (d : Nat) (hd : d ≤ 5) :
    ¬ (max ((2 : Int) ^ 101) ((3 : Int) ^ 100)) ^ (d * 100 + 201) <
      (2 : Int) ^ ((2 * d + 1) * 101 * 100) := by
  have hb := small_degree_base_obstruction d hd
  have hp := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := 2) (by decide) _) hb 100
  rw [int_pow_mul, int_pow_mul] at hp
  have hm := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := 3) (by decide) 100)
    (Int.le_max_right ((2 : Int) ^ 101) ((3 : Int) ^ 100)) (d * 100 + 201)
  rw [int_pow_mul] at hm
  have he : (d * 100 + 201) * 100 = 100 * (d * 100 + 201) := by ac_rfl
  rw [he] at hp
  intro hh
  have hlo := Int.le_trans hp hm
  omega

/-- The obstruction occurs within the original semantic domain, not just in free parameters. -/
theorem highWeight101_small_degree_failure (d : Nat) (hd : d ≤ 5) :
    ¬ Morphism.m highWeight101 ^ (d * (101 - 1) + 101 + Morphism.e highWeight101) <
      (2 : Int) ^ (101 * (101 - 1) * (2 * d + 1)) := by
  have he := highWeight101_parameters
  have hh := small_degree_worst_ledger_failure d hd
  change ¬ (max ((2 : Int) ^ 101) ((3 : Int) ^
    Morphism.weight (Morphism.image highWeight101 true) 101)) ^
      (d * (101 - 1) + 101 + Morphism.e highWeight101) < _
  rw [he.1, he.2]
  have hexp : 101 * (101 - 1) * (2 * d + 1) = (2 * d + 1) * 101 * 100 := by
    change 101 * 100 * (2 * d + 1) = _
    ac_rfl
  rw [hexp]
  exact hh

/-- The same word has a much better individual low-degree approximant. -/
def highWeight101Low : PolynomialPair where
  degree := 2
  p0 := fun j => ([-1, 1, -1] : List Int).getD j 0
  p1 := fun j => ([1, -1, 0] : List Int).getD j 0

set_option maxRecDepth 100000 in
theorem highWeight101_low_first : highWeight101Low.First (Morphism.parityWord highWeight101) 201 ∧
    highWeight101Low.residual (Morphism.parityWord highWeight101) 201 = -1 := by
  unfold PolynomialPair.First
  decide

theorem highWeight101_low_gap : highWeight101Low.Gap highWeight101 201 := by
  have hw := highWeight101_parameters
  unfold PolynomialPair.Gap Morphism.m Morphism.A Morphism.B
  rw [hw.1, hw.2]
  change (max ((2 : Int) ^ 101) ((3 : Int) ^ 100)) ^ 401 < (2 : Int) ^ (101 * 100 * 201)
  have hm : max ((2 : Int) ^ 101) ((3 : Int) ^ 100) ≤ (4 : Int) ^ 101 := by
    apply Int.max_le.mpr
    exact ⟨pow_le_pow_of_le (by decide) (by decide) _,
      Int.le_trans (pow_le_pow_of_le (by decide) (by decide : (3 : Int) ≤ 4) 100)
        (pow_mono_exp (by decide) (by decide))⟩
  have hp := pow_le_pow_of_le
    (Int.le_trans (pow_nonneg_of_nonneg (x := 2) (by decide) 101) (Int.le_max_left _ _)) hm 401
  have h4 : (4 : Int) ^ 101 = (2 : Int) ^ 202 := int_pow_mul 2 2 101
  rw [h4, int_pow_mul] at hp
  have hlt := pow_two_strict_exponent (show 202 * 401 < 101 * 100 * 201 by decide)
  exact Int.lt_of_le_of_lt hp hlt

theorem no_rational_seed_realizes_highWeight101_low_degree (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord highWeight101) :=
  no_rational_seed_with_polynomial_pair (by decide) highWeight101
    highWeight101_admissible.1 highWeight101_admissible.2.1
    highWeight101_admissible.2.2 highWeight101Low 201 (by decide)
    highWeight101_low_first.1 highWeight101_low_gap p q

/-- Every degree at least six satisfies the same universal dimension-count ledger. -/
theorem numerical_gap_from_six (L r e : Nat) (hL : 2 ≤ L) (hr : r < L) (he : e < L) :
    ∀ t : Nat, (max ((2 : Int) ^ L) ((3 : Int) ^ r)) ^ ((6 + t) * (L - 1) + L + e) <
      (2 : Int) ^ (L * (L - 1) * (2 * (6 + t) + 1))
  | 0 => by
    have hh := degree_six_numerical_gap L r e hL hr he
    rw [show 13 * L * (L - 1) = L * (L - 1) * 13 by ac_rfl] at hh
    exact hh
  | t + 1 => by
    let mm := max ((2 : Int) ^ L) ((3 : Int) ^ r)
    have h3 : (3 : Int) ^ r ≤ (3 : Int) ^ L := pow_mono_exp (by decide) (by omega)
    have h2 := pow_le_pow_of_le (x := (2 : Int)) (y := 3) (by decide) (by decide) L
    have hm3 : mm ≤ (3 : Int) ^ L := Int.max_le.mpr ⟨h2, h3⟩
    have h34 := positive_pow_strict 4 3 (by decide) (by decide) L (by omega)
    have h4 : (4 : Int) ^ L = (2 : Int) ^ (2 * L) := int_pow_mul 2 2 L
    rw [h4] at h34
    have hm2 : mm ≤ (2 : Int) ^ (2 * L) := Int.le_trans hm3 (by omega)
    have hinc := pow_le_pow_of_le (Int.le_trans (pow_nonneg_of_nonneg (x := 2) (by decide) L)
      (Int.le_max_left _ _)) hm2 (L - 1)
    rw [int_pow_mul] at hinc
    have hpos : 0 < mm := Int.lt_of_lt_of_le (pow_pos_of_pos (x := 2) (by decide) L) (Int.le_max_left _ _)
    have hi := numerical_gap_from_six L r e hL hr he t
    have hp := Int.mul_lt_mul hi hinc (pow_pos_of_pos hpos (L - 1))
      (pow_nonneg_of_nonneg (x := 2) (by decide) _)
    have hcost : (6 + (t + 1)) * (L - 1) + L + e =
        ((6 + t) * (L - 1) + L + e) + (L - 1) := by
      rw [show 6 + (t + 1) = (6 + t) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    have hgain : L * (L - 1) * (2 * (6 + (t + 1)) + 1) =
        L * (L - 1) * (2 * (6 + t) + 1) + 2 * L * (L - 1) := by
      rw [show 2 * (6 + (t + 1)) + 1 = (2 * (6 + t) + 1) + 2 by omega, Nat.mul_add]
      congr 1
      ac_rfl
    rw [hcost, hgain]
    simpa only [int_pow_add] using hp

def UniversalDimensionGap (d : Nat) : Prop :=
  ∀ L r e : Nat, 2 ≤ L → r < L → e < L →
    (max ((2 : Int) ^ L) ((3 : Int) ^ r)) ^ (d * (L - 1) + L + e) <
      (2 : Int) ^ (L * (L - 1) * (2 * d + 1))

/-- Six is minimal for this specific universal ledger and the guaranteed order `2*d+1`.
This does not say that every individual word needs degree six. -/
theorem universal_dimension_gap_iff (d : Nat) : UniversalDimensionGap d ↔ 6 ≤ d := by
  constructor
  · intro h
    by_cases hd : 6 ≤ d
    · exact hd
    · have hfail := small_degree_worst_ledger_failure d (by omega)
      have hg := h 101 100 100 (by decide) (by decide) (by decide)
      have he : 101 * (101 - 1) * (2 * d + 1) = (2 * d + 1) * 101 * 100 := by
        change 101 * 100 * (2 * d + 1) = _
        ac_rfl
      rw [he] at hg
      have hc : d * (101 - 1) + 101 + 100 = d * 100 + 201 := by omega
      rw [hc] at hg
      exact False.elim (hfail hg)
  · intro hd L r e hL hr he
    have hh := numerical_gap_from_six L r e hL hr he (d - 6)
    rw [Nat.add_sub_of_le hd] at hh
    exact hh

/-- Every raw degree at least six supplies a closing certificate for every admissible morphism. -/
theorem Morphism.universal_high_degree_certificate (d : Nat) (hd6 : 6 ≤ d)
    {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) :
    ∃ P : PolynomialPair, ∃ N : Nat, P.degree = d ∧ 2 * d + 1 ≤ N ∧
      (∃ j, j ≤ P.degree ∧ P.p1 j ≠ 0) ∧
      P.First (Morphism.parityWord M) N ∧ P.Gap M N := by
  rcases PolynomialPair.polynomial_pair_exists d (Morphism.parityWord M) with ⟨P, hdeg, hp, hz⟩
  rcases RationalSeries.nonzero_residual _ (Morphism.parity_binary M)
    (Morphism.not_eventually_periodic hL M h1 hw hd) P hp with ⟨n, hn⟩
  rcases RationalSeries.first_nonzero_coefficient (P.residual (Morphism.parityWord M)) n
    ⟨n, Nat.le_refl _, hn⟩ with ⟨N, _, hlead, hbefore⟩
  have hN : 2 * d + 1 ≤ N := by
    by_cases h : N < 2 * d + 1
    · have hh := hz N h
      contradiction
    · omega
  refine ⟨P, N, hdeg, hN, hp, ⟨hbefore, hlead⟩, ?_⟩
  have hgap := (universal_dimension_gap_iff d).2 hd6 L (Morphism.weight (Morphism.image M true) L)
    (Morphism.e M) hL (Morphism.weight_lt_length M hw hd) (Morphism.se_bounds M hd).2
  have hmono := pow_mono_exp (x := (2 : Int)) (by decide)
    (Nat.mul_le_mul_left (L * (L - 1)) hN)
  unfold PolynomialPair.Gap
  rw [hdeg]
  exact Int.lt_of_lt_of_le hgap hmono

/-- All these images remain covered by the proved universal theorem. -/
theorem no_rational_seed_realizes_highWeight101 (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord highWeight101) :=
  no_rational_seed_realizes_all_equal_weight (by decide) highWeight101
    highWeight101_admissible.1 highWeight101_admissible.2.1
    highWeight101_admissible.2.2 p q

end CollatzLab
