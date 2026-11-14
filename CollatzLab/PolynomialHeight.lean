import CollatzLab.PolynomialPair
import CollatzLab.ExponentialGap

/-! Coefficient norms and heights for general signed polynomial pairs. -/
namespace CollatzLab.PolynomialPair
open CollatzLab.Family

def coefficientNorm (p : Nat → Int) : Nat → Int
  | 0 => 1
  | n + 1 => coefficientNorm p n + absInt (p n)

def norm (P : PolynomialPair) : Int :=
  coefficientNorm P.p0 (P.degree + 1) + coefficientNorm P.p1 (P.degree + 1)

def heightConstant (P : PolynomialPair) : Int := ((P.degree : Int) + 1) * P.norm

theorem coefficientNorm_positive (p : Nat → Int) : ∀ n, 1 ≤ coefficientNorm p n
  | 0 => Int.le_refl _
  | n + 1 => by
    have := coefficientNorm_positive p n
    have := absInt_nonneg (p n)
    dsimp [coefficientNorm]; omega

theorem coefficientNorm_bound (p : Nat → Int) : ∀ n j, j < n → absInt (p j) ≤ coefficientNorm p n
  | 0, _, hj => by omega
  | n + 1, j, hj => by
    have hp := coefficientNorm_positive p n
    have hc := absInt_nonneg (p n)
    by_cases he : j = n
    · subst j; dsimp [coefficientNorm]; omega
    · have hi := coefficientNorm_bound p n j (by omega)
      dsimp [coefficientNorm]; omega

theorem norm_bounds (P : PolynomialPair) : 1 ≤ P.norm ∧
    (∀ j, j ≤ P.degree → absInt (P.p0 j) ≤ P.norm) ∧
    (∀ j, j ≤ P.degree → absInt (P.p1 j) ≤ P.norm) := by
  have h0 := coefficientNorm_positive P.p0 (P.degree + 1)
  have h1 := coefficientNorm_positive P.p1 (P.degree + 1)
  refine ⟨by dsimp [norm]; omega, ?_, ?_⟩
  · intro j hj
    have := coefficientNorm_bound P.p0 (P.degree + 1) j (by omega)
    dsimp [norm]; omega
  · intro j hj
    have := coefficientNorm_bound P.p1 (P.degree + 1) j (by omega)
    dsimp [norm]; omega

theorem heightConstant_positive (P : PolynomialPair) : 1 ≤ P.heightConstant := by
  have hnorm := P.norm_bounds.1
  have hh := Int.mul_le_mul (show (1 : Int) ≤ (P.degree : Int) + 1 by omega) hnorm
    (by decide : (0 : Int) ≤ 1) (by omega : 0 ≤ (P.degree : Int) + 1)
  exact hh

theorem eval_bound (p : Nat → Int) (a b m C : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ham : a ≤ m) (hbm : b ≤ m) (hC : 0 ≤ C) :
    ∀ d, (∀ j, j ≤ d → absInt (p j) ≤ C) →
      absInt (eval p a b d) ≤ ((d : Int) + 1) * C * m ^ d
  | 0, hp => by simpa [eval, sum, Int.pow_zero] using hp 0 (by omega)
  | d + 1, hp => by
    have hm : 0 ≤ m := by omega
    have hi := eval_bound p a b m C ha hb ham hbm hC d (by intro j hj; exact hp j (by omega))
    have hl := Int.mul_le_mul hbm hi (absInt_nonneg _) hm
    have hpow := pow_le_pow_of_le ha ham (d + 1)
    have hr := Int.mul_le_mul (hp (d + 1) (by omega)) hpow (pow_nonneg_of_nonneg ha _) hC
    have hh := absInt_add_le (b * eval p a b d) (p (d + 1) * a ^ (d + 1))
    rw [absInt_mul, absInt_mul, absInt_of_nonneg hb,
      absInt_of_nonneg (pow_nonneg_of_nonneg ha _)] at hh
    change absInt (b * eval p a b d + p (d + 1) * a ^ (d + 1)) ≤ _
    simp only [Int.ofNat_add, Int.ofNat_one]
    rw [Int.pow_succ m] at hr ⊢
    family_ring

theorem form_bound {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (P : PolynomialPair) (p q : Int) (k : Nat) :
    absInt (E M P p q k) ≤ P.heightConstant * Morphism.mk M k ^ P.degree * Morphism.H M p q k := by
  have ha : 0 ≤ Morphism.a M k := by have := (Morphism.ab_props hL M k).1; omega
  have hb : 0 ≤ Morphism.b M k := by have := (Morphism.ab_props hL M k).2.1; omega
  have hbounds := Morphism.ab_le_mk hL M k
  have hnorm := P.norm_bounds
  have h0 := eval_bound P.p0 _ _ _ P.norm ha hb hbounds.2.2.1 hbounds.2.2.2
    (by omega) P.degree hnorm.2.1
  have h1 := eval_bound P.p1 _ _ _ P.norm ha hb hbounds.2.2.1 hbounds.2.2.2
    (by omega) P.degree hnorm.2.2
  have ht0 := Int.mul_le_mul_of_nonneg_left h0 (absInt_nonneg (Morphism.D M q k))
  have ht1 := Int.mul_le_mul_of_nonneg_right h1 (absInt_nonneg (Morphism.u M p q k))
  have ht := absInt_add_le (Morphism.D M q k * eval P.p0 (Morphism.a M k) (Morphism.b M k) P.degree)
    (eval P.p1 (Morphism.a M k) (Morphism.b M k) P.degree * Morphism.u M p q k)
  rw [absInt_mul, absInt_mul] at ht
  unfold E heightConstant Morphism.H
  family_ring

theorem form_power_bound {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (P : PolynomialPair)
    {p q : Int} (hr : RealizesWord p q (Morphism.parityWord M)) (k : Nat) :
    absInt (E M P p q k) ^ (L - 1) ≤
      (P.heightConstant ^ (L - 1) * Morphism.H M p q 0 ^ (L - 1)) *
        ((2 * (L : Int)) ^ (L - 1)) ^ k *
          Morphism.m M ^ ((P.degree * (L - 1) + L + Morphism.e M) * L ^ k) := by
  have hm : 1 ≤ Morphism.m M := (Morphism.ab_le_mk hL M k).1
  have hC : 0 ≤ 2 * (L : Int) := by omega
  have hH0 := Morphism.height_positive hL M hw hd hr 0
  have hh := Morphism.height_power_closed hL M h1 hw hd hr k
  have hemono := pow_mono_exp (x := Morphism.m M) hm (Nat.mul_le_mul_left (L + Morphism.e M)
    (show L ^ k - 1 ≤ L ^ k by omega))
  have hnonneg := Int.mul_nonneg
    (pow_nonneg_of_nonneg (by omega : 0 ≤ Morphism.H M p q 0) (L - 1))
    (pow_nonneg_of_nonneg hC (k * (L - 1)))
  have hloose := Int.mul_le_mul_of_nonneg_left hemono hnonneg
  have hheight : Morphism.H M p q k ^ (L - 1) ≤ Morphism.H M p q 0 ^ (L - 1) *
      (2 * (L : Int)) ^ (k * (L - 1)) * Morphism.m M ^ ((L + Morphism.e M) * L ^ k) := Int.le_trans hh hloose
  have hp := pow_le_pow_of_le (absInt_nonneg _) (form_bound hL M P p q k) (L - 1)
  dsimp [Morphism.mk] at hp
  simp only [mul_pow, int_pow_mul] at hp
  have hco : 0 ≤ P.heightConstant ^ (L - 1) * Morphism.m M ^ ((L ^ k * P.degree) * (L - 1)) :=
    Int.mul_nonneg (pow_nonneg_of_nonneg (by have := P.heightConstant_positive; omega) _)
      (pow_nonneg_of_nonneg (by omega) _)
  have ht := Int.mul_le_mul_of_nonneg_left hheight hco
  have he : (L ^ k * P.degree) * (L - 1) + (L + Morphism.e M) * L ^ k =
      (P.degree * (L - 1) + L + Morphism.e M) * L ^ k := by
    calc
      _ = (P.degree * (L - 1) + (L + Morphism.e M)) * L ^ k := by
        conv => rhs; rw [Nat.add_mul]
        ac_rfl
      _ = _ := by rw [Nat.add_assoc]
  have hid : (P.heightConstant ^ (L - 1) * Morphism.m M ^ ((L ^ k * P.degree) * (L - 1))) *
      (Morphism.H M p q 0 ^ (L - 1) * (2 * (L : Int)) ^ (k * (L - 1)) *
        Morphism.m M ^ ((L + Morphism.e M) * L ^ k)) =
      (P.heightConstant ^ (L - 1) * Morphism.H M p q 0 ^ (L - 1)) *
        ((2 * (L : Int)) ^ (L - 1)) ^ k *
          Morphism.m M ^ ((P.degree * (L - 1) + L + Morphism.e M) * L ^ k) := by
    rw [int_pow_mul, Nat.mul_comm (L - 1) k, ← he, int_pow_add]; ac_rfl
  rw [hid] at ht
  exact Int.le_trans hp ht

end CollatzLab.PolynomialPair
