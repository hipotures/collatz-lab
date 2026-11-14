import CollatzLab.MorphismApprox
import CollatzLab.Family

/-! General height estimates, retaining the factor `(2L)^k`. -/
namespace CollatzLab.Morphism
open CollatzLab.Family

def m {L : Nat} (M : Images L) := max (A L) (B M)
def mk {L : Nat} (M : Images L) (k : Nat) := m M ^ (L ^ k)
def H {L : Nat} (M : Images L) (p q : Int) (k : Nat) := absInt (u M p q k) + absInt (D M q k)

theorem bit_abs (b : Bool) : absInt (bit b) ≤ 1 := by cases b <;> decide
theorem coeff_abs {L : Nat} (M : Images L) (j : Nat) : absInt (coeff M j) ≤ 1 := by
  cases h0 : image M false j <;> cases h1 : image M true j <;> simp [coeff, bit, h0, h1, absInt]

theorem sum_bound (v : Nat → Int) (a b M : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) (hv : ∀ j, absInt (v j) ≤ 1) :
    ∀ n, absInt (sum v a b (n + 1)) ≤ ((n : Int) + 1) * M ^ n
  | 0 => by simpa [sum, Int.pow_zero] using hv 0
  | n + 1 => by
    have hm : 0 ≤ M := by omega
    have hi := sum_bound v a b M ha hb haM hbM hv n
    have hleft := Int.mul_le_mul hbM hi (absInt_nonneg _) hm
    have hpow := pow_le_pow_of_le ha haM (n + 1)
    have hright := Int.mul_le_mul (hv (n + 1)) hpow (pow_nonneg_of_nonneg ha _) (by decide : (0 : Int) ≤ 1)
    have hh := absInt_add_le (b * sum v a b (n + 1)) (v (n + 1) * a ^ (n + 1))
    rw [absInt_mul, absInt_mul, absInt_of_nonneg hb,
      absInt_of_nonneg (pow_nonneg_of_nonneg ha _)] at hh
    change absInt (b * sum v a b (n + 1) + v (n + 1) * a ^ (n + 1)) ≤ _
    simp only [Int.ofNat_add, Int.ofNat_one]
    rw [Int.pow_succ M] at hright ⊢
    family_ring

theorem Q_bound {L : Nat} (hL : 2 ≤ L) (M : Images L) (c : Bool) (a b Mmax : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ Mmax) (hbM : b ≤ Mmax) :
    absInt (Q M c a b) ≤ (L : Int) * Mmax ^ (L - 1) := by
  have hh := sum_bound (fun j => bit (image M c j)) a b Mmax ha hb haM hbM
    (fun _ => bit_abs _) (L - 1)
  rw [show L - 1 + 1 = L by omega] at hh
  have hc : ((L - 1 : Nat) : Int) + 1 = (L : Int) := by omega
  rw [hc] at hh
  exact hh

theorem GammaStar_bound {L : Nat} (M : Images L) (hd : M.zero ≠ M.one) (a b Mmax : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ Mmax) (hbM : b ≤ Mmax) :
    absInt (GammaStar M a b) ≤ (L : Int) * Mmax ^ (e M - s M) := by
  have hh := sum_bound (fun j => coeff M (s M + j)) a b Mmax ha hb haM hbM
    (fun _ => coeff_abs _ _) (e M - s M)
  have hn : (((e M - s M : Nat) : Int) + 1) ≤ (L : Int) := by have := se_bounds M hd; omega
  have hp := pow_nonneg_of_nonneg (show 0 ≤ Mmax by omega) (e M - s M)
  have hm := Int.mul_le_mul_of_nonneg_right hn hp
  exact Int.le_trans hh hm

theorem ab_le_mk {L : Nat} (hL : 2 ≤ L) (M : Images L) (k : Nat) :
    1 ≤ m M ∧ 1 ≤ mk M k ∧ a M k ≤ mk M k ∧ b M k ≤ mk M k := by
  have ha : 0 < A L := (ab_props hL M 0).1
  have hleft : A L ≤ m M := Int.le_max_left _ _
  have hright : B M ≤ m M := Int.le_max_right _ _
  have hm : 1 ≤ m M := by omega
  have hapos : 0 ≤ A L := by omega
  have hb0 : 0 < B M := (ab_props hL M 0).2.1
  have hbpos : 0 ≤ B M := by omega
  have ha' : a M k = A L ^ (L ^ k) := by rw [a_closed, A, int_pow_mul]
  exact ⟨hm, pow_ge_one hm _, by rw [ha']; exact pow_le_pow_of_le hapos hleft _,
    by rw [b_closed]; exact pow_le_pow_of_le hbpos hright _⟩

theorem difference_bound {a b M : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) (n : Nat) : absInt (b ^ n - a ^ n) ≤ M ^ n := by
  have h0 := pow_nonneg_of_nonneg ha n
  have h1 := pow_nonneg_of_nonneg hb n
  have h2 := pow_le_pow_of_le ha haM n
  have h3 := pow_le_pow_of_le hb hbM n
  unfold absInt
  split <;> omega

theorem height_step_aux {L : Nat} (hL : 2 ≤ L) (M : Images L) (hd : M.zero ≠ M.one)
    (a b Mmax v d v1 d1 : Int) (ha : 0 < a) (hb : 0 < b)
    (haM : a ≤ Mmax) (hbM : b ≤ Mmax)
    (hu : a ^ s M * v1 = b ^ e M * delta M a b v d)
    (hd1 : d1 = d * GammaStar M a b * (b ^ L - a ^ L)) :
    absInt v1 + absInt d1 ≤ (2 * (L : Int)) * Mmax ^ (L + e M) * (absInt v + absInt d) := by
  have hm : 1 ≤ Mmax := by omega
  have hF := pow_nonneg_of_nonneg (show 0 ≤ Mmax by omega) (L + e M)
  have hL0 : (0 : Int) ≤ (L : Int) := by omega
  have hQ := Q_bound hL M false a b Mmax (by omega) (by omega) haM hbM
  have hG := GammaStar_bound M hd a b Mmax (by omega) (by omega) haM hbM
  have hdiff := difference_bound (by omega : 0 ≤ a) (by omega : 0 ≤ b) haM hbM L
  have hdel := absInt_sub_le ((b ^ L - a ^ L) * v) (d * b * Q M false a b)
  rw [absInt_mul, absInt_mul, absInt_mul, absInt_of_nonneg (by omega : 0 ≤ b)] at hdel
  have hterm0 := Int.mul_le_mul_of_nonneg_right hdiff (absInt_nonneg v)
  have hterm1 := Int.mul_le_mul (Int.mul_le_mul_of_nonneg_left hbM (absInt_nonneg d)) hQ
    (absInt_nonneg _) (Int.mul_nonneg (absInt_nonneg d) (by omega : 0 ≤ Mmax))
  have hpow : Mmax * Mmax ^ (L - 1) = Mmax ^ L := by
    rw [Int.mul_comm, ← Int.pow_succ, show L - 1 + 1 = L by omega]
  have hterm1' : absInt d * Mmax * ((L : Int) * Mmax ^ (L - 1)) =
      (L : Int) * Mmax ^ L * absInt d := by rw [← hpow]; ac_rfl
  rw [hterm1'] at hterm1
  have hdelta : absInt (delta M a b v d) ≤ Mmax ^ L * (absInt v + (L : Int) * absInt d) := by
    unfold delta
    family_ring
  have hu' := congrArg absInt hu
  rw [absInt_mul, absInt_mul,
    absInt_of_nonneg (pow_nonneg_of_nonneg (by omega : 0 ≤ a) _),
    absInt_of_nonneg (pow_nonneg_of_nonneg (by omega : 0 ≤ b) _)] at hu'
  have hdiv := Int.mul_le_mul_of_nonneg_right (pow_ge_one (x := a) (by omega) (s M)) (absInt_nonneg v1)
  have hbe := pow_le_pow_of_le (by omega : 0 ≤ b) hbM (e M)
  have hprod := Int.mul_le_mul hbe hdelta (absInt_nonneg _)
    (pow_nonneg_of_nonneg (by omega : 0 ≤ Mmax) (e M))
  have hpF : Mmax ^ e M * Mmax ^ L = Mmax ^ (L + e M) := by rw [← int_pow_add, Nat.add_comm]
  have hprod' : Mmax ^ e M * (Mmax ^ L * (absInt v + (L : Int) * absInt d)) =
      Mmax ^ (L + e M) * (absInt v + (L : Int) * absInt d) := by rw [← hpF]; ac_rfl
  rw [hprod'] at hprod
  have huBound : absInt v1 ≤ Mmax ^ (L + e M) * (absInt v + (L : Int) * absInt d) := by omega
  have hGe := pow_mono_exp (x := Mmax) hm (show e M - s M ≤ e M by omega)
  have hG' := Int.le_trans hG (Int.mul_le_mul_of_nonneg_left hGe hL0)
  have hdBound := Int.mul_le_mul
    (Int.mul_le_mul_of_nonneg_left hG' (absInt_nonneg d)) hdiff
    (absInt_nonneg _) (Int.mul_nonneg (absInt_nonneg d)
      (Int.mul_nonneg hL0 (pow_nonneg_of_nonneg (by omega : 0 ≤ Mmax) (e M))))
  have hdAbs : absInt d1 = absInt d * absInt (GammaStar M a b) * absInt (b ^ L - a ^ L) := by
    rw [hd1, absInt_mul, absInt_mul]
  have hdBound' : absInt d1 ≤ (L : Int) * Mmax ^ (L + e M) * absInt d := by
    rw [hdAbs]
    have hid : (absInt d * ((L : Int) * Mmax ^ e M)) * Mmax ^ L =
        (L : Int) * Mmax ^ (L + e M) * absInt d := by rw [← hpF]; ac_rfl
    rw [hid] at hdBound
    exact hdBound
  have hslack := Int.mul_nonneg (Int.mul_nonneg (show 0 ≤ 2 * (L : Int) - 1 by omega) hF) (absInt_nonneg v)
  family_ring

theorem height_step {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) (k : Nat) :
    H M p q (k + 1) ≤ (2 * (L : Int)) * mk M k ^ (L + e M) * H M p q k :=
  height_step_aux hL M hd _ _ _ _ _ _ _ (ab_props hL M k).1 (ab_props hL M k).2.1
    (ab_le_mk hL M k).2.2.1 (ab_le_mk hL M k).2.2.2
    (tower_exact hL M h1 hw hd hr k).2 rfl

theorem height_positive {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) (k : Nat) :
    1 ≤ H M p q k := by
  have ho := denominator_odd hL M hw hd q hr.2.1 k
  have hn : D M q k ≠ 0 := by omega
  have hh := absInt_pos_of_ne_zero hn
  have hu := absInt_nonneg (u M p q k)
  unfold H; omega

theorem form_bound {L : Nat} (hL : 2 ≤ L) (M : Images L) (p q : Int) (k : Nat) :
    absInt (E M p q k) ≤ (L : Int) * mk M k ^ L * H M p q k := by
  let aa := a M k
  let bb := b M k
  let mm := mk M k
  have ha : 0 ≤ aa := by have := (ab_props hL M k).1; dsimp [aa]; omega
  have hb : 0 ≤ bb := by have := (ab_props hL M k).2.1; dsimp [bb]; omega
  have haM : aa ≤ mm := (ab_le_mk hL M k).2.2.1
  have hbM : bb ≤ mm := (ab_le_mk hL M k).2.2.2
  have hQ := Q_bound hL M true aa bb mm ha hb haM hbM
  have hdiff := difference_bound ha hb haM hbM L
  have hh := absInt_sub_le (D M q k * (bb * Q M true aa bb)) ((bb ^ L - aa ^ L) * u M p q k)
  rw [absInt_mul, absInt_mul, absInt_mul, absInt_of_nonneg hb] at hh
  have ht0 := Int.mul_le_mul hbM hQ (absInt_nonneg _) (show 0 ≤ mm by omega)
  have hpow : mm * mm ^ (L - 1) = mm ^ L := by
    rw [Int.mul_comm, ← Int.pow_succ, show L - 1 + 1 = L by omega]
  have hid : mm * ((L : Int) * mm ^ (L - 1)) = (L : Int) * mm ^ L := by rw [← hpow]; ac_rfl
  rw [hid] at ht0
  have ht1 := Int.mul_le_mul_of_nonneg_left ht0 (absInt_nonneg (D M q k))
  have hscale := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ (L : Int) by omega)
    (pow_nonneg_of_nonneg (show 0 ≤ mm by omega) L)
  have ht2 := Int.mul_le_mul_of_nonneg_right (Int.le_trans hdiff (by simpa using hscale)) (absInt_nonneg (u M p q k))
  change absInt (D M q k * (bb * Q M true aa bb) - (bb ^ L - aa ^ L) * u M p q k) ≤
    (L : Int) * mm ^ L * (absInt (u M p q k) + absInt (D M q k))
  family_ring

theorem height_power_closed {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) : ∀ k,
    H M p q k ^ (L - 1) ≤ H M p q 0 ^ (L - 1) *
      (2 * (L : Int)) ^ (k * (L - 1)) * m M ^ ((L + e M) * (L ^ k - 1))
  | 0 => by simp [Nat.pow_zero, Int.pow_zero]
  | k + 1 => by
    let C := 2 * (L : Int)
    have hC : 0 ≤ C := by dsimp [C]; omega
    have hm : 0 ≤ m M := by have := (ab_le_mk hL M k).1; omega
    have hs := height_step hL M h1 hw hd hr k
    have hpos := height_positive hL M hw hd hr (k + 1)
    have hp := pow_le_pow_of_le (show 0 ≤ H M p q (k + 1) by omega) hs (L - 1)
    dsimp [mk] at hp
    rw [mul_pow, mul_pow, int_pow_mul, int_pow_mul] at hp
    have hco : 0 ≤ C ^ (L - 1) * m M ^ ((L ^ k * (L + e M)) * (L - 1)) :=
      Int.mul_nonneg (pow_nonneg_of_nonneg hC _) (pow_nonneg_of_nonneg hm _)
    have ht := Int.mul_le_mul_of_nonneg_left (height_power_closed hL M h1 hw hd hr k) hco
    have he : ((L ^ k * (L + e M)) * (L - 1)) + (L + e M) * (L ^ k - 1) =
        (L + e M) * (L ^ (k + 1) - 1) := by
      calc
        _ = ((L - 1) * L ^ k) * (L + e M) + (L + e M) * (L ^ k - 1) := by ac_rfl
        _ = _ := height_exponent L (L + e M) k (by omega)
    have hc : (L - 1) + k * (L - 1) = (k + 1) * (L - 1) := by rw [Nat.add_mul]; omega
    have hid : (C ^ (L - 1) * m M ^ ((L ^ k * (L + e M)) * (L - 1))) *
        (H M p q 0 ^ (L - 1) * C ^ (k * (L - 1)) * m M ^ ((L + e M) * (L ^ k - 1))) =
        H M p q 0 ^ (L - 1) * C ^ ((k + 1) * (L - 1)) *
          m M ^ ((L + e M) * (L ^ (k + 1) - 1)) := by
      rw [← he, ← hc, int_pow_add, int_pow_add]; ac_rfl
    rw [hid] at ht
    exact Int.le_trans hp (by simpa only [C, Nat.mul_assoc] using ht)

theorem form_power_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) (k : Nat) :
    absInt (E M p q k) ^ (L - 1) ≤
      ((L : Int) ^ (L - 1) * H M p q 0 ^ (L - 1)) *
        ((2 * (L : Int)) ^ (L - 1)) ^ k * m M ^ ((L * L + e M) * L ^ k) := by
  have hm : 1 ≤ m M := (ab_le_mk hL M k).1
  have hC : 0 ≤ 2 * (L : Int) := by omega
  have hH0 := height_positive hL M hw hd hr 0
  have hh := height_power_closed hL M h1 hw hd hr k
  have hemono := pow_mono_exp (x := m M) hm (Nat.mul_le_mul_left (L + e M)
    (show L ^ k - 1 ≤ L ^ k by omega))
  have hnonneg := Int.mul_nonneg
    (pow_nonneg_of_nonneg (by omega : 0 ≤ H M p q 0) (L - 1)) (pow_nonneg_of_nonneg hC (k * (L - 1)))
  have hloose := Int.mul_le_mul_of_nonneg_left hemono hnonneg
  have hheight : H M p q k ^ (L - 1) ≤ H M p q 0 ^ (L - 1) *
      (2 * (L : Int)) ^ (k * (L - 1)) * m M ^ ((L + e M) * L ^ k) := Int.le_trans hh hloose
  have hp := pow_le_pow_of_le (absInt_nonneg _) (form_bound hL M p q k) (L - 1)
  dsimp [mk] at hp
  simp only [mul_pow, int_pow_mul] at hp
  have hc : 0 ≤ (L : Int) ^ (L - 1) * m M ^ ((L ^ k * L) * (L - 1)) :=
    Int.mul_nonneg (pow_nonneg_of_nonneg (by omega) _) (pow_nonneg_of_nonneg (by omega) _)
  have ht := Int.mul_le_mul_of_nonneg_left hheight hc
  have hmul := congrArg (fun n : Nat => L * n) (show L - 1 + 1 = L by omega)
  dsimp only at hmul
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have he : (L ^ k * L) * (L - 1) + (L + e M) * L ^ k = (L * L + e M) * L ^ k := by
    calc
      _ = (L * (L - 1) + (L + e M)) * L ^ k := by
        conv => rhs; rw [Nat.add_mul]
        ac_rfl
      _ = _ := by congr 1; omega
  have hid : ((L : Int) ^ (L - 1) * m M ^ ((L ^ k * L) * (L - 1))) *
      (H M p q 0 ^ (L - 1) * (2 * (L : Int)) ^ (k * (L - 1)) * m M ^ ((L + e M) * L ^ k)) =
      ((L : Int) ^ (L - 1) * H M p q 0 ^ (L - 1)) *
        ((2 * (L : Int)) ^ (L - 1)) ^ k * m M ^ ((L * L + e M) * L ^ k) := by
    rw [int_pow_mul, Nat.mul_comm (L - 1) k, ← he, int_pow_add]; ac_rfl
  rw [hid] at ht
  exact Int.le_trans hp ht

end CollatzLab.Morphism
