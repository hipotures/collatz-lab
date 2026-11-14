import CollatzLab.EqualWeight

/-! Finite periodic-control certificates, with a period independent of block length. -/
namespace CollatzLab

structure PeriodicControl where
  period : Nat
  block : Fin period → Bool
  order : Nat

namespace PeriodicControl
open CollatzLab.Family

def coeff (C : PeriodicControl) (j : Nat) : Int :=
  if h : j < C.period then Morphism.bit (C.block ⟨j, h⟩) else 0
def Q (C : PeriodicControl) (a b : Int) := sum C.coeff a b C.period
def residual (C : PeriodicControl) (v : Nat → Int) (j : Nat) :=
  C.coeff j - v j + if j < C.period then 0 else v (j - C.period)
def tail (C : PeriodicControl) (v : Nat → Int) (a b : Int) :=
  sum (fun j => v (C.order + 1 - C.period + j)) a b C.period
def E {L : Nat} (M : Morphism.Images L) (C : PeriodicControl) (p q : Int) (k : Nat) :=
  Morphism.D M q k * (Morphism.b M k * C.Q (Morphism.a M k) (Morphism.b M k)) -
    (Morphism.b M k ^ C.period - Morphism.a M k ^ C.period) * Morphism.u M p q k

/-- All conditions involve a finite prefix, and are independently kernel checkable. -/
def Valid {L : Nat} (M : Morphism.Images L) (C : PeriodicControl) : Prop :=
  1 ≤ C.period ∧ C.period ≤ C.order ∧
    (∀ j, j < C.order → Morphism.parityWord M j = C.coeff (j % C.period)) ∧
    (C.coeff (C.order % C.period) - Morphism.parityWord M C.order) % 2 = 1

def Gap {L : Nat} (M : Morphism.Images L) (C : PeriodicControl) : Prop :=
  (2 : Int) ^ (L * (L - 1) * C.order) >
    Morphism.m M ^ (C.period * (L - 1) + L + Morphism.e M)

theorem coeff_outside (C : PeriodicControl) (j : Nat) (hj : C.period ≤ j) : C.coeff j = 0 := by
  simp [coeff, show ¬ j < C.period by omega]

theorem image_sum_extension (C : PeriodicControl) (a b : Int) (n : Nat) (hn : C.period ≤ n) :
    sum C.coeff a b n = b ^ (n - C.period) * C.Q a b := by
  have h0 : sum (fun j => C.coeff (C.period + j)) a b (n - C.period) = 0 := by
    rw [Morphism.sum_ext _ (fun _ => 0) a b _ (by intro j _; exact coeff_outside C _ (by omega)), Morphism.sum_zero]
  have hh := prefix_segment C.coeff a b C.period (n - C.period)
  rw [Nat.add_sub_of_le hn, h0, Int.mul_zero, Int.add_zero] at hh
  exact hh

theorem residual_identity (C : PeriodicControl) (v : Nat → Int) (a b : Int)
    (hPN : C.period ≤ C.order) :
    b ^ C.order * (b * C.Q a b) - (b ^ C.period - a ^ C.period) * sum v a b (C.order + 1) =
      b ^ C.period * sum (C.residual v) a b (C.order + 1) + a ^ (C.order + 1) * C.tail v a b := by
  have hn : C.period ≤ C.order + 1 := by omega
  have hsum : sum (C.residual v) a b (C.order + 1) =
      b ^ (C.order + 1 - C.period) * C.Q a b - sum v a b (C.order + 1) +
        a ^ C.period * sum v a b (C.order + 1 - C.period) := by
    unfold residual
    rw [Morphism.sum_add, Morphism.sum_sub, image_sum_extension C a b (C.order + 1) hn]
    have hh := Morphism.shifted_sum v a b C.period (C.order + 1 - C.period)
    rw [Nat.add_sub_of_le hn] at hh
    exact congrArg (fun x : Int => b ^ (C.order + 1 - C.period) * C.Q a b - sum v a b (C.order + 1) + x) hh
  have htail := prefix_segment v a b (C.order + 1 - C.period) C.period
  rw [show C.order + 1 - C.period + C.period = C.order + 1 by omega] at htail
  have hb : b ^ C.period * b ^ (C.order + 1 - C.period) = b ^ (C.order + 1) := by
    rw [← int_pow_add, Nat.add_sub_of_le hn]
  have ha : a ^ C.period * a ^ (C.order + 1 - C.period) = a ^ (C.order + 1) := by
    rw [← int_pow_add, Nat.add_sub_of_le hn]
  have htail' := congrArg (fun x : Int => a ^ C.period * x) htail
  have hb' : b ^ C.order * (b * C.Q a b) = b ^ (C.order + 1) * C.Q a b := by rw [Int.pow_succ]; ac_rfl
  rw [hsum, hb']
  unfold tail
  have hp := congrArg (fun x : Int => x * C.Q a b) hb
  have ht := congrArg (fun x : Int => x * sum (fun j => v (C.order + 1 - C.period + j)) a b C.period) ha
  family_ring

theorem residual_first {L : Nat} (M : Morphism.Images L) (C : PeriodicControl) (hc : C.Valid M) :
    (∀ j, j < C.order → C.residual (Morphism.parityWord M) j = 0) ∧
      C.residual (Morphism.parityWord M) C.order % 2 = 1 := by
  have hmod : ∀ j, C.period ≤ j → (j - C.period) % C.period = j % C.period := by
    intro j hj
    have he : C.period + (j - C.period) = j := by omega
    conv => rhs; rw [← he]
    simp
  constructor
  · intro j hj
    by_cases hs : j < C.period
    · unfold residual
      rw [if_pos hs, hc.2.2.1 j hj, Nat.mod_eq_of_lt hs]
      omega
    · have hshift : j - C.period < C.order := by have := hc.1; omega
      unfold residual
      rw [if_neg hs, coeff_outside C j (by omega), hc.2.2.1 j hj,
        hc.2.2.1 (j - C.period) hshift, hmod j (by omega)]
      omega
  · have hp := hc.2.2.1 (C.order - C.period) (by have := hc.1; have := hc.2.1; omega)
    rw [hmod C.order hc.2.1] at hp
    unfold residual
    rw [if_neg (by have := hc.2.1; omega), coeff_outside C C.order hc.2.1, hp]
    have hh := hc.2.2.2
    omega

theorem odd_multiple {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (C : PeriodicControl) (hc : C.Valid M)
    {p q : Int} (hr : RealizesWord p q (Morphism.parityWord M)) (k : Nat) :
    ∃ Q' : Int, Q' % 2 = 1 ∧ E M C p q k = Morphism.a M k ^ C.order * Q' := by
  let aa := Morphism.a M k
  let bb := Morphism.b M k
  let dd := Morphism.D M q k
  let vv := Morphism.u M p q k
  have hfirst := residual_first M C hc
  have hsum0 : sum (C.residual (Morphism.parityWord M)) aa bb C.order = 0 := by
    rw [Morphism.sum_ext _ (fun _ => 0) aa bb _ hfirst.1, Morphism.sum_zero]
  have hp := C.residual_identity (Morphism.parityWord M) aa bb hc.2.1
  have hsum1 : sum (C.residual (Morphism.parityWord M)) aa bb (C.order + 1) =
      aa ^ C.order * C.residual (Morphism.parityWord M) C.order := by
    rw [sum, hsum0]; simp [Int.mul_comm]
  rw [hsum1, Int.pow_succ aa] at hp
  change bb ^ C.order * (bb * C.Q aa bb) - (bb ^ C.period - aa ^ C.period) *
    Morphism.pre M aa bb (C.order + 1) = _ at hp
  rcases Morphism.tower_congruence hL M h1 hw hd hr k (C.order + 1) (by omega) with ⟨r, hh⟩
  rw [show C.order + 1 - 1 = C.order by omega, Int.pow_succ] at hh
  let T := dd * C.tail (Morphism.parityWord M) aa bb - (bb ^ C.period - aa ^ C.period) * r
  have hpD := congrArg (fun x : Int => dd * x) hp
  have hrP := congrArg (fun x : Int => (bb ^ C.period - aa ^ C.period) * x) hh
  have hfact : bb ^ C.order * E M C p q k = aa ^ C.order *
      (dd * bb ^ C.period * C.residual (Morphism.parityWord M) C.order + aa * T) := by
    change bb ^ C.order * vv - dd * Morphism.pre M aa bb (C.order + 1) = aa ^ C.order * aa * r at hh
    change (bb ^ C.period - aa ^ C.period) *
      (bb ^ C.order * vv - dd * Morphism.pre M aa bb (C.order + 1)) =
        (bb ^ C.period - aa ^ C.period) * (aa ^ C.order * aa * r) at hrP
    change bb ^ C.order * (dd * (bb * C.Q aa bb) - (bb ^ C.period - aa ^ C.period) * vv) = _
    dsimp [T]
    family_ring
  have hbez : IsBezout (aa ^ C.order) (bb ^ C.order) := IsBezout.pow (Morphism.ab_coprime M k) _ _
  rcases IsBezout.dvd_of_dvd_mul_left hbez ⟨_, hfact⟩ with ⟨Q', hQ⟩
  refine ⟨Q', ?_, hQ⟩
  have hpos : 0 < aa ^ C.order := pow_pos_of_pos (Morphism.ab_props hL M k).1 _
  have hcancel : bb ^ C.order * Q' = dd * bb ^ C.period *
      C.residual (Morphism.parityWord M) C.order + aa * T := by
    apply Int.eq_of_mul_eq_mul_left (a := aa ^ C.order) (by omega)
    rw [← hfact, hQ]; ac_rfl
  have heven : (aa * T) % 2 = 0 := even_mul (Morphism.ab_props hL M k).2.2.1 T
  have hodd := odd_mul_odd (odd_mul_odd (Morphism.denominator_odd hL M hw hd q hr.2.1 k)
    (odd_pow (Morphism.ab_props hL M k).2.2.2 C.period)) hfirst.2
  change (dd * bb ^ C.period * C.residual (Morphism.parityWord M) C.order) % 2 = 1 at hodd
  have hmod : (bb ^ C.order * Q') % 2 = 1 := by rw [hcancel]; omega
  rw [Int.mul_emod, odd_pow (Morphism.ab_props hL M k).2.2.2, Int.one_mul] at hmod
  omega

theorem valuation {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (C : PeriodicControl) (hc : C.Valid M)
    {p q : Int} (hr : RealizesWord p q (Morphism.parityWord M)) (k : Nat) :
    let exponent := C.order * L ^ (k + 1)
    E M C p q k ≠ 0 ∧ (2 : Int) ^ exponent ∣ E M C p q k ∧
      ¬ (2 : Int) ^ (exponent + 1) ∣ E M C p q k ∧ (2 : Int) ^ exponent ≤ absInt (E M C p q k) := by
  apply odd_multiple_bounds
  rcases odd_multiple hL M h1 hw hd C hc hr k with ⟨Q', ho, he⟩
  refine ⟨Q', ho, ?_⟩
  rw [Morphism.a_closed, int_pow_mul] at he
  have hexp : L * L ^ k * C.order = C.order * L ^ (k + 1) := by rw [Nat.pow_succ]; ac_rfl
  rw [hexp] at he
  exact he

theorem Q_bound (C : PeriodicControl) (hP : 1 ≤ C.period) (a b Mmax : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ Mmax) (hbM : b ≤ Mmax) :
    absInt (C.Q a b) ≤ (C.period : Int) * Mmax ^ (C.period - 1) := by
  have hc : ∀ j, absInt (C.coeff j) ≤ 1 := by
    intro j
    unfold coeff
    split
    · exact Morphism.bit_abs _
    · decide
  have hh := Morphism.sum_bound C.coeff a b Mmax ha hb haM hbM hc (C.period - 1)
  rw [show C.period - 1 + 1 = C.period by omega] at hh
  have hcast : (((C.period - 1 : Nat) : Int) + 1) = (C.period : Int) := by omega
  rw [hcast] at hh
  exact hh

theorem form_bound {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (C : PeriodicControl) (hP : 1 ≤ C.period) (p q : Int) (k : Nat) :
    absInt (E M C p q k) ≤ (C.period : Int) * Morphism.mk M k ^ C.period * Morphism.H M p q k := by
  let aa := Morphism.a M k
  let bb := Morphism.b M k
  let mm := Morphism.mk M k
  have ha : 0 ≤ aa := by have := (Morphism.ab_props hL M k).1; dsimp [aa]; omega
  have hb : 0 ≤ bb := by have := (Morphism.ab_props hL M k).2.1; dsimp [bb]; omega
  have haM : aa ≤ mm := (Morphism.ab_le_mk hL M k).2.2.1
  have hbM : bb ≤ mm := (Morphism.ab_le_mk hL M k).2.2.2
  have hQ := Q_bound C hP aa bb mm ha hb haM hbM
  have hdiff := Morphism.difference_bound ha hb haM hbM C.period
  have hh := absInt_sub_le (Morphism.D M q k * (bb * C.Q aa bb))
    ((bb ^ C.period - aa ^ C.period) * Morphism.u M p q k)
  rw [absInt_mul, absInt_mul, absInt_mul, absInt_of_nonneg hb] at hh
  have ht0 := Int.mul_le_mul hbM hQ (absInt_nonneg _) (show 0 ≤ mm by omega)
  have hpow : mm * mm ^ (C.period - 1) = mm ^ C.period := by
    rw [Int.mul_comm, ← Int.pow_succ, show C.period - 1 + 1 = C.period by omega]
  have hid : mm * ((C.period : Int) * mm ^ (C.period - 1)) = (C.period : Int) * mm ^ C.period := by
    rw [← hpow]; ac_rfl
  rw [hid] at ht0
  have ht1 := Int.mul_le_mul_of_nonneg_left ht0 (absInt_nonneg (Morphism.D M q k))
  have hscale := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ (C.period : Int) by omega)
    (pow_nonneg_of_nonneg (show 0 ≤ mm by omega) C.period)
  have ht2 := Int.mul_le_mul_of_nonneg_right (Int.le_trans hdiff (by simpa using hscale))
    (absInt_nonneg (Morphism.u M p q k))
  change absInt (Morphism.D M q k * (bb * C.Q aa bb) -
    (bb ^ C.period - aa ^ C.period) * Morphism.u M p q k) ≤
      (C.period : Int) * mm ^ C.period * (absInt (Morphism.u M p q k) + absInt (Morphism.D M q k))
  family_ring

theorem form_power_bound {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (C : PeriodicControl) (hc : C.Valid M)
    {p q : Int} (hr : RealizesWord p q (Morphism.parityWord M)) (k : Nat) :
    absInt (E M C p q k) ^ (L - 1) ≤
      ((C.period : Int) ^ (L - 1) * Morphism.H M p q 0 ^ (L - 1)) *
        ((2 * (L : Int)) ^ (L - 1)) ^ k *
          Morphism.m M ^ ((C.period * (L - 1) + L + Morphism.e M) * L ^ k) := by
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
  have hp := pow_le_pow_of_le (absInt_nonneg _) (form_bound hL M C hc.1 p q k) (L - 1)
  dsimp [Morphism.mk] at hp
  simp only [mul_pow, int_pow_mul] at hp
  have hco : 0 ≤ (C.period : Int) ^ (L - 1) * Morphism.m M ^ ((L ^ k * C.period) * (L - 1)) :=
    Int.mul_nonneg (pow_nonneg_of_nonneg (by omega) _) (pow_nonneg_of_nonneg (by omega) _)
  have ht := Int.mul_le_mul_of_nonneg_left hheight hco
  have he : (L ^ k * C.period) * (L - 1) + (L + Morphism.e M) * L ^ k =
      (C.period * (L - 1) + L + Morphism.e M) * L ^ k := by
    calc
      _ = (C.period * (L - 1) + (L + Morphism.e M)) * L ^ k := by
        conv => rhs; rw [Nat.add_mul]
        ac_rfl
      _ = _ := by rw [Nat.add_assoc]
  have hid : ((C.period : Int) ^ (L - 1) * Morphism.m M ^ ((L ^ k * C.period) * (L - 1))) *
      (Morphism.H M p q 0 ^ (L - 1) * (2 * (L : Int)) ^ (k * (L - 1)) *
        Morphism.m M ^ ((L + Morphism.e M) * L ^ k)) =
      ((C.period : Int) ^ (L - 1) * Morphism.H M p q 0 ^ (L - 1)) *
        ((2 * (L : Int)) ^ (L - 1)) ^ k *
          Morphism.m M ^ ((C.period * (L - 1) + L + Morphism.e M) * L ^ k) := by
    rw [int_pow_mul, Nat.mul_comm (L - 1) k, ← he, int_pow_add]; ac_rfl
  rw [hid] at ht
  exact Int.le_trans hp ht

end PeriodicControl

/-- A finite periodic-control certificate can improve on the image-period criterion. -/
theorem no_rational_seed_with_periodic_control {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (C : PeriodicControl) (hc : C.Valid M) (hgap : C.Gap M) (p q : Int) :
    ¬ RealizesWord p q (Morphism.parityWord M) := by
  intro hr
  let AA := (2 : Int) ^ (L * (L - 1) * C.order)
  let BB := Morphism.m M ^ (C.period * (L - 1) + L + Morphism.e M)
  let K := (C.period : Int) ^ (L - 1) * Morphism.H M p q 0 ^ (L - 1)
  let Dbase := (2 * (L : Int)) ^ (L - 1)
  have hm : 1 ≤ Morphism.m M := (Morphism.ab_le_mk hL M 0).1
  have hBB : 1 ≤ BB := Family.pow_ge_one hm _
  have hAB : BB < AA := hgap
  have hH := Morphism.height_positive hL M hw hd hr 0
  have hK : 1 ≤ K := by
    have h0 := Family.pow_ge_one (x := (C.period : Int)) (by have := hc.1; omega) (L - 1)
    have h1 := Family.pow_ge_one hH (L - 1)
    have hh := Int.mul_le_mul h0 h1 (by decide : (0 : Int) ≤ 1)
      (pow_nonneg_of_nonneg (show 0 ≤ (C.period : Int) by omega) (L - 1))
    simpa [K] using hh
  have hD : 1 ≤ Dbase := Family.pow_ge_one (by omega) _
  apply no_doubly_exponential_bound L hL AA BB K Dbase hBB hAB hK hD
  intro k
  have hv := (PeriodicControl.valuation hL M h1 hw hd C hc hr k).2.2.2
  have hpow := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := 2) (by decide) (C.order * L ^ (k + 1))) hv (L - 1)
  rw [int_pow_mul] at hpow
  have hexp : (C.order * L ^ (k + 1)) * (L - 1) = (L * (L - 1) * C.order) * L ^ k := by
    rw [Nat.pow_succ]; ac_rfl
  rw [hexp] at hpow
  have haid : AA ^ (L ^ k) = (2 : Int) ^ ((L * (L - 1) * C.order) * L ^ k) := int_pow_mul _ _ _
  have hlo : AA ^ (L ^ k) ≤ absInt (PeriodicControl.E M C p q k) ^ (L - 1) := by rw [haid]; exact hpow
  have hbid : BB ^ (L ^ k) = Morphism.m M ^ ((C.period * (L - 1) + L + Morphism.e M) * L ^ k) := int_pow_mul _ _ _
  have hhi : absInt (PeriodicControl.E M C p q k) ^ (L - 1) ≤ K * Dbase ^ k * BB ^ (L ^ k) := by
    rw [hbid]
    exact PeriodicControl.form_power_bound hL M h1 hw hd C hc hr k
  exact Int.le_trans hlo hhi

theorem no_rational_seed_with_shifted_periodic_control {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (C : PeriodicControl) (hc : C.Valid M) (hgap : C.Gap M) :
    ∀ (t : Nat) (p q : Int), ¬ RealizesWord p q (shiftWord (Morphism.parityWord M) t)
  | 0, p, q, hr => by
    apply no_rational_seed_with_periodic_control hL M h1 hw hd C hc hgap p q
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro j
    simpa [shiftWord] using hr.2.2 j
  | t + 1, p, q, hr =>
    no_rational_seed_with_shifted_periodic_control hL M h1 hw hd C hc hgap t
      (invBranchNum (Morphism.parityWord M t) p q) (invBranchDen (Morphism.parityWord M t) q)
      (realizes_shiftWord_pred (Morphism.parity_binary M t) hr)

end CollatzLab
