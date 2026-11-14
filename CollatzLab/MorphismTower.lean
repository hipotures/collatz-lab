import CollatzLab.MorphismPolynomial

/-! The generic exactly cancelled signed integer tower. -/
namespace CollatzLab.Morphism
open CollatzLab.Family

def kappa {L : Nat} (M : Images L) := (c M false - c M true) / (2 : Int) ^ s M

theorem kappa_spec {L : Nat} (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) : kappa M % 2 = 1 ∧
      c M false - c M true = (2 : Int) ^ s M * kappa M := by
  rcases offsets_odd_multiple M hw hd with ⟨k, ho, he⟩
  have hp := pow_pos_of_pos (x := 2) (by decide) (s M)
  have hk : kappa M = k := by
    unfold kappa
    rw [he, Int.mul_ediv_cancel_left k (by omega)]
  exact ⟨by rw [hk]; exact ho, by rw [hk]; exact he⟩

def a {L : Nat} (M : Images L) : Nat → Int
  | 0 => A L
  | k + 1 => a M k ^ L
def b {L : Nat} (M : Images L) : Nat → Int
  | 0 => B M
  | k + 1 => b M k ^ L
def D {L : Nat} (M : Images L) (q : Int) : Nat → Int
  | 0 => (B M - A L) * kappa M * q
  | k + 1 => D M q k * GammaStar M (a M k) (b M k) * (b M k ^ L - a M k ^ L)
def u {L : Nat} (M : Images L) (p q : Int) : Nat → Int
  | 0 => B M * g M p q 0 / (2 : Int) ^ s M
  | k + 1 => b M k ^ e M * (delta M (a M k) (b M k) (u M p q k) (D M q k) / a M k ^ s M)

theorem ab_props {L : Nat} (hL : 2 ≤ L) (M : Images L) : ∀ k,
    0 < a M k ∧ 0 < b M k ∧ a M k % 2 = 0 ∧ b M k % 2 = 1
  | 0 => ⟨pow_pos_of_pos (by decide) _, pow_pos_of_pos (by decide) _,
      even_pow (x := 2) (by decide) (by omega), odd_pow (x := 3) (by decide) _⟩
  | k + 1 => by
    rcases ab_props hL M k with ⟨ha, hb, hae, hbo⟩
    exact ⟨pow_pos_of_pos ha _, pow_pos_of_pos hb _, even_pow hae (by omega), odd_pow hbo _⟩

theorem ab_coprime {L : Nat} (M : Images L) : ∀ k, IsBezout (a M k) (b M k)
  | 0 => IsBezout.pow (show IsBezout 2 3 from ⟨-1, 1, rfl⟩) L (weight (image M true) L)
  | k + 1 => IsBezout.pow (ab_coprime M k) L L

theorem a_closed {L : Nat} (M : Images L) (k : Nat) : a M k = (2 : Int) ^ (L * L ^ k) := by
  induction k with
  | zero => simp [a, A]
  | succ k ih => dsimp [a]; rw [ih, int_pow_mul, Nat.pow_succ, Nat.mul_assoc]

theorem b_closed {L : Nat} (M : Images L) (k : Nat) : b M k = B M ^ (L ^ k) := by
  induction k with
  | zero => simp [b, int_pow_one]
  | succ k ih => dsimp [b]; rw [ih, int_pow_mul, Nat.pow_succ, Nat.mul_comm (L ^ k) L]

theorem a_base_factor {L : Nat} (M : Images L) (hd : M.zero ≠ M.one) :
    A L = (2 : Int) ^ s M * (2 : Int) ^ (L - s M) := by
  have hs : s M ≤ L := by have := se_bounds M hd; omega
  unfold A
  rw [← int_pow_add, Nat.add_sub_of_le hs]

theorem raw_coefficient {L : Nat} (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) (q : Int) :
    (B M - A L) * (c M false - c M true) * q = (2 : Int) ^ s M * D M q 0 := by
  rw [(kappa_spec M hw hd).2]
  change _ = (2 : Int) ^ s M * ((B M - A L) * kappa M * q)
  ac_rfl

theorem initial_exact {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) :
    (2 : Int) ^ s M * u M p q 0 = B M * g M p q 0 := by
  have hi := base_identity hL M h1 hw hr 1 (by decide)
  simp only [Nat.reduceSub, Int.pow_zero, Int.one_mul, int_pow_one,
    pre, sum, parityWord, word_zero, bit, if_true, Int.mul_zero, Int.add_zero, Int.mul_one] at hi
  rw [raw_coefficient M hw hd, a_base_factor M hd] at hi
  have hv : (2 : Int) ^ s M ∣ B M * g M p q 0 := by
    refine ⟨D M q 0 + (2 : Int) ^ (L - s M) * g M p q 1, ?_⟩
    family_ring
  have hh := Int.ediv_mul_cancel hv
  change (2 : Int) ^ s M * (B M * g M p q 0 / (2 : Int) ^ s M) = _
  rw [Int.mul_comm]
  exact hh

theorem initial_divisibility {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) :
    (2 : Int) ^ s M ∣ g M p q 0 := by
  have hbez : IsBezout ((2 : Int) ^ s M) (B M) :=
    IsBezout.pow (show IsBezout 2 3 from ⟨-1, 1, rfl⟩) (s M) (weight (image M true) L)
  apply IsBezout.dvd_of_dvd_mul_left hbez
  exact ⟨u M p q 0, (initial_exact hL M h1 hw hd hr).symm⟩

theorem normalized_base {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M))
    (n : Nat) (hn : 1 ≤ n) :
    A L ^ n ∣ B M ^ (n - 1) * u M p q 0 - D M q 0 * pre M (A L) (B M) n := by
  have hi := base_identity hL M h1 hw hr (n + 1) (by omega)
  rw [show n + 1 - 1 = n by omega, raw_coefficient M hw hd,
    ← initial_exact hL M h1 hw hd hr] at hi
  have hAp : A L ^ (n + 1) = (2 : Int) ^ s M * A L ^ n * (2 : Int) ^ (L - s M) := by
    rw [Int.pow_succ, a_base_factor M hd]; ac_rfl
  rw [hAp] at hi
  have hcan : B M ^ n * u M p q 0 - D M q 0 * pre M (A L) (B M) (n + 1) =
      A L ^ n * ((2 : Int) ^ (L - s M) * g M p q (n + 1)) := by
    apply Int.eq_of_mul_eq_mul_left (a := (2 : Int) ^ s M)
      (by have := pow_pos_of_pos (x := 2) (by decide) (s M); omega)
    family_ring
  have hbN : B M ^ n = B M * B M ^ (n - 1) := by
    rw [Int.mul_comm, ← Int.pow_succ, show n - 1 + 1 = n by omega]
  have hdiv : A L ^ n ∣ B M *
      (B M ^ (n - 1) * u M p q 0 - D M q 0 * pre M (A L) (B M) n) := by
    refine ⟨(2 : Int) ^ (L - s M) * g M p q (n + 1) + D M q 0 * parityWord M n, ?_⟩
    change B M ^ n * u M p q 0 - D M q 0 *
      (B M * pre M (A L) (B M) n + parityWord M n * A L ^ n) = _ at hcan
    rw [hbN] at hcan
    family_ring
  have hbez : IsBezout (A L ^ n) (B M) := by
    dsimp [A, B]
    rw [int_pow_mul]
    exact IsBezout.pow (show IsBezout 2 3 from ⟨-1, 1, rfl⟩) _ _
  exact IsBezout.dvd_of_dvd_mul_left hbez hdiv

theorem denominator_odd {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) (q : Int) (hq : q % 2 = 1) : ∀ k, D M q k % 2 = 1
  | 0 => by
    have hp := ab_props hL M 0
    have hdiff : (B M - A L) % 2 = 1 := by
      have he : A L % 2 = 0 := hp.2.2.1
      have ho : B M % 2 = 1 := hp.2.2.2
      omega
    exact odd_mul_odd (odd_mul_odd hdiff (kappa_spec M hw hd).1) hq
  | k + 1 => by
    have hp := ab_props hL M k
    have hdiff : (b M k ^ L - a M k ^ L) % 2 = 1 := by
      have he := even_pow hp.2.2.1 (n := L) (by omega)
      have ho := odd_pow hp.2.2.2 L
      omega
    exact odd_mul_odd (odd_mul_odd (denominator_odd hL M hw hd q hq k)
      (gammaStar_odd M hd _ _ hp.2.2.1 hp.2.2.2).1) hdiff

theorem tower_congruence {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) :
    ∀ k n, 1 ≤ n → a M k ^ n ∣ b M k ^ (n - 1) * u M p q k - D M q k * pre M (a M k) (b M k) n
  | 0, n, hn => normalized_base hL M h1 hw hd hr n hn
  | k + 1, n, hn => congruence_step hL M h1 (s M) (e M)
      (by have := se_bounds M hd; omega) (se_bounds M hd).2
      (a M k) (b M k) (u M p q k) (D M q k) (GammaStar M (a M k) (b M k))
      (ab_props hL M k).1 (ab_coprime M k) (gamma_factor M hd _ _)
      (tower_congruence hL M h1 hw hd hr k) n hn

theorem tower_exact {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) (k : Nat) :
    a M k ^ s M ∣ delta M (a M k) (b M k) (u M p q k) (D M q k) ∧
    a M k ^ s M * u M p q (k + 1) =
      b M k ^ e M * delta M (a M k) (b M k) (u M p q k) (D M q k) :=
  delta_exact hL M h1 (s M) (e M) (by have := se_bounds M hd; omega) (se_bounds M hd).2
    _ _ _ _ _ (gamma_factor M hd _ _) (tower_congruence hL M h1 hw hd hr k L (by omega))

end CollatzLab.Morphism
