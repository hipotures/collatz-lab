import CollatzLab.MorphismHeight
import CollatzLab.LeadingCoefficient

/-! Constant-first integer polynomial pairs and exact finite convolution. -/
namespace CollatzLab
/-- Only indices `0,...,degree` are used. Higher function values are ignored. -/
structure PolynomialPair where
  degree : Nat
  p0 : Nat → Int
  p1 : Nat → Int

namespace PolynomialPair
open Family

def cutoff (d : Nat) (p : Nat → Int) (n : Nat) : Int := if n ≤ d then p n else 0

def shift (v : Nat → Int) (i n : Nat) : Int := if n < i then 0 else v (n - i)

/-- Sum of the first `count` terms of the coefficient convolution. -/
def convolution (p v : Nat → Int) : Nat → Nat → Int
  | 0, _ => 0
  | count + 1, n => convolution p v count n + p count * shift v count n

def residual (P : PolynomialPair) (v : Nat → Int) (n : Nat) : Int :=
  cutoff P.degree P.p0 n + convolution P.p1 v (P.degree + 1) n

/-- Homogeneous evaluation of degree `d`, including trailing zero coefficients. -/
def eval (p : Nat → Int) (a b : Int) (d : Nat) : Int := sum p a b (d + 1)

def tail (p v : Nat → Int) (a b : Int) (n : Nat) : Nat → Int
  | 0 => 0
  | d + 1 => b * tail p v a b n d +
      p (d + 1) * sum (fun j => v (n - (d + 1) + j)) a b (d + 1)

def E {L : Nat} (M : Morphism.Images L) (P : PolynomialPair) (p q : Int) (k : Nat) : Int :=
  Morphism.D M q k * eval P.p0 (Morphism.a M k) (Morphism.b M k) P.degree +
    eval P.p1 (Morphism.a M k) (Morphism.b M k) P.degree * Morphism.u M p q k

def First (P : PolynomialPair) (v : Nat → Int) (N : Nat) : Prop :=
  (∀ n, n < N → P.residual v n = 0) ∧ P.residual v N ≠ 0

def Gap {L : Nat} (M : Morphism.Images L) (P : PolynomialPair) (N : Nat) : Prop :=
  Morphism.m M ^ (P.degree * (L - 1) + L + Morphism.e M) <
    (2 : Int) ^ (L * (L - 1) * N)

theorem sum_scale (c : Int) (v : Nat → Int) (a b : Int) : ∀ n,
    sum (fun j => c * v j) a b n = c * sum v a b n
  | 0 => by simp [sum]
  | n + 1 => by rw [sum, sum_scale, sum]; family_ring

theorem sum_cutoff (p : Nat → Int) (a b : Int) (d n : Nat) (hn : d + 1 ≤ n) :
    sum (cutoff d p) a b n = b ^ (n - (d + 1)) * eval p a b d := by
  have h0 : sum (fun j => cutoff d p (d + 1 + j)) a b (n - (d + 1)) = 0 := by
    rw [Morphism.sum_ext _ (fun _ => 0) a b _ (by intro j _; simp [cutoff]; omega), Morphism.sum_zero]
  have hfirst : sum (cutoff d p) a b (d + 1) = eval p a b d := by
    apply Morphism.sum_ext
    intro j hj
    simp [cutoff, show j ≤ d by omega]
  have hh := prefix_segment (cutoff d p) a b (d + 1) (n - (d + 1))
  rw [Nat.add_sub_of_le hn, h0, Int.mul_zero, Int.add_zero, hfirst] at hh
  exact hh

theorem convolution_identity (p v : Nat → Int) (a b : Int) (n : Nat) :
    ∀ d, d ≤ n →
    eval p a b d * sum v a b n =
      b ^ d * sum (convolution p v (d + 1)) a b n + a ^ n * tail p v a b n d
  | 0, _ => by
    have he : convolution p v 1 = fun j => p 0 * v j := by
      funext j
      simp [convolution, shift]
    rw [he, sum_scale]
    simp [eval, sum, tail, Int.pow_zero]
  | d + 1, hd => by
    have hi := convolution_identity p v a b n d (by omega)
    have hiB := congrArg (fun x : Int => b * x) hi
    have hs : sum (convolution p v (d + 1 + 1)) a b n =
        sum (convolution p v (d + 1)) a b n +
          p (d + 1) * sum (shift v (d + 1)) a b n := by
      change sum (fun j => convolution p v (d + 1) j + p (d + 1) * shift v (d + 1) j) a b n = _
      rw [Morphism.sum_add, sum_scale]
    have hshift : sum (shift v (d + 1)) a b n = a ^ (d + 1) * sum v a b (n - (d + 1)) := by
      have hh := Morphism.shifted_sum v a b (d + 1) (n - (d + 1))
      rw [Nat.add_sub_of_le hd] at hh
      exact hh
    have hp := prefix_segment v a b (n - (d + 1)) (d + 1)
    rw [Nat.sub_add_cancel hd] at hp
    have ha : a ^ (d + 1) * a ^ (n - (d + 1)) = a ^ n := by
      rw [← int_pow_add, Nat.add_sub_of_le hd]
    have ht := congrArg (fun x : Int => p (d + 1) * a ^ (d + 1) * x) hp
    have ht' := congrArg (fun x : Int => p (d + 1) * x *
      sum (fun j => v (n - (d + 1) + j)) a b (d + 1)) ha
    change (b * eval p a b d + p (d + 1) * a ^ (d + 1)) * sum v a b n = _
    rw [hs, hshift, tail, Int.pow_succ b]
    rw [Int.pow_succ b] at ht
    family_ring

/-- The entire omitted part is an explicit multiple of `a^n`. -/
theorem residual_identity (P : PolynomialPair) (v : Nat → Int) (a b : Int) (n : Nat)
    (hn : P.degree + 1 ≤ n) :
    b ^ (n - 1) * eval P.p0 a b P.degree +
      eval P.p1 a b P.degree * sum v a b n =
        b ^ P.degree * sum (P.residual v) a b n +
          a ^ n * tail P.p1 v a b n P.degree := by
  have hc := convolution_identity P.p1 v a b n P.degree (by omega)
  have hs : sum (P.residual v) a b n =
      b ^ (n - (P.degree + 1)) * eval P.p0 a b P.degree +
        sum (convolution P.p1 v (P.degree + 1)) a b n := by
    unfold residual
    rw [Morphism.sum_add, sum_cutoff _ _ _ _ _ hn]
  have hb : b ^ P.degree * b ^ (n - (P.degree + 1)) = b ^ (n - 1) := by
    rw [← int_pow_add, show P.degree + (n - (P.degree + 1)) = n - 1 by omega]
  have hb' := congrArg (fun x : Int => x * eval P.p0 a b P.degree) hb
  rw [hs]
  family_ring

/-- The tower form has the expected first coefficient before cancelling odd powers. -/
theorem tower_residual {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (P : PolynomialPair) (N : Nat) (hN : P.degree ≤ N)
    (hzero : ∀ j, j < N → P.residual (Morphism.parityWord M) j = 0)
    {p q : Int} (hr : RealizesWord p q (Morphism.parityWord M)) (k : Nat) :
    ∃ T : Int, Morphism.b M k ^ N * E M P p q k = Morphism.a M k ^ N *
      (Morphism.D M q k * Morphism.b M k ^ P.degree * P.residual (Morphism.parityWord M) N +
        Morphism.a M k * T) := by
  let aa := Morphism.a M k
  let bb := Morphism.b M k
  let dd := Morphism.D M q k
  have hsum0 : sum (P.residual (Morphism.parityWord M)) aa bb N = 0 := by
    rw [Morphism.sum_ext _ (fun _ => 0) aa bb _ hzero, Morphism.sum_zero]
  have hsum1 : sum (P.residual (Morphism.parityWord M)) aa bb (N + 1) =
      aa ^ N * P.residual (Morphism.parityWord M) N := by
    rw [sum, hsum0]; simp [Int.mul_comm]
  have hi := residual_identity P (Morphism.parityWord M) aa bb (N + 1) (by omega)
  rw [hsum1, show N + 1 - 1 = N by omega, Int.pow_succ aa] at hi
  rcases Morphism.tower_congruence hL M h1 hw hd hr k (N + 1) (by omega) with ⟨r, ht⟩
  rw [show N + 1 - 1 = N by omega, Int.pow_succ] at ht
  refine ⟨dd * tail P.p1 (Morphism.parityWord M) aa bb (N + 1) P.degree +
    eval P.p1 aa bb P.degree * r, ?_⟩
  have hiD := congrArg (fun x : Int => dd * x) hi
  have htP := congrArg (fun x : Int => eval P.p1 aa bb P.degree * x) ht
  change bb ^ N * (dd * eval P.p0 aa bb P.degree +
    eval P.p1 aa bb P.degree * Morphism.u M p q k) = _
  change bb ^ N * Morphism.u M p q k - dd * sum (Morphism.parityWord M) aa bb (N + 1) =
    aa ^ N * aa * r at ht
  change eval P.p1 aa bb P.degree *
    (bb ^ N * Morphism.u M p q k - dd * sum (Morphism.parityWord M) aa bb (N + 1)) =
      eval P.p1 aa bb P.degree * (aa ^ N * aa * r) at htP
  dsimp [aa, bb, dd] at *
  family_ring

/-- Divisibility by `a^N` holds even at the discarded initial levels. -/
theorem tower_divisibility {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (P : PolynomialPair) (N : Nat) (hN : P.degree ≤ N)
    (hzero : ∀ j, j < N → P.residual (Morphism.parityWord M) j = 0)
    {p q : Int} (hr : RealizesWord p q (Morphism.parityWord M)) (k : Nat) :
    Morphism.a M k ^ N ∣ E M P p q k := by
  rcases tower_residual hL M h1 hw hd P N hN hzero hr k with ⟨T, he⟩
  exact IsBezout.dvd_of_dvd_mul_left (IsBezout.pow (Morphism.ab_coprime M k) N N) ⟨_, he⟩

theorem odd_multiple_of_exact (x : Int) (v : Nat)
    (hd : (2 : Int) ^ v ∣ x) (hn : ¬ (2 : Int) ^ (v + 1) ∣ x) :
    ∃ c : Int, c % 2 = 1 ∧ x = (2 : Int) ^ v * c := by
  rcases hd with ⟨c, hc⟩
  refine ⟨c, ?_, hc⟩
  by_cases ho : c % 2 = 1
  · exact ho
  · have heven : c = 2 * (c / 2) := by omega
    apply False.elim
    apply hn
    refine ⟨c / 2, ?_⟩
    calc
      x = (2 : Int) ^ v * c := hc
      _ = (2 : Int) ^ v * (2 * (c / 2)) := congrArg (fun z : Int => (2 : Int) ^ v * z) heven
      _ = (2 : Int) ^ (v + 1) * (c / 2) := by rw [Int.pow_succ]; ac_rfl

/-- Cancelling any signed odd factor preserves an exact power-of-two valuation. -/
theorem cancel_odd_multiple (b x : Int) (hb : b % 2 = 1) (v : Nat)
    (h : ∃ c : Int, c % 2 = 1 ∧ b * x = (2 : Int) ^ v * c) :
    ∃ c : Int, c % 2 = 1 ∧ x = (2 : Int) ^ v * c := by
  rcases h with ⟨c, hc, he⟩
  have hbez : IsBezout 2 b := ⟨-(b / 2), 1, by omega⟩
  rcases IsBezout.dvd_of_dvd_mul_left (IsBezout.pow_left hbez v) ⟨c, he⟩ with ⟨t, ht⟩
  refine ⟨t, ?_, ht⟩
  have hp := pow_pos_of_pos (x := 2) (by decide) v
  have hcancel : b * t = c := by
    apply Int.eq_of_mul_eq_mul_left (a := (2 : Int) ^ v) (by omega)
    rw [← he, ht]; ac_rfl
  have hm := congrArg (fun x : Int => x % 2) hcancel
  dsimp only at hm
  rw [Int.mul_emod, hb, Int.one_mul, hc] at hm
  omega

/-- Exact non-unit valuation, valid precisely after the tower spacing exceeds `v`. -/
theorem valuation {L : Nat} (hL : 2 ≤ L) (M : Morphism.Images L)
    (h1 : Morphism.image M true 0 = true)
    (hw : Morphism.weight (Morphism.image M false) L = Morphism.weight (Morphism.image M true) L)
    (hd : M.zero ≠ M.one) (P : PolynomialPair) (N v : Nat) (hN : P.degree ≤ N)
    (hzero : ∀ j, j < N → P.residual (Morphism.parityWord M) j = 0)
    (c : Int) (hc : c % 2 = 1)
    (hlead : P.residual (Morphism.parityWord M) N = (2 : Int) ^ v * c)
    {p q : Int} (hr : RealizesWord p q (Morphism.parityWord M)) (k : Nat)
    (hk : v < L ^ (k + 1)) :
    let exponent := N * L ^ (k + 1) + v
    E M P p q k ≠ 0 ∧ (2 : Int) ^ exponent ∣ E M P p q k ∧
      ¬ (2 : Int) ^ (exponent + 1) ∣ E M P p q k ∧ (2 : Int) ^ exponent ≤ absInt (E M P p q k) := by
  rcases tower_residual hL M h1 hw hd P N hN hzero hr k with ⟨T, he⟩
  have ha : Morphism.a M k = (2 : Int) ^ (L ^ (k + 1)) := by
    rw [Morphism.a_closed, Nat.pow_succ, Nat.mul_comm]
  have hodd := odd_mul_odd (odd_mul_odd (Morphism.denominator_odd hL M hw hd q hr.2.1 k)
    (odd_pow (Morphism.ab_props hL M k).2.2.2 P.degree)) hc
  let c' := Morphism.D M q k * Morphism.b M k ^ P.degree * c
  have hval := nonunit_leading_valuation v (L ^ (k + 1)) hk c' T hodd
  rcases odd_multiple_of_exact _ v hval.2.1 hval.2.2.1 with ⟨t, ht, het⟩
  have hinner : Morphism.D M q k * Morphism.b M k ^ P.degree *
      P.residual (Morphism.parityWord M) N + Morphism.a M k * T =
        (2 : Int) ^ v * c' + (2 : Int) ^ (L ^ (k + 1)) * T := by
    rw [hlead, ha]; dsimp [c']; ac_rfl
  rw [hinner, het, ha, int_pow_mul] at he
  have he' : Morphism.b M k ^ N * E M P p q k =
      (2 : Int) ^ (N * L ^ (k + 1) + v) * t := by
    rw [int_pow_add, Nat.mul_comm N]
    rw [he]
    ac_rfl
  apply odd_multiple_bounds
  exact cancel_odd_multiple _ _ (odd_pow (Morphism.ab_props hL M k).2.2.2 N) _ ⟨t, ht, he'⟩

end PolynomialPair
end CollatzLab
