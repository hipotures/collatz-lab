import CollatzLab.MorphismTower
import CollatzLab.FamilyApprox

/-! The generic periodic residual, its unit coefficient and exact valuation. -/
namespace CollatzLab.Morphism
open CollatzLab.Family

def residual {L : Nat} (M : Images L) (j : Nat) :=
  bit (image M true j) - parityWord M j + if j < L then 0 else parityWord M (j - L)

def tail {L : Nat} (M : Images L) (a b : Int) (n : Nat) :=
  sum (fun j => parityWord M (n + 1 - L + j)) a b L

def E {L : Nat} (M : Images L) (p q : Int) (k : Nat) :=
  D M q k * (b M k * Q M true (a M k) (b M k)) -
    (b M k ^ L - a M k ^ L) * u M p q k

theorem sum_add (v w : Nat → Int) (a b : Int) : ∀ n,
    sum (fun j => v j + w j) a b n = sum v a b n + sum w a b n
  | 0 => by simp [sum]
  | n + 1 => by rw [sum, sum_add, sum, sum]; family_ring

theorem shifted_sum (v : Nat → Int) (a b : Int) (m : Nat) : ∀ n,
    sum (fun j => if j < m then 0 else v (j - m)) a b (m + n) = a ^ m * sum v a b n
  | n => by
    have h0 : sum (fun j => if j < m then 0 else v (j - m)) a b m = 0 := by
      rw [sum_ext _ (fun _ => 0) a b _ (by intro j hj; simp [hj]), sum_zero]
    have hh := prefix_segment (fun j => if j < m then 0 else v (j - m)) a b m n
    rw [h0, Int.mul_zero, Int.zero_add] at hh
    rw [hh]
    congr 1
    apply sum_ext
    intro j _
    simp [show ¬ m + j < m by omega, show m + j - m = j by omega]

theorem image_sum_extension {L : Nat} (M : Images L) (a b : Int) (n : Nat) (hn : L ≤ n) :
    sum (fun j => bit (image M true j)) a b n = b ^ (n - L) * Q M true a b := by
  have h0 : sum (fun j => bit (image M true (L + j))) a b (n - L) = 0 := by
    rw [sum_ext _ (fun _ => 0) a b _ (by intro j _; simp [image, show ¬ L + j < L by omega, bit]), sum_zero]
  have hh := prefix_segment (fun j => bit (image M true j)) a b L (n - L)
  rw [Nat.add_sub_of_le hn, h0, Int.mul_zero, Int.add_zero] at hh
  exact hh

/-- Exact finite residual identity, with the tail beyond its first `n+1` terms. -/
theorem residual_identity {L : Nat} (M : Images L) (a b : Int) (n : Nat) (hn : L ≤ n + 1) :
    b ^ n * (b * Q M true a b) - (b ^ L - a ^ L) * pre M a b (n + 1) =
      b ^ L * sum (residual M) a b (n + 1) + a ^ (n + 1) * tail M a b n := by
  have hsum : sum (residual M) a b (n + 1) =
      b ^ (n + 1 - L) * Q M true a b - pre M a b (n + 1) +
        a ^ L * pre M a b (n + 1 - L) := by
    unfold residual
    rw [sum_add, sum_sub, image_sum_extension M a b (n + 1) hn]
    have hh := shifted_sum (parityWord M) a b L (n + 1 - L)
    rw [Nat.add_sub_of_le hn] at hh
    exact congrArg (fun x : Int => b ^ (n + 1 - L) * Q M true a b - pre M a b (n + 1) + x) hh
  have htail := prefix_segment (parityWord M) a b (n + 1 - L) L
  rw [show n + 1 - L + L = n + 1 by omega] at htail
  have hb : b ^ L * b ^ (n + 1 - L) = b ^ (n + 1) := by
    rw [← int_pow_add, Nat.add_sub_of_le hn]
  have ha : a ^ L * a ^ (n + 1 - L) = a ^ (n + 1) := by
    rw [← int_pow_add, Nat.add_sub_of_le hn]
  have htail' := congrArg (fun x : Int => a ^ L * x) htail
  have hb' : b ^ n * (b * Q M true a b) = b ^ (n + 1) * Q M true a b := by
    rw [Int.pow_succ]; ac_rfl
  rw [hsum, hb']
  unfold tail
  change a ^ L * pre M a b (n + 1) = a ^ L *
    (b ^ L * pre M a b (n + 1 - L) + a ^ (n + 1 - L) *
      sum (fun j => parityWord M (n + 1 - L + j)) a b L) at htail'
  have hp := congrArg (fun x : Int => x * Q M true a b) hb
  have ht := congrArg (fun x : Int => x * sum (fun j => parityWord M (n + 1 - L + j)) a b L) ha
  family_ring

theorem residual_first {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) :
    (∀ j, j < N M → residual M j = 0) ∧ residual M (N M) % 2 = 1 := by
  have hfd := first_disagreement hL M h1 hw hd
  have ht := (t_bounds hL M h1 hw hd).1
  have hmul := Nat.mul_le_mul_left L ht
  have hNL : L ≤ N M := by dsimp [N]; omega
  have hmod : ∀ j, L ≤ j → (j - L) % L = j % L := by
    intro j hj
    have he : L + (j - L) = j := by omega
    conv => rhs; rw [← he]
    simp
  have hbefore : ∀ j, j < N M → parityWord M j = bit (image M true (j % L)) := by
    intro j hj; exact congrArg bit (hfd.1 j hj)
  constructor
  · intro j hj
    by_cases hsmall : j < L
    · unfold residual parityWord
      rw [if_pos hsmall, word_first_block hL M h1 j hsmall]
      omega
    · have hshift : j - L < N M := by omega
      unfold residual
      rw [if_neg hsmall, hbefore j hj, hbefore (j - L) hshift, hmod j (by omega)]
      simp [image, hsmall, bit]
      omega
  · have hshift : N M - L < N M := by omega
    have hp := hbefore (N M - L) hshift
    rw [hmod (N M) hNL] at hp
    unfold residual
    rw [if_neg (by omega : ¬ N M < L), hp]
    have hout : bit (image M true (N M)) = 0 := by simp [image, show ¬ N M < L by omega, bit]
    rw [hout]
    unfold parityWord
    cases h0 : word M (N M) <;> cases h1 : image M true (N M % L) <;>
      simp [h0, h1, bit] at hfd ⊢

theorem odd_multiple {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) (k : Nat) :
    ∃ Q' : Int, Q' % 2 = 1 ∧ E M p q k = a M k ^ N M * Q' := by
  let aa := a M k
  let bb := b M k
  let dd := D M q k
  let vv := u M p q k
  have hfirst := residual_first hL M h1 hw hd
  have hsum0 : sum (residual M) aa bb (N M) = 0 := by
    rw [sum_ext _ (fun _ => 0) aa bb _ hfirst.1, sum_zero]
  have hsum1 : sum (residual M) aa bb (N M + 1) = aa ^ N M * residual M (N M) := by
    rw [sum, hsum0]; simp [Int.mul_comm]
  have ht := (t_bounds hL M h1 hw hd).1
  have hmul := Nat.mul_le_mul_left L ht
  have hNL : L ≤ N M + 1 := by dsimp [N]; omega
  have hp := residual_identity M aa bb (N M) hNL
  rw [hsum1] at hp
  rw [Int.pow_succ aa] at hp
  rcases tower_congruence hL M h1 hw hd hr k (N M + 1) (by omega) with ⟨r, hh⟩
  rw [show N M + 1 - 1 = N M by omega, Int.pow_succ] at hh
  let T := dd * tail M aa bb (N M) - (bb ^ L - aa ^ L) * r
  have hpD := congrArg (fun x : Int => dd * x) hp
  have hrP := congrArg (fun x : Int => (bb ^ L - aa ^ L) * x) hh
  have hfact : bb ^ N M * E M p q k = aa ^ N M *
      (dd * bb ^ L * residual M (N M) + aa * T) := by
    change bb ^ N M * vv - dd * pre M aa bb (N M + 1) = aa ^ N M * aa * r at hh
    change (bb ^ L - aa ^ L) * (bb ^ N M * vv - dd * pre M aa bb (N M + 1)) =
      (bb ^ L - aa ^ L) * (aa ^ N M * aa * r) at hrP
    change bb ^ N M * (dd * (bb * Q M true aa bb) - (bb ^ L - aa ^ L) * vv) = _
    dsimp [T]
    family_ring
  have hbez : IsBezout (aa ^ N M) (bb ^ N M) := IsBezout.pow (ab_coprime M k) _ _
  rcases IsBezout.dvd_of_dvd_mul_left hbez ⟨_, hfact⟩ with ⟨Q', hQ⟩
  refine ⟨Q', ?_, hQ⟩
  have hcancel : bb ^ N M * Q' = dd * bb ^ L * residual M (N M) + aa * T := by
    have hpos : 0 < aa ^ N M := pow_pos_of_pos (ab_props hL M k).1 _
    apply Int.eq_of_mul_eq_mul_left (a := aa ^ N M)
      (by omega)
    rw [← hfact, hQ]; ac_rfl
  have heven : (aa * T) % 2 = 0 := even_mul (ab_props hL M k).2.2.1 T
  have hodd := odd_mul_odd (odd_mul_odd (denominator_odd hL M hw hd q hr.2.1 k)
    (odd_pow (ab_props hL M k).2.2.2 L)) hfirst.2
  change (dd * bb ^ L * residual M (N M)) % 2 = 1 at hodd
  have hmod : (bb ^ N M * Q') % 2 = 1 := by rw [hcancel]; omega
  rw [Int.mul_emod, odd_pow (ab_props hL M k).2.2.2, Int.one_mul] at hmod
  omega

theorem valuation {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) {p q : Int} (hr : RealizesWord p q (parityWord M)) (k : Nat) :
    let exponent := N M * L ^ (k + 1)
    E M p q k ≠ 0 ∧ (2 : Int) ^ exponent ∣ E M p q k ∧
      ¬ (2 : Int) ^ (exponent + 1) ∣ E M p q k ∧ (2 : Int) ^ exponent ≤ absInt (E M p q k) := by
  apply odd_multiple_bounds
  rcases odd_multiple hL M h1 hw hd hr k with ⟨Q', ho, he⟩
  refine ⟨Q', ho, ?_⟩
  rw [a_closed, int_pow_mul] at he
  have hexp : L * L ^ k * N M = N M * L ^ (k + 1) := by rw [Nat.pow_succ]; ac_rfl
  rw [hexp] at he
  exact he

end CollatzLab.Morphism
