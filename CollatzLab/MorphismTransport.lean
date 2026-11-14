import CollatzLab.MorphismOffset
import CollatzLab.FamilyTower

/-! Signed-denominator transport, preserving all powers of the even base. -/
namespace CollatzLab.Morphism
open CollatzLab.Family

def delta {L : Nat} (M : Images L) (a b v d : Int) :=
  (b ^ L - a ^ L) * v - d * b * Q M false a b

theorem first_image_sum {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (a b : Int) : pre M a b L = Q M true a b := by
  apply sum_ext
  intro j hj
  exact congrArg bit (word_first_block hL M h1 j hj)

/-- Factor hypotheses are finite polynomial identities, not seed hypotheses. -/
theorem delta_exact {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (s e : Nat) (hs : s ≤ L) (he : e < L)
    (a b v d G : Int)
    (hG : Gamma M a b = a ^ s * b ^ (L - 1 - e) * G)
    (hc : a ^ L ∣ b ^ (L - 1) * v - d * pre M a b L) :
    a ^ s ∣ delta M a b v d ∧
    a ^ s * (b ^ e * (delta M a b v d / a ^ s)) = b ^ e * delta M a b v d := by
  rcases hc with ⟨r, hr⟩
  rw [first_image_sum hL M h1] at hr
  have hQ : Q M true a b = Q M false a b + Gamma M a b := by unfold Gamma; omega
  have haL : a ^ L = a ^ s * a ^ (L - s) := by
    rw [← int_pow_add, Nat.add_sub_of_le hs]
  have hbL : b * b ^ (L - 1) = b ^ L := by
    rw [Int.mul_comm, ← Int.pow_succ, show L - 1 + 1 = L by omega]
  have hbG : b * Gamma M a b = a ^ s * b ^ (L - e) * G := by
    have heq : b ^ (L - e) = b ^ (L - 1 - e) * b := by
      rw [← Int.pow_succ, show L - 1 - e + 1 = L - e by omega]
    rw [hG, heq]; ac_rfl
  have hh := congrArg (fun x : Int => b * x) hr
  rw [hQ] at hh
  have hdelta : delta M a b v d =
      a ^ s * (a ^ (L - s) * (b * r - v) + d * b ^ (L - e) * G) := by
    unfold delta
    have hbr : b * (b ^ (L - 1) * v) = b ^ L * v := by rw [← hbL]; ac_rfl
    simp only [Int.mul_sub, Int.mul_add] at hh
    rw [hbr] at hh
    have hgamma := congrArg (fun x : Int => d * x) hbG
    rw [haL] at *
    family_ring
  have hd : a ^ s ∣ delta M a b v d := ⟨_, hdelta⟩
  refine ⟨hd, ?_⟩
  have hdiv := Int.ediv_mul_cancel hd
  calc
    a ^ s * (b ^ e * (delta M a b v d / a ^ s)) =
        b ^ e * ((delta M a b v d / a ^ s) * a ^ s) := by ac_rfl
    _ = _ := by rw [hdiv]

/-- Signed `d` avoids absolute-value sign cases; no ordering of `a,b` is needed. -/
theorem congruence_step {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (s e : Nat) (hs : s ≤ L) (he : e < L)
    (a b v d G : Int) (ha : 0 < a) (hbez : IsBezout a b)
    (hG : Gamma M a b = a ^ s * b ^ (L - 1 - e) * G)
    (hc : ∀ n, 1 ≤ n → a ^ n ∣ b ^ (n - 1) * v - d * pre M a b n) :
    let v1 := b ^ e * (delta M a b v d / a ^ s)
    let d1 := d * G * (b ^ L - a ^ L)
    ∀ n, 1 ≤ n → (a ^ L) ^ n ∣
      (b ^ L) ^ (n - 1) * v1 - d1 * pre M (a ^ L) (b ^ L) n := by
  let v1 := b ^ e * (delta M a b v d / a ^ s)
  let d1 := d * G * (b ^ L - a ^ L)
  change ∀ n, 1 ≤ n → (a ^ L) ^ n ∣ (b ^ L) ^ (n - 1) * v1 - d1 * pre M (a ^ L) (b ^ L) n
  have hv : a ^ s * v1 = b ^ e * delta M a b v d :=
    (delta_exact hL M h1 s e hs he a b v d G hG (hc L (by omega))).2
  intro n hn
  let Mlen := L * (n + 1)
  have hM : 1 ≤ Mlen := by
    dsimp [Mlen]; have := Nat.mul_le_mul hL (show 1 ≤ n + 1 by omega); omega
  rcases hc Mlen hM with ⟨r, hr⟩
  have hm := prefix_mahler hL M h1 a b (n + 1)
  have hhr := congrArg (fun x : Int => b * (b ^ L - a ^ L) * x) hr
  have hbM : b * b ^ (Mlen - 1) = b ^ Mlen := by
    rw [Int.mul_comm, ← Int.pow_succ, show Mlen - 1 + 1 = Mlen by omega]
  have hbM2 : b ^ (L - e) * (b ^ L) ^ n * b ^ e = b ^ Mlen := by
    rw [int_pow_mul, ← int_pow_add, ← int_pow_add]
    congr 1
    dsimp [Mlen]; rw [Nat.mul_succ]; omega
  have ht : a ^ s * b ^ (L - e) *
      ((b ^ L) ^ n * v1 - d1 * pre M (a ^ L) (b ^ L) (n + 1)) =
      a ^ Mlen * (b * (b ^ L - a ^ L) * r - d * b * Q M false a b) := by
    have hhr' : b ^ Mlen * (b ^ L - a ^ L) * v - d * b *
        ((b ^ L - a ^ L) * pre M a b Mlen) = a ^ Mlen * (b * (b ^ L - a ^ L) * r) := by
      have hx : b * (b ^ L - a ^ L) * (b ^ (Mlen - 1) * v) =
          b ^ Mlen * (b ^ L - a ^ L) * v := by rw [← hbM]; ac_rfl
      dsimp only at hhr
      rw [Int.mul_sub (b * (b ^ L - a ^ L)), hx] at hhr
      family_ring
    have hhv : a ^ s * b ^ (L - e) * ((b ^ L) ^ n * v1) =
        b ^ Mlen * delta M a b v d := by
      calc
        _ = b ^ (L - e) * (b ^ L) ^ n * (a ^ s * v1) := by ac_rfl
        _ = _ := by rw [hv, ← hbM2]; ac_rfl
    unfold delta at hhv
    change (b ^ L - a ^ L) * pre M a b Mlen = Q M false a b * (b ^ Mlen - a ^ Mlen) +
      Gamma M a b * (b ^ L - a ^ L) * pre M (a ^ L) (b ^ L) (n + 1) at hm
    have hm' := congrArg (fun x : Int => d * b * x) hm
    have hbG : b * Gamma M a b = a ^ s * b ^ (L - e) * G := by
      have heq : b ^ (L - e) = b ^ (L - 1 - e) * b := by
        rw [← Int.pow_succ, show L - 1 - e + 1 = L - e by omega]
      rw [hG, heq]; ac_rfl
    have hbg' := congrArg (fun x : Int => d * (b ^ L - a ^ L) *
      pre M (a ^ L) (b ^ L) (n + 1) * x) hbG
    dsimp [d1]
    rw [Int.mul_sub, hhv]
    family_ring
  have haM : a ^ Mlen = a ^ s * (a ^ L) ^ n * a ^ (L - s) := by
    rw [int_pow_mul, ← int_pow_add, ← int_pow_add]
    congr 1
    dsimp [Mlen]; rw [Nat.mul_succ]; omega
  have hd : a ^ s * (a ^ L) ^ n ∣ a ^ s *
      (b ^ (L - e) * ((b ^ L) ^ n * v1 - d1 * pre M (a ^ L) (b ^ L) (n + 1))) := by
    refine ⟨a ^ (L - s) * (b * (b ^ L - a ^ L) * r - d * b * Q M false a b), ?_⟩
    rw [← Int.mul_assoc, ht, haM]; ac_rfl
  have hd1 := dvd_cancel_left_of_pos (pow_pos_of_pos ha s) hd
  have hbbez : IsBezout ((a ^ L) ^ n) (b ^ (L - e)) := by
    rw [int_pow_mul]; exact IsBezout.pow hbez _ _
  have hd2 := IsBezout.dvd_of_dvd_mul_left hbbez hd1
  have hd3 : (a ^ L) ^ n ∣ b ^ L *
      ((b ^ L) ^ (n - 1) * v1 - d1 * pre M (a ^ L) (b ^ L) n) := by
    rcases hd2 with ⟨r', hr'⟩
    refine ⟨r' + d1 * parityWord M n, ?_⟩
    have hbN : (b ^ L) ^ n = b ^ L * (b ^ L) ^ (n - 1) := by
      rw [Int.mul_comm, ← Int.pow_succ, show n - 1 + 1 = n by omega]
    change (b ^ L) ^ n * v1 - d1 *
      (b ^ L * pre M (a ^ L) (b ^ L) n + parityWord M n * (a ^ L) ^ n) = _ at hr'
    rw [hbN] at hr'
    family_ring
  have hbez1 : IsBezout ((a ^ L) ^ n) (b ^ L) := by
    rw [int_pow_mul]; exact IsBezout.pow hbez _ _
  exact IsBezout.dvd_of_dvd_mul_left hbez1 hd3

end CollatzLab.Morphism
