import CollatzLab.RepeatedPrefix

/-! Finite compatibility and the limitation of eliminating a seed from two returns. -/
namespace CollatzLab
open Morphism

def cycleCoeff (v : Nat → Bool) (m : Nat) : Int :=
  (2 : Int) ^ m - (3 : Int) ^ weight v m

def returnDet (v : Nat → Bool) (m n : Nat) : Int :=
  cycleCoeff v m * offset v n - cycleCoeff v n * offset v m

theorem cycleCoeff_odd (v : Nat → Bool) (m : Nat) (hm : 1 ≤ m) :
    cycleCoeff v m % 2 = 1 := by
  have := Family.even_pow (x := (2 : Int)) (by decide) hm
  have := odd_pow (x := (3 : Int)) (by decide) (weight v m)
  unfold cycleCoeff
  omega

/-- The sign agrees with a2*E1-a1*E2 = (a1*c2-a2*c1)*q. -/
theorem returnDet_elimination (v : Nat → Bool) (m n : Nat) (p q : Int) :
    cycleCoeff v n * prefixCycleForm v m p q -
      cycleCoeff v m * prefixCycleForm v n p q = returnDet v m n * q := by
  unfold returnDet prefixCycleForm cycleCoeff
  family_ring

/-- Cancellation uses only oddness of q; its sign and reducedness are irrelevant. -/
theorem returnDet_of_forms (v : Nat → Bool) (m n K : Nat) (p q : Int)
    (hq : q % 2 = 1)
    (hm : (2 : Int) ^ K ∣ prefixCycleForm v m p q)
    (hn : (2 : Int) ^ K ∣ prefixCycleForm v n p q) :
    (2 : Int) ^ K ∣ returnDet v m n := by
  rcases hm with ⟨u, hu⟩
  rcases hn with ⟨z, hz⟩
  have he := returnDet_elimination v m n p q
  have hd : (2 : Int) ^ K ∣ q * returnDet v m n := by
    refine ⟨cycleCoeff v n * u - cycleCoeff v m * z, ?_⟩
    rw [hu, hz] at he
    family_ring
  have hb : IsBezout 2 q := ⟨-(q / 2), 1, by omega⟩
  exact (IsBezout.pow_left hb K).dvd_of_dvd_mul_left hd

theorem two_return_divisibility (v : Nat → Bool) (m n ell f : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v j)))
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    (2 : Int) ^ min (m + ell) (n + f) ∣ returnDet v m n := by
  let K := min (m + ell) (n + f)
  have hp : ∀ a, K ≤ a → (2 : Int) ^ K ∣ (2 : Int) ^ a := by
    intro a ha
    refine ⟨(2 : Int) ^ (a - K), ?_⟩
    rw [← int_pow_add, Nat.add_sub_of_le ha]
  exact returnDet_of_forms v m n K p q hr.2.1
    (Int.dvd_trans (hp _ (Nat.min_le_left ..))
      (matching_prefix_divisibility v m ell hr hm))
    (Int.dvd_trans (hp _ (Nat.min_le_right ..))
      (matching_prefix_divisibility v n f hr hn))

def finiteWord (v : Nat → Bool) (N j : Nat) : Bool :=
  if j < N then v j else false

/-- A finite prefix followed by zeros always has a rational seed. The witness
may depend on N; this says nothing about rationality of the infinite word. -/
theorem finiteWord_realized : ∀ N (v : Nat → Bool),
    ∃ p q : Int, RealizesWord p q (fun j => bit (finiteWord v N j))
  | 0, v => by
    refine ⟨0, 1, by decide, by decide, ?_⟩
    intro j
    have hz : ∀ j, numIter 1 0 j = 0 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => simp [numIter, ih, numStep]
    simp [seedParity, hz, finiteWord, bit]
  | N + 1, v => by
    rcases finiteWord_realized N (fun j => v (j + 1)) with ⟨p, q, hr⟩
    let u := fun j => bit (finiteWord v (N + 1) j)
    have ht : RealizesWord p q (shiftWord u (0 + 1)) := by
      refine ⟨hr.1, hr.2.1, ?_⟩
      intro j
      rw [hr.2.2 j]
      dsimp [u, shiftWord, finiteWord]
      by_cases hj : j < N
      · simp [hj, show 1 + j < N + 1 by omega, Nat.add_comm]
      · simp [hj, show ¬ 1 + j < N + 1 by omega]
    have hb : u 0 = 0 ∨ u 0 = 1 := by
      dsimp [u, bit]; split <;> simp
    have hh := realizes_shiftWord_pred hb ht
    exact ⟨_, _, by simpa [RealizesWord, shiftWord, u] using hh⟩

/-- Crucial no-go: the congruence holds for every binary word with these
finite matches. No infinite rational realization is a hypothesis. -/
theorem returnDet_automatic (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    (2 : Int) ^ min (m + ell) (n + f) ∣ returnDet v m n := by
  let N := max (m + ell) (n + f)
  let u := finiteWord v N
  have hN1 : m + ell ≤ N := Nat.le_max_left ..
  have hN2 : n + f ≤ N := Nat.le_max_right ..
  have hv : ∀ j, j < N → u j = v j := by
    intro j hj; simp [u, finiteWord, hj]
  rcases finiteWord_realized N v with ⟨p, q, hr⟩
  have hmu : ∀ j, j < ell → u (m + j) = u j := by
    intro j hj; rw [hv _ (by omega), hv _ (by omega)]; exact hm j hj
  have hnu : ∀ j, j < f → u (n + j) = u j := by
    intro j hj; rw [hv _ (by omega), hv _ (by omega)]; exact hn j hj
  have hd := two_return_divisibility u m n ell f hr hmu hnu
  have h1 := common_prefix u v m (fun j hj => hv j (by omega))
  have h2 := common_prefix u v n (fun j hj => hv j (by omega))
  simpa only [returnDet, cycleCoeff, h1.1, h1.2, h2.1, h2.2] using hd

/-- Thus a nonzero determinant is already large for combinatorial reasons.
This cannot supply a rationality obstruction for a genuine pair of returns. -/
theorem returnDet_zero_or_large (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    returnDet v m n = 0 ∨
      (2 : Int) ^ min (m + ell) (n + f) ≤ absInt (returnDet v m n) := by
  by_cases hz : returnDet v m n = 0
  · exact Or.inl hz
  right
  rcases returnDet_automatic v m n ell f hm hn with ⟨d, hd⟩
  have hd0 : d ≠ 0 := by intro h; rw [h, Int.mul_zero] at hd; exact hz hd
  have h1 := absInt_pos_of_ne_zero hd0
  rw [hd, absInt_mul, absInt_of_nonneg (pow_nonneg_of_nonneg (by decide) _)]
  have hh := Int.mul_le_mul_of_nonneg_left h1
    (pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) (min (m + ell) (n + f)))
  simpa using hh

theorem returnDet_small_iff_zero (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    absInt (returnDet v m n) < (2 : Int) ^ min (m + ell) (n + f) ↔
      returnDet v m n = 0 := by
  constructor
  · intro h
    rcases returnDet_zero_or_large v m n ell f hm hn with hz | hlarge
    · exact hz
    · omega
  · intro hz
    rw [hz]
    exact pow_pos_of_pos (by decide) _

end CollatzLab
