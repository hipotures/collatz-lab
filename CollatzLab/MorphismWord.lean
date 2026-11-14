import CollatzLab.FamilyPrefix

/-! Arbitrary uniform binary substitutions, with the fixed point starting in `1`. -/
namespace CollatzLab.Morphism

structure Images (L : Nat) where
  zero : Fin L → Bool
  one : Fin L → Bool

def image {L : Nat} (M : Images L) (b : Bool) (j : Nat) : Bool :=
  if h : j < L then (if b then M.one ⟨j, h⟩ else M.zero ⟨j, h⟩) else false

def bit (b : Bool) : Int := if b then 1 else 0

def aux {L : Nat} (M : Images L) : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => true
  | f + 1, n => image M (aux M f (n / L)) (n % L)

def word {L : Nat} (M : Images L) (n : Nat) : Bool := aux M n n
def parityWord {L : Nat} (M : Images L) (n : Nat) : Int := bit (word M n)

theorem word_zero {L : Nat} (M : Images L) : word M 0 = true := rfl

theorem aux_stable {L : Nat} (hL : 2 ≤ L) (M : Images L) :
    ∀ f g n, n ≤ f → n ≤ g → aux M f n = aux M g n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, hf, _ => by
    have : n = 0 := by omega
    subst n; rfl
  | _ + 1, 0, n, _, hg => by
    have : n = 0 := by omega
    subst n; rfl
  | f + 1, g + 1, n, hf, hg => by
    by_cases hn : n = 0
    · subst n; rfl
    · have hd : n / L < n := Nat.div_lt_self (by omega) (by omega)
      simp only [aux, hn, aux_stable hL M f g (n / L) (by omega) (by omega)]

theorem aux_eq {L : Nat} (hL : 2 ≤ L) (M : Images L) (f n : Nat)
    (hf : n ≤ f) : aux M f n = word M n :=
  aux_stable hL M f n n hf (Nat.le_refl n)

theorem word_rec {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (n : Nat) :
    word M n = image M (word M (n / L)) (n % L) := by
  by_cases hn : n = 0
  · subst n; simpa [word_zero] using h1.symm
  · rw [← aux_eq hL M (n + 1) n (by omega)]
    simp only [aux, hn, aux_eq hL M n (n / L) (Nat.div_le_self ..)]

theorem word_block {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (n j : Nat) (hj : j < L) :
    word M (L * n + j) = image M (word M n) j := by
  rw [word_rec hL M h1]
  have hd : (L * n + j) / L = n := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; omega
  have hm : (L * n + j) % L = j := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [hd, hm]

/-- Uniqueness requires the specified starting symbol: both images may fix zero. -/
theorem word_unique {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (v : Nat → Bool) (hv0 : v 0 = true)
    (hv : ∀ n j, j < L → v (L * n + j) = image M (v n) j) :
    v = word M := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n; exact hv0
    · have hm : n % L < L := Nat.mod_lt n (by omega)
      have he : L * (n / L) + n % L = n := by have := Nat.mod_add_div n L; omega
      conv => lhs; rw [← he, hv _ _ hm]
      rw [word_rec hL M h1, ih (n / L) (Nat.div_lt_self (by omega) (by omega))]

/-- Every full block is literally the selected finite image. -/
theorem literal_block {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (n : Nat) :
    List.ofFn (fun j : Fin L => word M (L * n + j.val)) =
      List.ofFn (fun j : Fin L => if word M n then M.one j else M.zero j) := by
  apply congrArg List.ofFn
  funext j
  rw [word_block hL M h1 _ _ j.isLt]
  simp [image, j.isLt]

theorem parity_binary {L : Nat} (M : Images L) (n : Nat) :
    parityWord M n = 0 ∨ parityWord M n = 1 := by
  unfold parityWord bit
  cases word M n <;> simp

/-- Prefix weight, with no ordering assumption on `2^L` and `3^r`. -/
def weight (v : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => weight v n + if v n then 1 else 0

def offset (v : Nat → Bool) : Nat → Int
  | 0 => 0
  | n + 1 => if v n then 3 * offset v n + (2 : Int) ^ n else offset v n

theorem weight_le (v : Nat → Bool) : ∀ n, weight v n ≤ n
  | 0 => by simp [weight]
  | n + 1 => by have := weight_le v n; simp only [weight]; split <;> omega

theorem weight_mono (v : Nat → Bool) {n m : Nat} (hnm : n ≤ m) :
    weight v n ≤ weight v m := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst n; exact Nat.le_refl _
  | succ m ih =>
    by_cases hn : n = m + 1
    · rw [hn]
      exact Nat.le_refl _
    · have := ih (by omega)
      simp only [weight]; split <;> omega

theorem weight_positive {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) : 1 ≤ weight (image M true) L := by
  have hh := weight_mono (image M true) (n := 1) (m := L) (by omega)
  simpa [weight, h1] using hh

theorem weight_full_iff (v : Nat → Bool) : ∀ n,
    weight v n = n ↔ ∀ j, j < n → v j = true
  | 0 => by simp [weight]
  | n + 1 => by
    have hle := weight_le v n
    constructor
    · intro hh
      have hv : v n = true := by
        cases hb : v n <;> simp [weight, hb] at hh ⊢ <;> omega
      have hw : weight v n = n := by simp [weight, hv] at hh; omega
      intro j hj
      by_cases he : j = n
      · rw [he]; exact hv
      · exact (weight_full_iff v n).1 hw j (by omega)
    · intro hh
      have hv := hh n (by omega)
      have hw := (weight_full_iff v n).2 (fun j hj => hh j (by omega))
      simp [weight, hv, hw]

/-- H1--H3 force a zero in the `1` image; no extra admissibility condition. -/
theorem one_has_zero {L : Nat} (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) : ∃ j, j < L ∧ image M true j = false := by
  classical
  by_cases hz : ∃ j, j < L ∧ image M true j = false
  · exact hz
  · have hfull : ∀ j, j < L → image M true j = true := by
      intro j hj
      cases hb : image M true j
      · exact False.elim (hz ⟨j, hj, hb⟩)
      · rfl
    have hwt := (weight_full_iff (image M true) L).2 hfull
    have hwf := (weight_full_iff (image M false) L).1 (hw.trans hwt)
    apply False.elim
    apply hd
    funext j
    have h0 := hwf j.val j.isLt
    have h1 := hfull j.val j.isLt
    simp only [image, dif_pos j.isLt, Bool.false_eq_true, if_false, if_true] at h0 h1
    exact h0.trans h1.symm

theorem weight_lt_length {L : Nat} (M : Images L)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) : weight (image M true) L < L := by
  have hle := weight_le (image M true) L
  rcases one_has_zero M hw hd with ⟨j, hj, hz⟩
  by_cases he : weight (image M true) L = L
  · have hh := (weight_full_iff (image M true) L).1 he j hj
    rw [hz] at hh
    contradiction
  · omega

/-- The affine identity is derived from the actual signed numerator dynamics. -/
theorem affine_prefix (v : Nat → Bool) (q p : Int) (hq : q % 2 = 1)
    (m : Nat) : ∀ n,
    (∀ j, j < n → seedParity q p (m + j) = bit (v j)) →
    (2 : Int) ^ n * numIter q p (m + n) =
      (3 : Int) ^ (weight v n) * numIter q p m + offset v n * q
  | 0, _ => by simp [weight, offset]
  | n + 1, hv => by
    have hi := affine_prefix v q p hq m n (fun j hj => hv j (by omega))
    have hp : numIter q p (m + n) % 2 = bit (v n) := hv n (by omega)
    have hs := numStep_eq q (numIter q p (m + n)) hq
    cases hb : v n with
    | false =>
      have hh := hs.1 (by rw [hp]; simp [bit, hb])
      change 2 * numIter q p (m + n + 1) = _ at hh
      have hm := congrArg (fun x : Int => (2 : Int) ^ n * x) hh
      simp only [weight, offset, hb, Bool.false_eq_true, if_false, Nat.add_zero]
      rw [Int.pow_succ]
      simp only [Nat.add_assoc] at hm
      family_ring
    | true =>
      have hh := hs.2 (by rw [hp]; simp [bit, hb])
      change 2 * numIter q p (m + n + 1) = _ at hh
      have hm := congrArg (fun x : Int => (2 : Int) ^ n * x) hh
      have hi3 := congrArg (fun x : Int => 3 * x) hi
      simp only [weight, offset, hb, if_true]
      rw [Int.pow_succ, Int.pow_succ]
      simp only [Nat.add_assoc] at hm
      family_ring

end CollatzLab.Morphism
