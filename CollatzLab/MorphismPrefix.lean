import CollatzLab.MorphismWord

/-! Generic finite Mahler identities, derived from literal binary images. -/
namespace CollatzLab.Morphism
open CollatzLab.Family

def pre {L : Nat} (M : Images L) (a b : Int) (n : Nat) := sum (parityWord M) a b n
def Q {L : Nat} (M : Images L) (c : Bool) (a b : Int) :=
  sum (fun j => bit (image M c j)) a b L
def Gamma {L : Nat} (M : Images L) (a b : Int) := Q M true a b - Q M false a b

theorem sum_ext (v w : Nat → Int) (a b : Int) : ∀ n,
    (∀ j, j < n → v j = w j) → sum v a b n = sum w a b n
  | 0, _ => rfl
  | n + 1, hv => by
    rw [sum, sum, sum_ext v w a b n (fun j hj => hv j (by omega)), hv n (by omega)]

theorem sum_sub (v w : Nat → Int) (a b : Int) : ∀ n,
    sum (fun j => v j - w j) a b n = sum v a b n - sum w a b n
  | 0 => by simp [sum]
  | n + 1 => by rw [sum, sum_sub, sum, sum]; family_ring

theorem sum_zero (a b : Int) : ∀ n, sum (fun _ => 0) a b n = 0
  | 0 => rfl
  | n + 1 => by simp [sum, sum_zero a b n]

theorem sum_block {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (a b : Int) (m : Nat) :
    sum (fun j => parityWord M (L * m + j)) a b L =
      Q M false a b + Gamma M a b * parityWord M m := by
  have he : sum (fun j => parityWord M (L * m + j)) a b L =
      Q M (word M m) a b := by
    apply sum_ext
    intro j hj
    simp only [parityWord, word_block hL M h1 m j hj]
  rw [he]
  unfold parityWord Gamma bit
  cases word M m <;> simp <;> omega

theorem prefix_block {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (a b : Int) (m : Nat) :
    pre M a b (L * (m + 1)) = b ^ L * pre M a b (L * m) +
      a ^ (L * m) * (Q M false a b + Gamma M a b * parityWord M m) := by
  rw [Nat.mul_succ]
  exact (prefix_segment (parityWord M) a b (L * m) L).trans
    (by rw [sum_block hL M h1]; rfl)

/-- All block counts, with no analytic convergence hypothesis. -/
theorem prefix_mahler {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (a b : Int) : ∀ n,
    (b ^ L - a ^ L) * pre M a b (L * n) =
      Q M false a b * (b ^ (L * n) - a ^ (L * n)) +
      Gamma M a b * (b ^ L - a ^ L) * pre M (a ^ L) (b ^ L) n
  | 0 => by simp [pre, sum, Int.pow_zero]
  | n + 1 => by
    have hi := congrArg (fun x : Int => b ^ L * x) (prefix_mahler hL M h1 a b n)
    rw [prefix_block hL M h1]
    change _ = Q M false a b * (b ^ (L * (n + 1)) - a ^ (L * (n + 1))) +
      Gamma M a b * (b ^ L - a ^ L) *
        (b ^ L * pre M (a ^ L) (b ^ L) n + parityWord M n * (a ^ L) ^ n)
    rw [int_pow_mul, Nat.mul_succ, int_pow_add, int_pow_add]
    family_ring

def A (L : Nat) : Int := 2 ^ L
def B {L : Nat} (M : Images L) : Int := 3 ^ weight (image M true) L
def c {L : Nat} (M : Images L) (b : Bool) : Int := offset (image M b) L

/-- Equal-weight affine blocks, including both possible orderings of `A,B`. -/
theorem numIter_block {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    {p q : Int} (hr : RealizesWord p q (parityWord M)) (m : Nat) :
    A L * numIter q p (L * (m + 1)) = B M * numIter q p (L * m) +
      (c M false + (c M true - c M false) * parityWord M m) * q := by
  have hp : ∀ j, j < L → seedParity q p (L * m + j) = bit (image M (word M m) j) := by
    intro j hj
    rw [hr.2.2]
    exact congrArg bit (word_block hL M h1 m j hj)
  have ha := affine_prefix (image M (word M m)) q p hr.2.1 (L * m) L hp
  rw [← Nat.mul_succ] at ha
  unfold A B c parityWord bit
  cases hb : word M m <;> simp only [hb, Bool.false_eq_true, if_false, if_true, Int.mul_zero,
    Int.mul_one, Int.add_zero, Int.add_sub_cancel] at ha ⊢
  · rw [hw] at ha
    exact ha
  · have he : offset (image M false) L + (offset (image M true) L - offset (image M false) L) =
        offset (image M true) L := by omega
    rw [he]
    exact ha

/-- The unnormalized seed recurrence uses only ordinary integer arithmetic. -/
def g {L : Nat} (M : Images L) (p q : Int) (n : Nat) : Int :=
  (B M - A L) * numIter q p (L * n) + c M false * q

theorem g_step {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    {p q : Int} (hr : RealizesWord p q (parityWord M)) (n : Nat) :
    A L * g M p q (n + 1) = B M * g M p q n -
      ((B M - A L) * (c M false - c M true) * q) * parityWord M n := by
  have hh := congrArg (fun x : Int => (B M - A L) * x) (numIter_block hL M h1 hw hr n)
  unfold g
  family_ring

/-- Every finite base congruence, before the exact `2^s` normalization. -/
theorem base_identity {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    {p q : Int} (hr : RealizesWord p q (parityWord M)) : ∀ n, 1 ≤ n →
    B M ^ (n - 1) * (B M * g M p q 0) -
      ((B M - A L) * (c M false - c M true) * q) * pre M (A L) (B M) n =
      A L ^ n * g M p q n
  | 0, hn => by omega
  | 1, _ => by
    have hs := g_step hL M h1 hw hr 0
    simpa [pre, sum, parityWord, word_zero, bit, Int.pow_zero, int_pow_one] using hs.symm
  | n + 2, _ => by
    have hi := base_identity hL M h1 hw hr (n + 1) (by omega)
    have hs := g_step hL M h1 hw hr (n + 1)
    have hiB := congrArg (fun x : Int => B M * x) hi
    have hsA := congrArg (fun x : Int => A L ^ (n + 1) * x) hs
    rw [show n + 2 - 1 = n + 1 by omega, Int.pow_succ (B M), Int.pow_succ (A L)]
    change _ - ((B M - A L) * (c M false - c M true) * q) *
      (B M * pre M (A L) (B M) (n + 1) + parityWord M (n + 1) * A L ^ (n + 1)) = _
    simp only [show n + 1 - 1 = n by omega] at hiB
    simp only [Nat.add_assoc, Nat.reduceAdd] at *
    family_ring

end CollatzLab.Morphism
