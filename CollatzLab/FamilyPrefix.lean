import CollatzLab.FamilyWord

/-! Finite integer sums and the uniform block Mahler identity. -/
namespace CollatzLab.Family

theorem two_mul (x : Int) : 2 * x = x + x := by omega
theorem three_mul (x : Int) : 3 * x = x + x + x := by omega
theorem four_mul (x : Int) : 4 * x = x + x + x + x := by omega
theorem mul_two (x : Int) : x * 2 = x + x := by omega
theorem mul_three (x : Int) : x * 3 = x + x + x := by omega
theorem mul_four (x : Int) : x * 4 = x + x + x + x := by omega

/-- Expand distributivity and sort products; the remaining linear identity is checked by omega. -/
macro "family_ring" : tactic => `(tactic|
  (try simp only [two_mul, three_mul, four_mul, mul_two, mul_three, mul_four,
    Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
    Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_zero, Int.zero_mul,
    Int.one_mul, Int.mul_one, Int.add_zero, Int.zero_add,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at *
   all_goals omega))

/-- Homogenized sum of a finite word, with degree `n-1`. -/
def sum (v : Nat → Int) (a b : Int) : Nat → Int
  | 0 => 0
  | n + 1 => b * sum v a b n + v n * a ^ n

/-- The homogeneous geometric sum of length `n`. -/
def geom (a b : Int) : Nat → Int
  | 0 => 0
  | n + 1 => b * geom a b n + a ^ n

def pre (L : Nat) (a b : Int) (n : Nat) := sum (familyWord L) a b n

def C (L : Nat) (a b : Int) := b ^ 2 * geom a b (L - 2) + a ^ (L - 1)

theorem geom_identity (a b : Int) : ∀ n, (b - a) * geom a b n = b ^ n - a ^ n
  | 0 => by simp [geom, Int.pow_zero]
  | n + 1 => by
    have ih := geom_identity a b n
    have hi := congrArg (fun t : Int => b * t) ih
    simp only [geom, Int.pow_succ]
    family_ring

theorem geom_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ n, 0 ≤ geom a b n
  | 0 => by simp [geom, Int.pow_zero]
  | n + 1 => by
    have := Int.mul_nonneg hb (geom_nonneg ha hb n)
    have := pow_nonneg_of_nonneg ha n
    dsimp [geom, Int.pow_zero]; omega

theorem prefix_segment (v : Nat → Int) (a b : Int) (m : Nat) : ∀ n,
    sum v a b (m + n) = b ^ n * sum v a b m + a ^ m * sum (fun j => v (m + j)) a b n
  | 0 => by simp [sum, Int.pow_zero]
  | n + 1 => by
    rw [Nat.add_succ, sum, prefix_segment v a b m n, sum, Int.pow_succ, int_pow_add]
    family_ring

theorem prefix_initial (L : Nat) (hL : 3 ≤ L) (a b : Int) (m : Nat) :
    ∀ r, r ≤ L - 2 →
    pre L a b (L * m + r) = b ^ r * pre L a b (L * m) + a ^ (L * m) * geom a b r
  | 0, _ => by simp [pre, geom, Int.pow_zero]
  | r + 1, hr => by
    change b * pre L a b (L * m + r) + familyWord L (L * m + r) * a ^ (L * m + r) = _
    rw [prefix_initial L hL a b m r (by omega), word_initial hL m r (by omega),
      int_pow_add, geom, Int.pow_succ]
    family_ring

theorem prefix_block (L : Nat) (hL : 3 ≤ L) (a b : Int) (m : Nat) :
    pre L a b (L * (m + 1)) = b ^ L * pre L a b (L * m) +
      C L a b * a ^ (L * m) + a ^ (L - 2) * (b - a) * familyWord L m * a ^ (L * m) := by
  have he : L * (m + 1) = (L * m + (L - 2) + 1) + 1 := by
    rw [Nat.mul_succ]; omega
  have he1 : L * m + (L - 2) + 1 = L * m + (L - 1) := by omega
  rw [he]
  change b * (b * pre L a b (L * m + (L - 2)) +
    familyWord L (L * m + (L - 2)) * a ^ (L * m + (L - 2))) +
    familyWord L (L * m + (L - 2) + 1) * a ^ (L * m + (L - 2) + 1) = _
  rw [prefix_initial L hL a b m (L - 2) (Nat.le_refl _), he1,
    word_penult hL, word_last hL, int_pow_add a (L * m) (L - 2),
    int_pow_add a (L * m) (L - 1)]
  have hp : b ^ L = b ^ (L - 2) * b * b := by
    have : L = (L - 2) + 1 + 1 := by omega
    conv => lhs; rw [this, Int.pow_succ, Int.pow_succ]
  have hp1 : a ^ (L - 1) = a ^ (L - 2) * a := by
    have : L - 1 = (L - 2) + 1 := by omega
    rw [this, Int.pow_succ]
  rw [hp, hp1]
  dsimp [C]
  rw [hp1]
  simp only [Int.pow_succ, Int.pow_zero]
  family_ring

/-- The finite homogenized Mahler equation, at every block count `n`. -/
theorem prefix_mahler (L : Nat) (hL : 3 ≤ L) (a b : Int) : ∀ n,
    (b ^ L - a ^ L) * pre L a b (L * n) =
      C L a b * (b ^ (L * n) - a ^ (L * n)) +
      a ^ (L - 2) * (b - a) * (b ^ L - a ^ L) * pre L (a ^ L) (b ^ L) n
  | 0 => by simp [pre, sum, Int.pow_zero]
  | n + 1 => by
    have hi := congrArg (fun t : Int => b ^ L * t) (prefix_mahler L hL a b n)
    rw [prefix_block L hL]
    change _ = C L a b * (b ^ (L * (n + 1)) - a ^ (L * (n + 1))) +
      a ^ (L - 2) * (b - a) * (b ^ L - a ^ L) *
        (b ^ L * pre L (a ^ L) (b ^ L) n + familyWord L n * (a ^ L) ^ n)
    rw [int_pow_mul]
    have he : L * (n + 1) = L * n + L := Nat.mul_succ L n
    rw [he, int_pow_add, int_pow_add]
    family_ring

/-- The bases of the rational-seed recurrence. -/
def A (L : Nat) : Int := 2 ^ L
def B (L : Nat) : Int := 3 ^ (L - 1)
def c0 (L : Nat) : Int := B L - 2 ^ (L - 2)

/-- Consecutive odd steps in the common initial part of a block. -/
theorem odd_run {L : Nat} (hL : 3 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (m : Nat) : ∀ r, r ≤ L - 2 →
    (2 : Int) ^ r * (numIter q p (L * m + r) + q) =
      (3 : Int) ^ r * (numIter q p (L * m) + q)
  | 0, _ => by simp
  | r + 1, hb => by
    have hi := odd_run hL hr m r (by omega)
    have hs := (numIter_step_eq hr.2.1 (hr.2.2 (L * m + r))).2
      (word_initial hL m r (by omega))
    have hm := congrArg (fun t : Int => (2 : Int) ^ r * t) hs
    simp only [Nat.add_assoc] at hm
    have hi3 := congrArg (fun t : Int => 3 * t) hi
    rw [Int.pow_succ, Int.pow_succ]
    family_ring

/-- Length-`L` affine block recurrence derived solely from Collatz parity steps. -/
theorem numIter_block {L : Nat} (hL : 3 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (m : Nat) :
    A L * numIter q p (L * (m + 1)) = B L * numIter q p (L * m) +
      (c0 L - (2 : Int) ^ (L - 2) * familyWord L m) * q := by
  let i := L * m + (L - 2)
  have hpen := numIter_step_eq hr.2.1 (hr.2.2 i)
  have hlast := numIter_step_eq hr.2.1 (hr.2.2 (i + 1))
  have hw1 : familyWord L i = familyWord L m := word_penult hL m
  have hw2 : familyWord L (i + 1) = 1 - familyWord L m := by
    have he : i + 1 = L * m + (L - 1) := by dsimp [i]; omega
    rw [he, word_last hL]
  rw [hw1] at hpen
  rw [hw2] at hlast
  simp only [show i + 1 + 1 = i + 2 by omega] at hlast
  have ht : 4 * numIter q p (i + 2) = 3 * numIter q p i + (2 - familyWord L m) * q := by
    rcases word_binary L m with hw | hw
    · have h1 := hpen.1 hw
      have h2 := hlast.2 (by omega)
      rw [hw]; omega
    · have h1 := hpen.2 hw
      have h2 := hlast.1 (by omega)
      rw [hw]; omega
  have hi := odd_run hL hr m (L - 2) (Nat.le_refl _)
  have hi3 := congrArg (fun t : Int => 3 * t) hi
  have ht2 := congrArg (fun t : Int => (2 : Int) ^ (L - 2) * t) ht
  have he : L * (m + 1) = i + 2 := by dsimp [i]; rw [Nat.mul_succ]; omega
  have hA : A L = 4 * (2 : Int) ^ (L - 2) := by
    have he : L = (L - 2) + 2 := by omega
    dsimp [A]; conv => lhs; rw [he, int_pow_add]
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]; omega
  have hB : B L = 3 * (3 : Int) ^ (L - 2) := by
    have he : L - 1 = (L - 2) + 1 := by omega
    dsimp [B]; rw [he, Int.pow_succ]; ac_rfl
  rw [he, hA, c0, hB]
  change (2 : Int) ^ (L - 2) * (numIter q p i + q) = _ at hi
  change 3 * ((2 : Int) ^ (L - 2) * (numIter q p i + q)) = _ at hi3
  family_ring

/-- Exact divisibility needed for the initial normalization, at every block. -/
theorem initial_divisibility {L : Nat} (hL : 3 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (m : Nat) :
    (2 : Int) ^ (L - 2) ∣ (B L - A L) * numIter q p (L * m) + c0 L * q := by
  have hi := congrArg (fun t : Int => 3 * t)
    (odd_run hL hr m (L - 2) (Nat.le_refl _))
  have heA : A L = 4 * (2 : Int) ^ (L - 2) := by
    dsimp [A]; conv => lhs; rw [show L = (L - 2) + 2 by omega, int_pow_add]
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]; omega
  have heB : B L = 3 * (3 : Int) ^ (L - 2) := by
    dsimp [B]; rw [show L - 1 = (L - 2) + 1 by omega, Int.pow_succ]; ac_rfl
  refine ⟨3 * numIter q p (L * m + (L - 2)) + 2 * q - 4 * numIter q p (L * m), ?_⟩
  rw [c0, heA, heB]
  family_ring

/-- The normalized block numerator is an integer quotient, with exact division proved below. -/
def quotient (L : Nat) (p q : Int) (m : Nat) :=
  ((B L - A L) * numIter q p (L * m) + c0 L * q) / (2 : Int) ^ (L - 2)

theorem quotient_exact {L : Nat} (hL : 3 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (m : Nat) :
    (2 : Int) ^ (L - 2) * quotient L p q m =
      (B L - A L) * numIter q p (L * m) + c0 L * q := by
  rcases initial_divisibility hL hr m with ⟨r, he⟩
  dsimp [quotient]; rw [he, Int.mul_ediv_cancel_left r (by
    have := pow_pos_of_pos (x := 2) (by decide) (L - 2); omega)]

theorem quotient_step {L : Nat} (hL : 3 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (m : Nat) :
    A L * quotient L p q (m + 1) = B L * quotient L p q m -
      ((B L - A L) * q) * familyWord L m := by
  have hi := quotient_exact hL hr m
  have hj := quotient_exact hL hr (m + 1)
  have hs := numIter_block hL hr m
  have hh := congrArg (fun t : Int => (B L - A L) * t) hs
  have hiB := congrArg (fun t : Int => B L * t) hi
  have hjA := congrArg (fun t : Int => A L * t) hj
  apply Int.eq_of_mul_eq_mul_left (a := (2 : Int) ^ (L - 2))
    (by have := pow_pos_of_pos (x := 2) (by decide) (L - 2); omega)
  family_ring

/-- All finite initial congruences, with an explicit integer remainder. -/
theorem base_identity {L : Nat} (hL : 3 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) : ∀ n, 1 ≤ n →
    (B L) ^ (n - 1) * (B L * quotient L p q 0) -
      ((B L - A L) * q) * pre L (A L) (B L) n =
      (A L) ^ n * quotient L p q n
  | 0, hn => by omega
  | 1, _ => by
    have hs := quotient_step hL hr 0
    simp [pre, sum, word_zero, Int.pow_zero, int_pow_one] at *
    exact hs.symm
  | n + 2, _ => by
    have hi := base_identity hL hr (n + 1) (by omega)
    have hs := quotient_step hL hr (n + 1)
    have hiB := congrArg (fun t : Int => B L * t) hi
    have hsA := congrArg (fun t : Int => (A L) ^ (n + 1) * t) hs
    have he : n + 2 - 1 = n + 1 := by omega
    rw [he, Int.pow_succ (B L), Int.pow_succ (A L)]
    change _ - ((B L - A L) * q) *
      (B L * pre L (A L) (B L) (n + 1) + familyWord L (n + 1) * (A L) ^ (n + 1)) = _
    simp only [show n + 1 - 1 = n by omega] at hiB
    simp only [Nat.add_assoc, Nat.reduceAdd] at *
    family_ring

end CollatzLab.Family
