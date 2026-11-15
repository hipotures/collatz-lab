import CollatzLab.RationalHeight
import CollatzLab.FrontierSix

/-! Exact substituted rational-shadow structure for the literal Phase 12 word. -/
namespace CollatzLab.FrontierHeight
open CollatzLab Morphism RationalHeight

def inflate (v : Nat → Bool) (n : Nat) : Bool :=
  image frontierSix (v (n / 6)) (n % 6)

def baseShadow (n : Nat) : Bool := if n < 3 then word frontierSix n else true

def shadow : Nat → Nat → Bool
  | 0 => baseShadow
  | k + 1 => inflate (shadow k)

def matchLength : Nat → Nat
  | 0 => 11
  | k + 1 => 6 * matchLength k + 1

theorem fixed_inflate (n : Nat) : inflate (word frontierSix) n = word frontierSix n :=
  (word_rec (by decide) frontierSix frontierSix_images.2.2.1 n).symm

theorem matchLength_formula (k : Nat) : 5 * matchLength k + 1 = 56 * 6 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [matchLength, Nat.pow_succ]; omega

/-- First mismatch propagation, including the extra forced leading column. -/
theorem inflate_first_failure {v : Nat → Bool} {m : Nat}
    (he : ∀ j, j < m → v j = word frontierSix j) (hne : v m ≠ word frontierSix m) :
    (∀ j, j < 6 * m + 1 → inflate v j = word frontierSix j) ∧
      inflate v (6 * m + 1) ≠ word frontierSix (6 * m + 1) := by
  constructor
  · intro j hj
    rw [← fixed_inflate j]
    by_cases h : j / 6 < m
    · simp only [inflate, he _ h]
    · have hj0 : j = 6 * m := by omega
      subst j
      have hd : 6 * m / 6 = m := by omega
      simp only [inflate, hd, Nat.mul_mod_right]
      cases v m <;> cases word frontierSix m <;> decide
  · have hdiv : (6 * m + 1) / 6 = m := by omega
    have hmod : (6 * m + 1) % 6 = 1 := by omega
    rw [← fixed_inflate (6 * m + 1)]
    simp only [inflate, hdiv, hmod]
    cases hv : v m <;> cases hw : word frontierSix m <;>
      simp_all [image, frontierSix]

theorem shadow_first_failure : ∀ k,
    (∀ j, j < matchLength k → shadow k j = word frontierSix j) ∧
      shadow k (matchLength k) ≠ word frontierSix (matchLength k)
  | 0 => by
    constructor
    · intro j hj
      have ht : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
          j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by change j < 11 at hj; omega
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · decide
  | k + 1 => inflate_first_failure (shadow_first_failure k).1 (shadow_first_failure k).2

theorem inflate_period_after {v : Nat → Bool} {u s : Nat}
    (h : ∀ n, u ≤ n → v (n + s) = v n) :
    ∀ n, 6 * u ≤ n → inflate v (n + 6 * s) = inflate v n := by
  intro n hn
  have hd : (n + 6 * s) / 6 = n / 6 + s := by omega
  have hm : (n + 6 * s) % 6 = n % 6 := by omega
  simp only [inflate, hd, hm, h (n / 6) (by omega)]

theorem shadow_period_after : ∀ k n, 3 * 6 ^ k ≤ n →
    shadow k (n + 6 ^ k) = shadow k n
  | 0, n, hn => by simp [shadow, baseShadow, show ¬ n < 3 by simpa using hn,
      show ¬ n + 1 < 3 by simpa using (show 3 ≤ n + 1 by omega)]
  | k + 1, n, hn => by
    have hh := inflate_period_after (shadow_period_after k) n
    simpa only [shadow, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hh (by simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn)

theorem shadow_tail_initial (k j : Nat) (hj : j < 6 ^ k) :
    shadow k (3 * 6 ^ k + j) = word frontierSix j := by
  have hf := matchLength_formula k
  have hp := Nat.pow_pos (a := 6) (by decide) (n := k)
  have hh := (shadow_first_failure k).1 (3 * 6 ^ k + j) (by omega)
  have he := word_power_congr (by decide) frontierSix frontierSix_images.2.2.1 k 3 0
    (by decide : word frontierSix 3 = word frontierSix 0) j hj
  apply hh.trans
  simpa only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.mul_comm] using he

/-- Closing the actual affine map gives a rational seed for any supercritical
period. The proof first checks the finite parity cylinder, then the orbit. -/
theorem periodic_seed (v : Nat → Bool) (s : Nat) (hs : 1 ≤ s)
    (hper : ∀ n, v (n + s) = v n)
    (hgap : (2 : Int) ^ s < (3 : Int) ^ weight v s) :
    RealizesWord (-offset v s) ((3 : Int) ^ weight v s - (2 : Int) ^ s)
      (fun j => bit (v j)) := by
  let a := (3 : Int) ^ weight v s
  let M := (2 : Int) ^ s
  let c := offset v s
  have hM := pow_pos_of_pos (x := (2 : Int)) (by decide) s
  have hq : (a - M) % 2 = 1 := by
    have ho := odd_pow (x := (3 : Int)) (by decide) (weight v s)
    have he := Family.even_pow (x := (2 : Int)) (by decide) hs
    dsimp [a, M]; omega
  have hA := residue_spec v s
  have haff := affine_prefix v 1 (residue v s) (by decide) 0 s
    (fun j hj => by simpa using hA.2.2 j hj)
  simp only [Nat.zero_add, numIter, Int.mul_one] at haff
  have hd : InLattice (residue v s) s (-c) (a - M) := by
    refine ⟨residue v s - numIter 1 (residue v s) s, ?_⟩
    dsimp [a, M, c]
    family_ring
  have hpre := (cylinder_iff hA.2.2 hq).2 hd
  have ht := affine_prefix v (a - M) (-c) hq 0 s (fun j hj => by simpa using hpre j hj)
  simp only [Nat.zero_add, numIter] at ht
  have hcycle : numIter (a - M) (-c) s = -c := by
    apply Int.eq_of_mul_eq_mul_left (a := M) (by dsimp [M]; omega)
    dsimp [a, M, c] at *
    family_ring
  refine ⟨by dsimp [a, M] at *; omega, hq, ?_⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < s
    · exact hpre n hn
    · have hns : s + (n - s) = n := by omega
      have htail : seedParity (a - M) (-c) n = seedParity (a - M) (-c) (n - s) := by
        calc
          _ = seedParity (a - M) (-c) (s + (n - s)) := congrArg _ hns.symm
          _ = _ := by rw [seedParity_add, hcycle]
      rw [htail, ih (n - s) (by omega)]
      exact congrArg bit (by simpa only [show n - s + s = n by omega] using (hper (n - s)).symm)

/-- Exact rational inverse of a finite prefix, retaining its numerator and
denominator instead of hiding the witness in an existence argument. -/
theorem prepend_seed (v : Nat → Bool) (u : Nat) {p q : Int}
    (hr : RealizesWord p q (fun j => bit (v (u + j)))) :
    RealizesWord ((2 : Int) ^ u * p - offset v u * q)
      ((3 : Int) ^ weight v u * q) (fun j => bit (v j)) := by
  let a := (3 : Int) ^ weight v u
  let M := (2 : Int) ^ u
  let c := offset v u
  let P := M * p - c * q
  let Q := a * q
  have ha := pow_pos_of_pos (x := (3 : Int)) (by decide) (weight v u)
  have hM := pow_pos_of_pos (x := (2 : Int)) (by decide) u
  have hqo : Q % 2 = 1 := by
    have ho := odd_pow (x := (3 : Int)) (by decide) (weight v u)
    dsimp [Q, a]; rw [Int.mul_emod, ho, hr.2.1]; decide
  have hqp : 0 < Q := Int.mul_pos ha hr.1
  have hA := residue_spec v u
  have hbase := affine_prefix v 1 (residue v u) (by decide) 0 u
    (fun j hj => by simpa using hA.2.2 j hj)
  simp only [Nat.zero_add, numIter, Int.mul_one] at hbase
  have hd : InLattice (residue v u) u P Q := by
    refine ⟨p - q * numIter 1 (residue v u) u, ?_⟩
    have ht := congrArg (fun x : Int => q * x) hbase
    dsimp [P, Q, a, M, c]
    family_ring
  have hpre := (cylinder_iff hA.2.2 hqo).2 hd
  have ht := affine_prefix v Q P hqo 0 u (fun j hj => by simpa using hpre j hj)
  simp only [Nat.zero_add, numIter] at ht
  have hend : numIter Q P u = a * p := by
    apply Int.eq_of_mul_eq_mul_left (a := M) (by dsimp [M]; omega)
    dsimp [P, Q, a, M, c] at *
    family_ring
  refine ⟨hqp, hqo, ?_⟩
  intro n
  by_cases hn : n < u
  · exact hpre n hn
  · have heq : numIter Q P u * q = p * Q := by rw [hend]; dsimp [Q]; ac_rfl
    have hh := (numIter_equiv hqo hr.2.1 heq (n - u)).2
    have hn' : u + (n - u) = n := by omega
    calc
      _ = seedParity Q P (u + (n - u)) := congrArg _ hn'.symm
      _ = seedParity q p (n - u) := by rw [seedParity_add, hh]
      _ = bit (v (u + (n - u))) := hr.2.2 (n - u)
      _ = _ := by rw [hn']

theorem local_pressure (n t : Nat) (ht : t < 6) :
    (2 : Int) ^ t ≤ 4 * (3 : Int) ^ weight (fun j => word frontierSix (6 * n + j)) t := by
  have he : ∀ j, j < t → word frontierSix (6 * n + j) = image frontierSix (word frontierSix n) j :=
    fun j hj => word_block (by decide) frontierSix frontierSix_images.2.2.1 n j (by omega)
  rw [(common_prefix _ _ t he).1]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases word frontierSix n <;> decide

/-- An integer pressure bound for every prefix, without analytic limits. -/
theorem prefix_pressure (n : Nat) :
    (2 : Int) ^ n ≤ 4 * (3 : Int) ^ weight (word frontierSix) n := by
  let t := n / 6
  let s := n % 6
  let r := weight (fun j => word frontierSix (6 * t + j)) s
  have hn : 6 * t + s = n := by dsimp [t, s]; omega
  have hc := frontierSix_prefix_step t s
  rw [hn] at hc
  have hw := weight_le (word frontierSix) t
  have hcount : 4 * t + r ≤ weight (word frontierSix) n := by
    have he : ((4 * t + r : Nat) : Int) ≤ (weight (word frontierSix) n : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]
      dsimp [r]; omega
    exact Int.ofNat_le.mp he
  have hbase := pow_le_pow_of_le (x := (2 : Int) ^ 6) (y := (3 : Int) ^ 4)
    (by decide) (by decide) t
  rw [int_pow_mul, int_pow_mul] at hbase
  have hlocal := local_pressure t s (by dsimp [s]; omega)
  have hlarge := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) hcount)
  simp only [Int.natCast_pow] at hlarge
  calc
    (2 : Int) ^ n = (2 : Int) ^ (6 * t) * (2 : Int) ^ s := by rw [← int_pow_add, hn]
    _ ≤ (3 : Int) ^ (4 * t) * (2 : Int) ^ s :=
      Int.mul_le_mul_of_nonneg_right hbase (pow_nonneg_of_nonneg (by decide) _)
    _ ≤ (3 : Int) ^ (4 * t) * (4 * (3 : Int) ^ r) :=
      Int.mul_le_mul_of_nonneg_left hlocal (pow_nonneg_of_nonneg (by decide) _)
    _ = 4 * (3 : Int) ^ (4 * t + r) := by rw [int_pow_add]; family_ring
    _ ≤ 4 * (3 : Int) ^ weight (word frontierSix) n :=
      Int.mul_le_mul_of_nonneg_left hlarge (by decide)

theorem offset_of_pressure (v : Nat → Bool)
    (hp : ∀ n, (2 : Int) ^ n ≤ 4 * (3 : Int) ^ weight v n) : ∀ n,
    offset v n ≤ 2 * (n : Int) * (3 : Int) ^ weight v n
  | 0 => by simp [offset, weight]
  | n + 1 => by
    have hi := offset_of_pressure v hp n
    have hpr := hp n
    have hz := pow_nonneg_of_nonneg (x := (3 : Int)) (by decide) (weight v n)
    cases hb : v n
    · simp only [offset, weight, hb, Bool.false_eq_true, if_false, Nat.add_zero,
        Int.natCast_add, Int.natCast_one]
      family_ring
    · have h3 := Int.mul_le_mul_of_nonneg_left hi (by decide : (0 : Int) ≤ 3)
      simp only [offset, weight, hb, if_true, Int.pow_succ, Int.natCast_add, Int.natCast_one]
      family_ring

theorem power_gap : ∀ k,
    (2 : Int) ^ (6 ^ k) < (3 : Int) ^ weight (word frontierSix) (6 ^ k)
  | 0 => by decide
  | k + 1 => by
    let t := 6 ^ k
    have hc := frontierSix_prefix_step t 0
    have hw := weight_le (word frontierSix) t
    have hcount : 4 * t ≤ weight (word frontierSix) (6 * t) := by
      have he : ((4 * t : Nat) : Int) ≤ (weight (word frontierSix) (6 * t) : Int) := by
        simp only [weight, Nat.add_zero, Int.natCast_mul] at hc ⊢
        omega
      exact Int.ofNat_le.mp he
    have hg := positive_pow_strict ((3 : Int) ^ 4) ((2 : Int) ^ 6)
      (by decide) (by decide) t (Nat.pow_pos (by decide))
    rw [int_pow_mul, int_pow_mul] at hg
    have hh := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) hcount)
    simp only [Int.natCast_pow] at hh
    change (3 : Int) ^ (4 * t) ≤ (3 : Int) ^ weight (word frontierSix) (6 * t) at hh
    have he : 6 ^ (k + 1) = 6 * t := by dsimp [t]; rw [Nat.pow_succ]; omega
    rw [he]
    omega

def shadowNum (k : Nat) : Int :=
  -((2 : Int) ^ (3 * 6 ^ k) * offset (word frontierSix) (6 ^ k) +
    offset (word frontierSix) (3 * 6 ^ k) *
      ((3 : Int) ^ weight (word frontierSix) (6 ^ k) - (2 : Int) ^ (6 ^ k)))

def shadowDen (k : Nat) : Int :=
  (3 : Int) ^ weight (word frontierSix) (3 * 6 ^ k) *
    ((3 : Int) ^ weight (word frontierSix) (6 ^ k) - (2 : Int) ^ (6 ^ k))

/-- These explicit signed rational pairs realize the whole substituted shadow. -/
theorem shadow_realized (k : Nat) :
    RealizesWord (shadowNum k) (shadowDen k) (fun j => bit (shadow k j)) := by
  let S := 6 ^ k
  let v := fun j => shadow k (3 * S + j)
  have hv := common_prefix v (word frontierSix) S (shadow_tail_initial k)
  have hs : 1 ≤ S := Nat.pow_pos (by decide)
  have hper : ∀ n, v (n + S) = v n := by
    intro n
    simpa only [v, S, Nat.add_assoc] using shadow_period_after k (3 * S + n) (by omega)
  have hgap : (2 : Int) ^ S < (3 : Int) ^ weight v S := by
    rw [hv.1]; exact power_gap k
  have ht := periodic_seed v S hs hper hgap
  rw [hv.1, hv.2] at ht
  have hpre := common_prefix (shadow k) (word frontierSix) (3 * S)
    (fun j hj => (shadow_first_failure k).1 j (by
      have := matchLength_formula k; have := hs; dsimp [S] at *; omega))
  have hh := prepend_seed (shadow k) (3 * S) ht
  rw [hpre.1, hpre.2] at hh
  have hnum : (2 : Int) ^ (3 * S) * (-offset (word frontierSix) S) -
      offset (word frontierSix) (3 * S) * ((3 : Int) ^ weight (word frontierSix) S - (2 : Int) ^ S) =
        shadowNum k := by dsimp [shadowNum, S]; family_ring
  rw [hnum] at hh
  exact hh

theorem shadow_prefix (k : Nat) :
    Prefix (shadowDen k) (shadowNum k) (word frontierSix) (matchLength k) := by
  intro j hj
  rw [(shadow_realized k).2.2 j]
  change bit (shadow k j) = bit (word frontierSix j)
  rw [(shadow_first_failure k).1 j hj]

theorem shadow_failure (k : Nat) :
    seedParity (shadowDen k) (shadowNum k) (matchLength k) ≠
      bit (word frontierSix (matchLength k)) := by
  rw [(shadow_realized k).2.2]
  change bit (shadow k (matchLength k)) ≠ bit (word frontierSix (matchLength k))
  have hh := (shadow_first_failure k).2
  cases h1 : shadow k (matchLength k) <;> cases h2 : word frontierSix (matchLength k) <;>
    simp_all [bit]

theorem shadow_weight_sum (k : Nat) :
    7 * ((weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k) : Nat) : Int) =
      20 * (6 ^ k : Nat) - 6 * (-1 : Int) ^ k := by
  have hu := balance_power (by decide) frontierSix frontierSix_images.2.2.1 k 0 3
  have hv := frontierSix_power_count k 0
  simp only [balance, frontierSix_images.2.2.2.2.1,
    frontierSix_images.2.2.2.2.2.1, frontierSix_images.2.2.2.2.2.2,
    Nat.mul_zero, Nat.zero_add, Int.natCast_mul] at hu
  simp only [Nat.mul_zero, Nat.zero_add, bit, word_zero, if_true] at hv
  have hw : weight (word frontierSix) 3 = 1 := by decide
  rw [hw, Nat.mul_comm (6 ^ k) 3] at hu
  change 7 * (weight (word frontierSix) (3 * 6 ^ k) : Int) -
    5 * ((6 ^ k : Nat) * 3 : Nat) = (-1 : Int) ^ k * (7 * 1 - 5 * 3) at hu
  change 7 * (weight (word frontierSix) (6 ^ k) : Int) =
    5 * (6 ^ k : Nat) + (-1 : Int) ^ k * (7 * 1 - 5) at hv
  simp only [Int.natCast_mul] at hu
  simp only [Int.natCast_add] at *
  omega

/-- An all-level exact height bound on the explicit rational shadows. -/
theorem shadow_height_bound (k : Nat) :
    height (shadowNum k) (shadowDen k) ≤
      14 * 6 ^ k * 3 ^ (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k)) := by
  let S := 6 ^ k
  let a := (3 : Int) ^ weight (word frontierSix) (3 * S)
  let b := (3 : Int) ^ weight (word frontierSix) S
  let c := offset (word frontierSix) (3 * S)
  let d := offset (word frontierSix) S
  let U := (2 : Int) ^ (3 * S)
  let V := (2 : Int) ^ S
  let T := 14 * (S : Int) * a * b
  have hS : 1 ≤ S := Nat.pow_pos (by decide)
  have ha : 0 < a := pow_pos_of_pos (by decide) _
  have hb : 0 < b := pow_pos_of_pos (by decide) _
  have hc0 : 0 ≤ c := offset_nonneg _ _
  have hd0 : 0 ≤ d := offset_nonneg _ _
  have hU : 0 ≤ U := pow_nonneg_of_nonneg (by decide) _
  have hV : 0 ≤ V := pow_nonneg_of_nonneg (by decide) _
  have hD : 0 < b - V := by have := power_gap k; dsimp [S, b, V] at *; omega
  have hc : c ≤ 6 * (S : Int) * a := by
    have hh := offset_of_pressure (word frontierSix) prefix_pressure (3 * S)
    simp only [Int.natCast_mul] at hh
    dsimp [c, a]; family_ring
  have hd : d ≤ 2 * (S : Int) * b := offset_of_pressure (word frontierSix) prefix_pressure S
  have hUp : U ≤ 4 * a := prefix_pressure (3 * S)
  have hd1 := Int.mul_le_mul_of_nonneg_left hd hU
  have hd2 := Int.mul_le_mul_of_nonneg_right hUp
    (show 0 ≤ 2 * (S : Int) * b from Int.mul_nonneg (by omega) (by omega))
  have hc1 := Int.mul_le_mul_of_nonneg_left (show b - V ≤ b by omega) hc0
  have hc2 := Int.mul_le_mul_of_nonneg_right hc (show 0 ≤ b by omega)
  have hP : absInt (shadowNum k) = U * d + c * (b - V) := by
    have h1 := Int.mul_nonneg hU hd0
    have h2 := Int.mul_nonneg hc0 (show 0 ≤ b - V by omega)
    change absInt (-(U * d + c * (b - V))) = _
    unfold absInt; split <;> omega
  have hPbound : absInt (shadowNum k) ≤ T := by rw [hP]; dsimp [T]; family_ring
  have hq1 := Int.mul_le_mul_of_nonneg_left (show b - V ≤ b by omega) (show 0 ≤ a by omega)
  have hq2 := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ 14 * (S : Int) by omega)
    (show 0 ≤ a * b from Int.mul_nonneg (by omega) (by omega))
  have hQbound : absInt (shadowDen k) ≤ T := by
    rw [absInt_of_nonneg (show 0 ≤ shadowDen k by have := (shadow_realized k).1; omega)]
    change a * (b - V) ≤ T
    dsimp [T]; family_ring
  have hT : ((14 * S * 3 ^ (weight (word frontierSix) (3 * S) + weight (word frontierSix) S) : Nat) : Int) = T := by
    simp only [Int.natCast_mul, Int.natCast_pow, int_pow_add]
    dsimp [T, a, b]
    ac_rfl
  apply Nat.max_le.mpr
  constructor
  · exact Int.ofNat_le.mp (by rw [← absInt_eq_natAbs, hT]; exact hPbound)
  · exact Int.ofNat_le.mp (by rw [← absInt_eq_natAbs, hT]; exact hQbound)

theorem H_shadow_upper (k : Nat) :
    H (word frontierSix) (matchLength k) ≤
      14 * 6 ^ k * 3 ^ (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k)) := by
  have hr := shadow_realized k
  exact Nat.le_trans ((H_spec _ _).2 _ _ hr.1 hr.2.1 (shadow_prefix k)) (shadow_height_bound k)

theorem H_shadow_crossing (k : Nat) :
    (2 : Int) ^ matchLength k ≤ 2 *
      (14 * (6 ^ k : Nat) * (3 : Int) ^
        (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k))) *
          (H (word frontierSix) (matchLength k + 1) : Int) := by
  have hcross := shadow_crossing (shadow_realized k).2.1 (shadow_prefix k) (shadow_failure k)
  have hh := Int.ofNat_le.mpr (shadow_height_bound k)
  simp only [Int.natCast_mul, Int.natCast_pow] at hh
  change (height (shadowNum k) (shadowDen k) : Int) ≤
    14 * (6 : Int) ^ k * (3 : Int) ^
      (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k)) at hh
  have hm := Int.mul_le_mul_of_nonneg_right hh
    (show 0 ≤ (H (word frontierSix) (matchLength k + 1) : Int) by omega)
  simp only [Int.natCast_pow]
  change (2 : Int) ^ matchLength k ≤ 2 *
    (14 * (6 : Int) ^ k * (3 : Int) ^
      (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k))) *
        (H (word frontierSix) (matchLength k + 1) : Int)
  apply Int.le_trans hcross
  have h2 := Int.mul_le_mul_of_nonneg_left hm (by decide : (0 : Int) ≤ 2)
  simpa only [Int.mul_assoc] using h2

theorem H_after_shadow (k N : Nat) (hn : matchLength k < N) :
    (2 : Int) ^ matchLength k ≤ 2 *
      (14 * (6 ^ k : Nat) * (3 : Int) ^
        (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k))) *
          (H (word frontierSix) N : Int) := by
  have hb := H_shadow_crossing k
  have hm := Int.ofNat_le.mpr (H_mono (word frontierSix) (show matchLength k + 1 ≤ N by omega))
  have hp : 0 ≤ 2 * (14 * (6 ^ k : Nat) * (3 : Int) ^
      (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k))) :=
    Int.mul_nonneg (by decide) (Int.mul_nonneg
      (by exact_mod_cast Nat.zero_le (14 * 6 ^ k)) (pow_nonneg_of_nonneg (by decide) _))
  exact Int.le_trans hb (Int.mul_le_mul_of_nonneg_left hm hp)

/-- Independent small regressions, proved without running the Python solver. -/
theorem H_eleven : H (word frontierSix) 11 = 3 := by
  have hpre : Prefix 1 (-3) (word frontierSix) 11 := by
    have h : ∀ j : Fin 11, seedParity 1 (-3) j = bit (word frontierSix j) := by decide
    intro j hj; exact h ⟨j, hj⟩
  have hu := (H_spec (word frontierSix) 11).2 (-3) 1 (by decide) (by decide) hpre
  change H (word frontierSix) 11 ≤ 3 at hu
  rcases (H_spec (word frontierSix) 11).1 with ⟨p, q, hqp, hqo, hp, he⟩
  have hb := height_bounds p q
  have hqabs := absInt_of_nonneg (show 0 ≤ q by omega)
  rw [he, hqabs] at hb
  have hd := (cylinder_iff hpre hqo).1 hp
  change (2048 : Int) ∣ p - (-3) * q at hd
  have hm := Int.emod_eq_zero_of_dvd hd
  unfold absInt at hb
  omega

theorem H_twelve : H (word frontierSix) 12 = 513 := by
  have hpre : Prefix 1 2045 (word frontierSix) 12 := by
    have h : ∀ j : Fin 12, seedParity 1 2045 j = bit (word frontierSix j) := by decide
    intro j hj; exact h ⟨j, hj⟩
  have htest : Prefix 513 509 (word frontierSix) 12 := by
    have h : ∀ j : Fin 12, seedParity 513 509 j = bit (word frontierSix j) := by decide
    intro j hj; exact h ⟨j, hj⟩
  have hu := (H_spec (word frontierSix) 12).2 509 513 (by decide) (by decide) htest
  change H (word frontierSix) 12 ≤ 513 at hu
  rcases (H_spec (word frontierSix) 12).1 with ⟨p, q, hqp, hqo, hp, he⟩
  have hb := height_bounds p q
  have hqabs := absInt_of_nonneg (show 0 ≤ q by omega)
  rw [he, hqabs] at hb
  have hd := (cylinder_iff hpre hqo).1 hp
  change (4096 : Int) ∣ p - 2045 * q at hd
  rcases hd with ⟨d, hd⟩
  have hqo' : q = 2 * (q / 2) + 1 := by omega
  have hline : p + 3 * q = 4096 * (d + q / 2) + 2048 := by omega
  by_cases hlo : 513 ≤ H (word frontierSix) 12
  · omega
  · have hbound : H (word frontierSix) 12 ≤ 512 := by omega
    have hpb : -512 ≤ p ∧ p ≤ 512 := by
      have ht := hb.1
      unfold absInt at ht
      split at ht <;> omega
    have hqb : q ≤ 511 := by omega
    have hrange : -2048 < p + 3 * q ∧ p + 3 * q < 2048 := by omega
    generalize d + q / 2 = z at hline
    omega

end CollatzLab.FrontierHeight
