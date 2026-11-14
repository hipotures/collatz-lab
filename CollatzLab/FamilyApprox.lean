import CollatzLab.FamilyTower

/-! The periodic approximant and its first differing coefficient, uniformly in `L`. -/
namespace CollatzLab.Family

/-- Order of the first disagreement with `(1^(L-1)0)^infinity`. -/
def N (L : Nat) := L * L - 2

def P (L : Nat) (a b : Int) := b ^ 2 * geom a b (L - 1)

def E (L : Nat) (p q : Int) (k : Nat) :=
  D L q k * P L (a L k) (b L k) - u L p q k * (b L k ^ L - a L k ^ L)

theorem first_block (L : Nat) (hL : 3 ≤ L) (r : Nat) (hr : r < L - 1) :
    familyWord L r = 1 := by
  by_cases hs : r < L - 2
  · simpa using word_initial hL 0 r hs
  · have he : r = L - 2 := by omega
    rw [he]
    simpa [word_zero] using word_penult hL 0

theorem first_zero (L : Nat) (hL : 3 ≤ L) : familyWord L (L - 1) = 0 := by
  have hh := word_last hL 0
  simpa [word_zero] using hh

theorem periodic_block (L : Nat) (hL : 3 ≤ L) (a b : Int) :
    C L a b + a ^ (L - 2) * (b - a) = b * geom a b (L - 1) := by
  have hg : geom a b (L - 1) = b * geom a b (L - 2) + a ^ (L - 2) := by
    rw [show L - 1 = (L - 2) + 1 by omega, geom]
  have hp : a ^ (L - 1) = a ^ (L - 2) * a := by
    rw [← Int.pow_succ, show L - 2 + 1 = L - 1 by omega]
  rw [C, hg, hp]
  simp only [Int.pow_succ, Int.pow_zero]
  family_ring

/-- All full blocks preceding block `L-1` equal the periodic approximant. -/
theorem periodic_prefix (L : Nat) (hL : 3 ≤ L) (a b : Int) : ∀ m, m ≤ L - 1 →
    (b ^ L - a ^ L) * pre L a b (L * m) =
      b * geom a b (L - 1) * (b ^ (L * m) - a ^ (L * m))
  | 0, _ => by simp [pre, sum, Int.pow_zero]
  | m + 1, hm => by
    have hi := congrArg (fun t : Int => b ^ L * t) (periodic_prefix L hL a b m (by omega))
    rw [prefix_block L hL, first_block L hL m (by omega)]
    have hb : C L a b * a ^ (L * m) + a ^ (L - 2) * (b - a) * 1 * a ^ (L * m) =
        b * geom a b (L - 1) * a ^ (L * m) := by
      rw [← periodic_block L hL] <;> family_ring
    rw [Int.add_assoc, hb, Nat.mul_succ, int_pow_add, int_pow_add]
    family_ring

theorem order_split (L : Nat) (hL : 3 ≤ L) : N L = L * (L - 1) + (L - 2) := by
  have hs : L = (L - 1) + 1 := by omega
  have hh := congrArg (fun n : Nat => L * n) hs
  dsimp only at hh
  rw [Nat.mul_add] at hh
  dsimp [N]; omega

/-- The first changed symbol, proved without evaluating a bounded list of `L`s. -/
theorem first_difference (L : Nat) (hL : 3 ≤ L) :
    familyWord L (N L) = 0 := by
  rw [order_split L hL, word_penult hL, first_zero L hL]

/-- Exact finite Padé identity; its constant coefficient after division by `a^N` is `b^L`. -/
theorem approximant_identity (L : Nat) (hL : 3 ≤ L) (a b : Int) :
    b ^ (N L) * P L a b - (b ^ L - a ^ L) * pre L a b (N L + 1) =
      a ^ (N L) * (b ^ L + a * (a * geom a b (L - 1) - a ^ (L - 1))) := by
  let m := L * (L - 1)
  have hs : N L = m + (L - 2) := order_split L hL
  have hp : pre L a b (N L + 1) + a ^ (N L) =
      b ^ (L - 1) * pre L a b m + a ^ m * geom a b (L - 1) := by
    rw [hs]
    change b * pre L a b (m + (L - 2)) + familyWord L (m + (L - 2)) * a ^ (m + (L - 2)) +
      a ^ (m + (L - 2)) = _
    have hw : familyWord L (m + (L - 2)) = 0 := by
      rw [← hs]; exact first_difference L hL
    rw [hw, prefix_initial L hL a b (L - 1) (L - 2) (Nat.le_refl _)]
    have hg : geom a b (L - 1) = b * geom a b (L - 2) + a ^ (L - 2) := by
      rw [show L - 1 = (L - 2) + 1 by omega, geom]
    have hb : b ^ (L - 1) = b ^ (L - 2) * b := by
      rw [← Int.pow_succ, show L - 2 + 1 = L - 1 by omega]
    rw [hg, hb, int_pow_add]
    dsimp [m] at *
    family_ring
  have ht := congrArg (fun t : Int => (b ^ L - a ^ L) * t) hp
  have hper := periodic_prefix L hL a b (L - 1) (Nat.le_refl _)
  have hper' := congrArg (fun t : Int => b ^ (L - 1) * t) hper
  have hnB : b ^ (N L) * b ^ 2 = b ^ m * b ^ L := by
    rw [← int_pow_add, ← int_pow_add]
    congr 1; omega
  have hnA : a ^ (N L) * a * a = a ^ m * a ^ L := by
    rw [← Int.pow_succ, ← Int.pow_succ, ← int_pow_add]
    congr 1; omega
  have hbL : b ^ (L - 1) * b = b ^ L := by
    rw [← Int.pow_succ, show L - 1 + 1 = L by omega]
  have haL : a ^ (L - 1) * a = a ^ L := by
    rw [← Int.pow_succ, show L - 1 + 1 = L by omega]
  have hnAP : a ^ (N L) * a * a ^ (L - 1) = a ^ (N L) * a ^ L := by
    rw [← haL]; ac_rfl
  have hnAP2 : a ^ (N L) * a * (a * geom a b (L - 1)) =
      a ^ m * a ^ L * geom a b (L - 1) := by
    rw [← hnA]; ac_rfl
  have hper'' : (b ^ L - a ^ L) * (b ^ (L - 1) * pre L a b m) =
      b ^ L * geom a b (L - 1) * (b ^ m - a ^ m) := by
    change _ = b ^ L * geom a b (L - 1) * (b ^ m - a ^ m)
    have hid : b ^ (L - 1) * (b * geom a b (L - 1) * (b ^ m - a ^ m)) =
        b ^ L * geom a b (L - 1) * (b ^ m - a ^ m) := by rw [← hbL]; ac_rfl
    change b ^ (L - 1) * ((b ^ L - a ^ L) * pre L a b m) =
      b ^ (L - 1) * (b * geom a b (L - 1) * (b ^ m - a ^ m)) at hper'
    rw [hid] at hper'
    family_ring
  rw [P, ← Int.mul_assoc, hnB]
  have hrhs : a ^ (N L) * (b ^ L + a * (a * geom a b (L - 1) - a ^ (L - 1))) =
      a ^ (N L) * b ^ L + a ^ m * a ^ L * geom a b (L - 1) - a ^ (N L) * a ^ L := by
    family_ring
  rw [hrhs]
  dsimp [m] at *
  family_ring

/-- The linear form is an odd multiple of precisely the asserted power of `a_k`. -/
theorem odd_multiple {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    ∃ Q : Int, Q % 2 = 1 ∧ E L p q k = a L k ^ (N L) * Q := by
  let a := a L k
  let b := b L k
  let d := D L q k
  let v := u L p q k
  rcases tower_congruence hL hr k (N L + 1) (by omega) with ⟨r, hh⟩
  have hsub : N L + 1 - 1 = N L := by omega
  rw [hsub, Int.pow_succ] at hh
  have hp := approximant_identity L (by omega) a b
  have hpD := congrArg (fun t : Int => d * t) hp
  have hrP := congrArg (fun t : Int => (b ^ L - a ^ L) * t) hh
  let T := d * (a * geom a b (L - 1) - a ^ (L - 1)) - r * (b ^ L - a ^ L)
  have hfact : b ^ (N L) * E L p q k = a ^ (N L) * (d * b ^ L + a * T) := by
    change b ^ (N L) * v - d * pre L a b (N L + 1) = a ^ (N L) * a * r at hh
    change (b ^ L - a ^ L) * (b ^ (N L) * v - d * pre L a b (N L + 1)) =
      (b ^ L - a ^ L) * (a ^ (N L) * a * r) at hrP
    change b ^ (N L) * (d * P L a b - v * (b ^ L - a ^ L)) = _
    dsimp [T]
    family_ring
  have hbez : IsBezout (a ^ (N L)) (b ^ (N L)) := IsBezout.pow (ab_coprime L k) _ _
  have hd : a ^ (N L) ∣ E L p q k := IsBezout.dvd_of_dvd_mul_left hbez ⟨_, hfact⟩
  rcases hd with ⟨Q, hQ⟩
  refine ⟨Q, ?_, hQ⟩
  have hap : 0 < a ^ (N L) := pow_pos_of_pos (by have := (ab_bounds L hL k).1; omega) _
  have hcancel : b ^ (N L) * Q = d * b ^ L + a * T := by
    apply Int.eq_of_mul_eq_mul_left (a := a ^ (N L)) (by omega)
    rw [← hfact, hQ]; ac_rfl
  have haeven : a % 2 = 0 := (ab_bounds L hL k).2.2.2.1
  have hbodd : b % 2 = 1 := (ab_bounds L hL k).2.2.2.2
  have hdodd : d % 2 = 1 := (denominator_props hL hr.1 hr.2.1 k).2
  have hodd := odd_mul_odd hdodd (odd_pow hbodd L)
  have heven := even_mul haeven T
  have hmod : (b ^ (N L) * Q) % 2 = 1 := by rw [hcancel]; omega
  rw [Int.mul_emod, odd_pow hbodd, Int.one_mul] at hmod
  omega

/-- An elementary exact valuation certificate, avoiding any analytic interpretation. -/
theorem odd_multiple_bounds (e : Int) (m : Nat)
    (hf : ∃ Q : Int, Q % 2 = 1 ∧ e = (2 : Int) ^ m * Q) :
    e ≠ 0 ∧ (2 : Int) ^ m ∣ e ∧ ¬ (2 : Int) ^ (m + 1) ∣ e ∧ (2 : Int) ^ m ≤ absInt e := by
  rcases hf with ⟨Q, ho, he⟩
  have hp := pow_pos_of_pos (x := 2) (by decide) m
  have hQ : Q ≠ 0 := by omega
  have hq := absInt_pos_of_ne_zero hQ
  have habs : absInt e = (2 : Int) ^ m * absInt Q := by
    rw [he, absInt_mul, absInt_of_nonneg (by omega)]
  have hlo := Int.mul_le_mul_of_nonneg_left hq (by omega : 0 ≤ (2 : Int) ^ m)
  refine ⟨?_, ⟨Q, he⟩, ?_, ?_⟩
  · intro hz; rw [hz] at habs
    have habs0 : absInt 0 = 0 := rfl
    rw [habs0] at habs
    omega
  · intro hd
    rcases hd with ⟨r, hr⟩
    rw [Int.pow_succ] at hr
    have hh : Q = 2 * r := by
      apply Int.eq_of_mul_eq_mul_left (a := (2 : Int) ^ m) (by omega)
      rw [← he, hr]; ac_rfl
    omega
  · omega

/-- Exact divisibility, nondivisibility, nonvanishing and the absolute-value lower bound. -/
theorem valuation {L : Nat} (hL : 4 ≤ L) {p q : Int}
    (hr : RealizesWord p q (familyWord L)) (k : Nat) :
    let m := N L * L ^ (k + 1)
    E L p q k ≠ 0 ∧ (2 : Int) ^ m ∣ E L p q k ∧
      ¬ (2 : Int) ^ (m + 1) ∣ E L p q k ∧ (2 : Int) ^ m ≤ absInt (E L p q k) := by
  apply odd_multiple_bounds
  rcases odd_multiple hL hr k with ⟨Q, ho, he⟩
  refine ⟨Q, ho, ?_⟩
  rw [a_closed, int_pow_mul] at he
  have hexp : L * L ^ k * N L = N L * L ^ (k + 1) := by
    rw [Nat.pow_succ]; ac_rfl
  rw [hexp] at he
  exact he

end CollatzLab.Family
