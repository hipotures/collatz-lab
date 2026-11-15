import CollatzLab.TwoReturn

/-! Exact finite parity cylinders and signed rational reconstruction heights. -/
namespace CollatzLab.RationalHeight
open CollatzLab Morphism

def Prefix (q p : Int) (v : Nat → Bool) (N : Nat) : Prop :=
  ∀ j, j < N → seedParity q p j = bit (v j)

def InLattice (A : Int) (N : Nat) (p q : Int) : Prop :=
  (2 : Int) ^ N ∣ p - A * q

def height (p q : Int) : Nat := max p.natAbs q.natAbs

theorem odd_cancel (N : Nat) {d x : Int} (hd : d % 2 = 1)
    (h : (2 : Int) ^ N ∣ d * x) : (2 : Int) ^ N ∣ x := by
  have hb : IsBezout 2 d := ⟨-(d / 2), 1, by omega⟩
  exact (hb.pow_left N).dvd_of_dvd_mul_left h

theorem parity_cross_iff {p q r s : Int} (hq : q % 2 = 1) (hs : s % 2 = 1) :
    p % 2 = r % 2 ↔ (2 : Int) ∣ p * s - r * q := by
  have hm : (p * s - r * q) % 2 = (p % 2 - r % 2) % 2 := by
    simp [Int.sub_emod, Int.mul_emod, hq, hs]
  constructor
  · intro he
    apply Int.dvd_of_emod_eq_zero
    rw [hm, he]
    simp
  · intro hd
    have hz := Int.emod_eq_zero_of_dvd hd
    rw [hm] at hz
    omega

theorem cross_step {p q r s : Int} (hq : q % 2 = 1) (hs : s % 2 = 1)
    (hp : p % 2 = r % 2) :
    ∃ c : Int, c % 2 = 1 ∧
      2 * (numStep q p * s - numStep s r * q) = c * (p * s - r * q) := by
  have h1 := numStep_eq q p hq
  have h2 := numStep_eq s r hs
  by_cases hz : p % 2 = 0
  · refine ⟨1, by decide, ?_⟩
    have hp1 := h1.1 hz
    have hp2 := h2.1 (by omega)
    have hmul1 := congrArg (fun x : Int => x * s) hp1
    have hmul2 := congrArg (fun x : Int => x * q) hp2
    family_ring
  · refine ⟨3, by decide, ?_⟩
    have hp1 := h1.2 (by omega)
    have hp2 := h2.2 (by omega)
    have hmul1 := congrArg (fun x : Int => x * s) hp1
    have hmul2 := congrArg (fun x : Int => x * q) hp2
    family_ring

theorem cross_step_dvd (N : Nat) {p q r s : Int}
    (hq : q % 2 = 1) (hs : s % 2 = 1) (hp : p % 2 = r % 2) :
    (2 : Int) ^ (N + 1) ∣ p * s - r * q ↔
      (2 : Int) ^ N ∣ numStep q p * s - numStep s r * q := by
  rcases cross_step hq hs hp with ⟨c, hc, he⟩
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    rw [Int.pow_succ] at hd
    rw [hd] at he
    family_ring
  · rintro ⟨d, hd⟩
    apply odd_cancel (N + 1) hc
    refine ⟨d, ?_⟩
    rw [hd] at he
    rw [Int.pow_succ]
    family_ring

/-- Finite isometry in actual numerator semantics, for either sign of q,s. -/
theorem prefix_cross_iff : ∀ N (p q r s : Int), q % 2 = 1 → s % 2 = 1 →
    ((∀ j, j < N → seedParity q p j = seedParity s r j) ↔
      (2 : Int) ^ N ∣ p * s - r * q)
  | 0, p, q, r, s, _, _ => by simp
  | N + 1, p, q, r, s, hq, hs => by
    constructor
    · intro h
      have hp : p % 2 = r % 2 := h 0 (by omega)
      apply (cross_step_dvd N hq hs hp).2
      apply (prefix_cross_iff N _ q _ s hq hs).1
      intro j hj
      have hh := h (j + 1) (by omega)
      simpa only [seedParity, numIter_succ_shift] using hh
    · intro hd
      have hd2 : (2 : Int) ∣ p * s - r * q := by
        exact Int.dvd_trans ⟨(2 : Int) ^ N, by rw [Int.pow_succ]; ac_rfl⟩ hd
      have hp := (parity_cross_iff hq hs).2 hd2
      have ht := (prefix_cross_iff N _ q _ s hq hs).2
        ((cross_step_dvd N hq hs hp).1 hd)
      intro j hj
      cases j with
      | zero => exact hp
      | succ j =>
        have hh := ht j (by omega)
        simpa only [seedParity, numIter_succ_shift] using hh

theorem cylinder_iff {v : Nat → Bool} {N : Nat} {A p q : Int}
    (hA : Prefix 1 A v N) (hq : q % 2 = 1) :
    Prefix q p v N ↔ InLattice A N p q := by
  have he : Prefix q p v N ↔
      ∀ j, j < N → seedParity q p j = seedParity 1 A j := by
    constructor
    · intro h j hj; rw [h j hj, hA j hj]
    · intro h j hj; rw [h j hj, hA j hj]
  rw [he]
  simpa [InLattice] using prefix_cross_iff N p q A 1 hq (by decide)

theorem lattice_representation (A : Int) (N : Nat) (p q : Int) :
    InLattice A N p q ↔ ∃ k : Int, p = (2 : Int) ^ N * k + A * q := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩

theorem lattice_determinant (A : Int) (N : Nat) :
    (2 : Int) ^ N * 1 - 0 * A = (2 : Int) ^ N := by omega

/-- Dividing a common odd factor preserves all N congruence bits. -/
theorem divide_odd (A : Int) (N : Nat) {p q d : Int} (hd : d % 2 = 1)
    (h : InLattice A N (d * p) (d * q)) : InLattice A N p q := by
  apply odd_cancel N hd
  have he : d * p - A * (d * q) = d * (p - A * q) := by family_ring
  simpa only [InLattice, he] using h

/-- Every finite parity cylinder has a representative integer in [0,2^N). -/
theorem residue_exists (v : Nat → Bool) (N : Nat) :
    ∃ A : Int, 0 ≤ A ∧ A < (2 : Int) ^ N ∧ Prefix 1 A v N := by
  rcases finiteWord_realized N v with ⟨p, q, hr⟩
  have hb : IsBezout 2 q := ⟨-(q / 2), 1, by have := hr.2.1; omega⟩
  rcases hb.pow_left N with ⟨u, z, hz⟩
  let A := (p * z) % (2 : Int) ^ N
  have hM := pow_pos_of_pos (x := (2 : Int)) (by decide) N
  have he := Int.emod_add_ediv (p * z) ((2 : Int) ^ N)
  have hd : (2 : Int) ^ N ∣ A * q - p * 1 := by
    refine ⟨-(p * u + q * ((p * z) / (2 : Int) ^ N)), ?_⟩
    have hm := congrArg (fun x : Int => p * x) hz
    have ht := congrArg (fun x : Int => q * x) he
    dsimp [A]
    family_ring
  refine ⟨A, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hM, ?_⟩
  have hh := (prefix_cross_iff N A 1 p q (by decide) hr.2.1).2 hd
  intro j hj
  rw [hh j hj, hr.2.2 j]
  simp [finiteWord, hj]

theorem residue_unique {v : Nat → Bool} {N : Nat} {A B : Int}
    (hA : 0 ≤ A ∧ A < (2 : Int) ^ N ∧ Prefix 1 A v N)
    (hB : 0 ≤ B ∧ B < (2 : Int) ^ N ∧ Prefix 1 B v N) : A = B := by
  have hd := (prefix_cross_iff N A 1 B 1 (by decide) (by decide)).1
    (fun j hj => (hA.2.2 j hj).trans (hB.2.2 j hj).symm)
  simp only [Int.mul_one] at hd
  have hm := (Int.emod_eq_emod_iff_emod_sub_eq_zero).2 (Int.emod_eq_zero_of_dvd hd)
  rw [Int.emod_eq_of_lt hA.1 hA.2.1, Int.emod_eq_of_lt hB.1 hB.2.1] at hm
  exact hm

noncomputable def residue (v : Nat → Bool) (N : Nat) : Int :=
  Classical.choose (residue_exists v N)

theorem residue_spec (v : Nat → Bool) (N : Nat) :
    0 ≤ residue v N ∧ residue v N < (2 : Int) ^ N ∧ Prefix 1 (residue v N) v N :=
  Classical.choose_spec (residue_exists v N)

theorem parity_lattice_iff (v : Nat → Bool) (N : Nat) (p q : Int)
    (hq : q % 2 = 1) : Prefix q p v N ↔ InLattice (residue v N) N p q :=
  cylinder_iff (residue_spec v N).2.2 hq

theorem minimum_exists (v : Nat → Bool) (N : Nat) :
    ∃ B : Nat, (∃ p q : Int, 0 < q ∧ q % 2 = 1 ∧ Prefix q p v N ∧ height p q = B) ∧
      ∀ p q : Int, 0 < q → q % 2 = 1 → Prefix q p v N → B ≤ height p q := by
  classical
  let P := fun B => ∃ p q : Int, 0 < q ∧ q % 2 = 1 ∧ Prefix q p v N ∧ height p q = B
  have least : ∀ b : Nat, P b → ∃ B, P B ∧ ∀ k, P k → B ≤ k := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro hb
      by_cases hh : ∃ k, k < b ∧ P k
      · rcases hh with ⟨k, hk, hp⟩
        exact ih k hk hp
      · refine ⟨b, hb, ?_⟩
        intro k hk
        by_cases h : b ≤ k
        · exact h
        · exact False.elim (hh ⟨k, by omega, hk⟩)
  have hr := residue_spec v N
  rcases least (height (residue v N) 1) ⟨_, 1, by decide, by decide, hr.2.2, rfl⟩ with
    ⟨B, hB, hmin⟩
  exact ⟨B, hB, fun p q hp hq hv => hmin _ ⟨p, q, hp, hq, hv, rfl⟩⟩

noncomputable def H (v : Nat → Bool) (N : Nat) : Nat :=
  Classical.choose (minimum_exists v N)

theorem H_spec (v : Nat → Bool) (N : Nat) :
    (∃ p q : Int, 0 < q ∧ q % 2 = 1 ∧ Prefix q p v N ∧ height p q = H v N) ∧
      ∀ p q : Int, 0 < q → q % 2 = 1 → Prefix q p v N → H v N ≤ height p q :=
  Classical.choose_spec (minimum_exists v N)

theorem H_mono (v : Nat → Bool) {N M : Nat} (hnm : N ≤ M) : H v N ≤ H v M := by
  rcases (H_spec v M).1 with ⟨p, q, hp, hq, hv, he⟩
  rw [← he]
  exact (H_spec v N).2 p q hp hq (fun j hj => hv j (by omega))

theorem H_positive (v : Nat → Bool) (N : Nat) : 1 ≤ H v N := by
  rcases (H_spec v N).1 with ⟨p, q, hp, _, _, he⟩
  have hq := Int.natAbs_of_nonneg (show 0 ≤ q by omega)
  have hh : q.natAbs ≤ height p q := Nat.le_max_right ..
  omega

theorem H_zero (v : Nat → Bool) : H v 0 = 1 := by
  have h := (H_spec v 0).2 0 1 (by decide) (by decide) (by intro j hj; omega)
  have hp := H_positive v 0
  change H v 0 ≤ 1 at h
  omega

theorem H_centered_bound (v : Nat → Bool) (N : Nat) : H v (N + 1) ≤ 2 ^ N := by
  let A := residue v (N + 1)
  let M := (2 : Int) ^ N
  have hp := pow_pos_of_pos (x := (2 : Int)) (by decide) N
  have hspec := residue_spec v (N + 1)
  have hAp : 0 ≤ A ∧ A < M * 2 := by
    simpa only [A, M, Int.pow_succ] using ⟨hspec.1, hspec.2.1⟩
  let p := if A ≤ M then A else A - M * 2
  have hpp : -M ≤ p ∧ p ≤ M := by dsimp [p]; split <;> omega
  have hd : InLattice A (N + 1) p 1 := by
    dsimp [InLattice, p]
    split
    · simp
    · refine ⟨-1, ?_⟩
      rw [Int.pow_succ]
      dsimp [M]; omega
  have hv := (cylinder_iff hspec.2.2 (by decide : (1 : Int) % 2 = 1)).2 hd
  have hh := (H_spec v (N + 1)).2 p 1 (by decide) (by decide) hv
  have ha : p.natAbs ≤ 2 ^ N := by
    have he : (p.natAbs : Int) ≤ M := by
      cases hp' : p with
      | ofNat z => simp only [hp', Int.natAbs_ofNat] at *; omega
      | negSucc z => simp only [hp', Int.natAbs_negSucc] at *; omega
    exact Int.ofNat_le.mp (by simpa only [M, Int.natCast_pow] using he)
  have h1 : 1 ≤ 2 ^ N := by
    have := Family.pow_ge_one (x := (2 : Int)) (by decide) N
    exact Int.ofNat_le.mp (by simpa only [Int.natCast_pow] using this)
  exact Nat.le_trans hh (Nat.max_le.mpr ⟨ha, h1⟩)

/-- The minimum over all odd-denominator pairs is attained only primitively. -/
theorem minimizer_primitive {v : Nat → Bool} {N : Nat} {p q : Int}
    (hp : 0 < q) (hq : q % 2 = 1) (hv : Prefix q p v N)
    (hh : height p q = H v N) : p.gcd q = 1 := by
  let d := p.gcd q
  have hqabs : 0 < q.natAbs := Int.natAbs_pos.mpr (by omega)
  have hd : 0 < d := Nat.gcd_pos_of_pos_right p.natAbs hqabs
  rcases (Int.gcd_dvd_left (a := p) (b := q)) with ⟨a, ha⟩
  rcases (Int.gcd_dvd_right (a := p) (b := q)) with ⟨b, hb⟩
  change p = (d : Int) * a at ha
  change q = (d : Int) * b at hb
  have hdo : (d : Int) % 2 = 1 := by
    by_cases hz : (d : Int) % 2 = 0
    · have he : q % 2 = 0 := by rw [hb, Int.mul_emod]; change ((d : Int) % 2 * _) % 2 = 0; simp [hz]
      omega
    · omega
  have hbo : b % 2 = 1 := by
    have he := hq
    rw [hb, Int.mul_emod] at he
    change (((d : Int) % 2) * (b % 2)) % 2 = 1 at he
    simpa [hdo] using he
  have hbp : 0 < b := by
    by_cases h : 0 < b
    · exact h
    · have he := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (d : Int) by omega)
        (show b ≤ 0 by omega)
      change (d : Int) * b ≤ 0 at he
      change q = (d : Int) * b at hb
      omega
  have heq : a * q = p * b := by
    have h1 := congrArg (fun x : Int => x * b) ha
    have h2 := congrArg (fun x : Int => a * x) hb
    family_ring
  have hva : Prefix b a v N := by
    intro j hj
    rw [(numIter_equiv hbo hq heq j).2]
    exact hv j hj
  have hmin := (H_spec v N).2 a b hbp hbo hva
  have hf : height p q = d * height a b := by
    have hpa := congrArg Int.natAbs ha
    have hqb := congrArg Int.natAbs hb
    simp only [Int.natAbs_mul, Int.natAbs_ofNat] at hpa hqb
    unfold height
    rw [hpa, hqb, Nat.mul_max_mul_left]
  have hpos : 1 ≤ height a b := by
    have hbabs := Int.natAbs_pos.mpr (show b ≠ 0 by omega)
    have he : b.natAbs ≤ height a b := Nat.le_max_right ..
    omega
  by_cases hd1 : d = 1
  · exact hd1
  · have hmul := Nat.mul_le_mul_right (height a b) (show 2 ≤ d by omega)
    omega

theorem height_bounds (p q : Int) :
    absInt p ≤ (height p q : Int) ∧ absInt q ≤ (height p q : Int) := by
  rw [absInt_eq_natAbs, absInt_eq_natAbs]
  exact ⟨Int.ofNat_le.mpr (Nat.le_max_left ..), Int.ofNat_le.mpr (Nat.le_max_right ..)⟩

/-- Keep both heights: this is useful for a shadow crossing, not only uniqueness. -/
theorem cross_height_bound (p q r s : Int) :
    absInt (p * s - r * q) ≤ 2 * (height p q : Int) * (height r s : Int) := by
  have h0 := absInt_sub_le (p * s) (r * q)
  rw [absInt_mul, absInt_mul] at h0
  rcases height_bounds p q with ⟨hp, hq⟩
  rcases height_bounds r s with ⟨hr, hs⟩
  have h1 := Int.mul_le_mul_of_nonneg_right hp (absInt_nonneg s)
  have h2 := Int.mul_le_mul_of_nonneg_left hs (show 0 ≤ (height p q : Int) by omega)
  have h3 := Int.mul_le_mul_of_nonneg_right hr (absInt_nonneg q)
  have h4 := Int.mul_le_mul_of_nonneg_left hq (show 0 ≤ (height r s : Int) by omega)
  family_ring

theorem same_prefix_height_separation {v : Nat → Bool} {N : Nat} {p q r s : Int}
    (hq : q % 2 = 1) (hs : s % 2 = 1)
    (hp : Prefix q p v N) (hr : Prefix s r v N) (hne : p * s ≠ r * q) :
    (2 : Int) ^ N ≤ 2 * (height p q : Int) * (height r s : Int) := by
  have hd := (prefix_cross_iff N p q r s hq hs).1
    (fun j hj => (hp j hj).trans (hr j hj).symm)
  rcases hd with ⟨d, hd⟩
  have hd0 : d ≠ 0 := by intro hz; rw [hz, Int.mul_zero] at hd; omega
  have hd1 := absInt_pos_of_ne_zero hd0
  have hM := pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) N
  have he : absInt (p * s - r * q) = (2 : Int) ^ N * absInt d := by
    rw [hd, absInt_mul, absInt_of_nonneg hM]
  have hl := Int.mul_le_mul_of_nonneg_left hd1 hM
  have hu := cross_height_bound p q r s
  omega

theorem bounded_height_unique {v : Nat → Bool} {N B : Nat} {p q r s : Int}
    (hq : q % 2 = 1) (hs : s % 2 = 1) (hp : Prefix q p v N) (hr : Prefix s r v N)
    (h1 : height p q ≤ B) (h2 : height r s ≤ B)
    (hsmall : 2 * B * B < 2 ^ N) : p * s = r * q := by
  by_cases he : p * s = r * q
  · exact he
  · have hlo := same_prefix_height_separation hq hs hp hr he
    have hB : 0 ≤ (B : Int) := by omega
    have hmul1 := Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr h1)
      (show 0 ≤ (height r s : Int) by omega)
    have hmul2 := Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr h2) hB
    have hhi : (2 : Int) * B * B < (2 : Int) ^ N := by
      exact_mod_cast hsmall
    family_ring

/-- A shadow that fails the next parity forces a height jump in that cylinder. -/
theorem shadow_crossing {v : Nat → Bool} {N : Nat} {p q : Int}
    (hq : q % 2 = 1) (hp : Prefix q p v N)
    (hfail : seedParity q p N ≠ bit (v N)) :
    (2 : Int) ^ N ≤ 2 * (height p q : Int) * (H v (N + 1) : Int) := by
  rcases (H_spec v (N + 1)).1 with ⟨r, s, _, hs, hr, he⟩
  have hne : p * s ≠ r * q := by
    intro h
    have ht := (numIter_equiv hq hs h N).2
    exact hfail (ht.trans (hr N (by omega)))
  have hh := same_prefix_height_separation hq hs hp (fun j hj => hr j (by omega)) hne
  simpa only [he] using hh

/-- Bounded finite reconstruction heights characterize rational realization,
without assuming eventual periodicity of any rational Collatz itinerary. -/
theorem bounded_iff_rational (v : Nat → Bool) :
    (∃ B K : Nat, ∀ N, K ≤ N → H v N ≤ B) ↔
      ∃ p q : Int, RealizesWord p q (fun j => bit (v j)) := by
  constructor
  · rintro ⟨B, K, hb⟩
    let N := K + 2 * B * B
    rcases (H_spec v N).1 with ⟨p, q, hp, hq, hv, he⟩
    have hsmall : 2 * B * B < 2 ^ N := by
      have hn := nat_lt_pow2 N
      dsimp [N] at *; omega
    have hbase : height p q ≤ B := by rw [he]; exact hb N (by dsimp [N]; omega)
    refine ⟨p, q, hp, hq, ?_⟩
    intro j
    let M := max N (j + 1)
    have hNM : N ≤ M := Nat.le_max_left ..
    have hjM : j < M := by have := Nat.le_max_right N (j + 1); dsimp [M]; omega
    have hKM : K ≤ M := by dsimp [N] at hNM; omega
    rcases (H_spec v M).1 with ⟨r, s, _, hs, hr, hf⟩
    have hbound : height r s ≤ B := by rw [hf]; exact hb M hKM
    have hcross := bounded_height_unique hq hs hv
      (fun a ha => hr a (by omega)) hbase hbound hsmall
    exact ((numIter_equiv hq hs hcross j).2).trans (hr j hjM)
  · rintro ⟨p, q, hr⟩
    refine ⟨height p q, 0, ?_⟩
    intro N _
    exact (H_spec v N).2 p q hr.1 hr.2.1 (fun j _ => hr.2.2 j)

end CollatzLab.RationalHeight
