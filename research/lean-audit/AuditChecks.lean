/-
  Independent adversarial checks of the definitions in Lean PR #9
  (hipotures/collatz-lab, commit ec67222eb3453f0ae32a08928b04e763783e4aa8),
  written for issue #10, Gate A. See research/lean-semantic-audit.md.

  This file is NOT part of a Lake package on this branch (the CollatzLab library
  only exists in PR #9). Run it against a checkout of PR #9:

      git fetch origin fable/phase5-mahler-generalization
      git show FETCH_HEAD:research/lean-audit/AuditChecks.lean > /tmp/AuditChecks.lean
      lake build && lake env lean /tmp/AuditChecks.lean

  Expected: no errors, and every `#print axioms` line lists a subset of
  `[propext, Classical.choice, Quot.sound]`. Nothing here is imported by the
  library; it only consumes it. No `sorry`, no extra axioms, no `native_decide`.
-/
import CollatzLab

namespace CollatzLabAudit
open CollatzLab

/-! ## A. The Lean word `w` is the fixed point of `μ(1)=1110, μ(0)=1101` -/

/-- Symbol `r` of the block `μ(b)`: `μ(1) = 1110`, `μ(0) = 1101`. -/
def muBlock (b : Int) (r : Nat) : Int :=
  if b = 1 then (if r = 3 then 0 else 1) else (if r = 2 then 0 else 1)

/-- `w(4n + r) = μ(w(n))_r`: `w` is a fixed point of the morphism `μ`. -/
theorem w_is_mu_fixed_point (n r : Nat) (hr : r < 4) :
    w (4 * n + r) = muBlock (w n) r := by
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [Nat.add_zero, w_mul4]
    rcases w_binary n with h | h <;> simp [muBlock, h]
  · rw [w_mul4_add1]
    rcases w_binary n with h | h <;> simp [muBlock, h]
  · rw [w_mul4_add2]
    rcases w_binary n with h | h <;> simp [muBlock, h]
  · rw [w_mul4_add3]
    rcases w_binary n with h | h <;> simp [muBlock, h]

/-- The base-4 recurrence has exactly one solution, so it pins `w` down. -/
theorem w_unique (v : Nat → Int)
    (h0 : ∀ n, v (4 * n) = 1) (h1 : ∀ n, v (4 * n + 1) = 1)
    (h2 : ∀ n, v (4 * n + 2) = v n) (h3 : ∀ n, v (4 * n + 3) = 1 - v n) :
    ∀ n, v n = w n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hmod with h | h | h | h
    · obtain ⟨m, hm⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
      subst hm
      rw [h0, w_mul4]
    · obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
      subst hm
      rw [h1, w_mul4_add1]
    · obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 2 := ⟨n / 4, by omega⟩
      subst hm
      rw [h2, w_mul4_add2]
      exact ih m (by omega)
    · obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 3 := ⟨n / 4, by omega⟩
      subst hm
      rw [h3, w_mul4_add3, ih m (by omega)]

/-- One application of `μ` to a finite word. -/
def muList : List Int → List Int
  | [] => []
  | b :: t => (if b = 1 then [1, 1, 1, 0] else [1, 1, 0, 1]) ++ muList t

set_option maxRecDepth 100000 in
/-- `μ^4(1)` (256 symbols), obtained by literally iterating the morphism,
    equals the first 256 values of the Lean function `w`. -/
theorem w_prefix_256_eq_mu_iterate :
    (List.range 256).map w = muList (muList (muList (muList [1]))) := by
  decide

/-- The first 64 symbols, written out, for comparison with the prose and Rust. -/
theorem w_prefix_64_explicit :
    (List.range 64).map w =
      [1,1,1,0, 1,1,1,0, 1,1,1,0, 1,1,0,1,
       1,1,1,0, 1,1,1,0, 1,1,1,0, 1,1,0,1,
       1,1,1,0, 1,1,1,0, 1,1,1,0, 1,1,0,1,
       1,1,1,0, 1,1,1,0, 1,1,0,1, 1,1,1,0] := by
  decide

/-! ## B. `RealizesWord` is satisfiable: it is not an empty predicate -/

theorem numIter_one_one : ∀ j : Nat, numIter 1 1 j = if j % 2 = 0 then 1 else 2
  | 0 => rfl
  | j + 1 => by
    have ih := numIter_one_one j
    show numStep 1 (numIter 1 1 j) = _
    rw [ih]
    by_cases h : j % 2 = 0
    · have h' : ¬ ((j + 1) % 2 = 0) := by omega
      rw [if_pos h, if_neg h']
      decide
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [if_neg h, if_pos h']
      decide

/-- The positive integer `1` (the trivial cycle `1 → 2 → 1`) realizes `(10)^∞`. -/
theorem realizes_trivial_cycle :
    RealizesWord 1 1 (fun j => if j % 2 = 0 then 1 else 0) := by
  refine ⟨by decide, by decide, ?_⟩
  intro j
  unfold seedParity
  rw [numIter_one_one j]
  by_cases h : j % 2 = 0 <;> simp [h]

theorem numIter_control : ∀ j : Nat,
    numIter 11 (-19) j =
      if j % 4 = 0 then -19 else if j % 4 = 1 then -23 else if j % 4 = 2 then -29 else -38
  | 0 => rfl
  | j + 1 => by
    have ih := numIter_control j
    show numStep 11 (numIter 11 (-19) j) = _
    rw [ih]
    have hmod : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    rcases hmod with h | h | h | h
    · have e0 : ¬ ((j + 1) % 4 = 0) := by omega
      have e1 : (j + 1) % 4 = 1 := by omega
      rw [if_pos h, if_neg e0, if_pos e1]
      decide
    · have a0 : ¬ (j % 4 = 0) := by omega
      have e0 : ¬ ((j + 1) % 4 = 0) := by omega
      have e1 : ¬ ((j + 1) % 4 = 1) := by omega
      have e2 : (j + 1) % 4 = 2 := by omega
      rw [if_neg a0, if_pos h, if_neg e0, if_neg e1, if_pos e2]
      decide
    · have a0 : ¬ (j % 4 = 0) := by omega
      have a1 : ¬ (j % 4 = 1) := by omega
      have e0 : ¬ ((j + 1) % 4 = 0) := by omega
      have e1 : ¬ ((j + 1) % 4 = 1) := by omega
      have e2 : ¬ ((j + 1) % 4 = 2) := by omega
      rw [if_neg a0, if_neg a1, if_pos h, if_neg e0, if_neg e1, if_neg e2]
      decide
    · have a0 : ¬ (j % 4 = 0) := by omega
      have a1 : ¬ (j % 4 = 1) := by omega
      have a2 : ¬ (j % 4 = 2) := by omega
      have e0 : (j + 1) % 4 = 0 := by omega
      rw [if_neg a0, if_neg a1, if_neg a2, if_pos e0]
      decide

/-- The periodic control word `(1110)^∞` IS realized by the rational seed `-19/11`.
    So the predicate that `no_rational_seed_realizes_w` negates is satisfiable for a
    word that agrees with `w` on its first 14 symbols. -/
theorem realizes_periodic_control :
    RealizesWord (-19) 11 (fun j => if j % 4 = 3 then 0 else 1) := by
  refine ⟨by decide, by decide, ?_⟩
  intro j
  unfold seedParity
  rw [numIter_control j]
  have hmod : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases hmod with h | h | h | h <;> simp [h]

set_option maxRecDepth 100000 in
/-- A positive integer whose first 64 accelerated-Collatz parities are exactly
    `w(0), …, w(63)` (computed independently in Python by three methods). -/
theorem finite_prefix_witness :
    ∀ j : Nat, j < 64 → seedParity 1 9941361107984147175 j = w j := by
  decide

set_option maxRecDepth 100000 in
/-- The same integer is the unique residue class: it stops matching at step 64
    or later only because it is not the 2-adic seed itself. Its 64-step image is
    larger than the seed (coefficient noncrossing in action). -/
theorem finite_prefix_witness_grows :
    tIterInt 9941361107984147175 64 > 9941361107984147175 := by
  decide

/-- Lean core `Int` division and remainder are Euclidean (`-7 / 2 = -4`, `-7 % 2 = 1`),
    which is what the parity test `p % 2 = 0` in `numStep` needs for negative `p`. -/
theorem int_div_mod_are_euclidean : (-7 : Int) / 2 = -4 ∧ (-7 : Int) % 2 = 1 := by
  decide

/-- One odd step from a negative rational: `T(-19/11) = -23/11`. -/
theorem numStep_negative_example : numStep 11 (-19) = -23 := by
  decide

/-- Integer-division sanity: on odd `p` and odd `q` the odd branch is exact. -/
theorem numStep_odd_exact (q p : Int) (hq : q % 2 = 1) (hp : p % 2 = 1) :
    2 * numStep q p = 3 * p + q := (numStep_eq q p hq).2 hp

/-- Negative numerators use Euclidean remainder, so parity is still in `{0,1}`. -/
theorem seedParity_binary (q p : Int) (j : Nat) :
    seedParity q p j = 0 ∨ seedParity q p j = 1 := by
  unfold seedParity; omega

/-! ## C. Documentation claims that are NOT what the Lean theorems say -/

/-- `research/lean-formalization.md` and the PR body describe Theorem 3.1 (strong)
    as `4 * oddSteps k ≥ 3 * k + 1`. That inequality is false already at `k = 4`. -/
theorem documented_strong_form_is_false : ¬ (4 * oddSteps 4 ≥ 3 * 4 + 1) := by
  decide

/-- The mapping table defines `w` by `w(4m)=w(m), w(4m+1)=1, w(4m+2)=1, w(4m+3)=0`.
    The Lean `w` does not satisfy `w(4m+2) = 1`: `w(14) = 0`. -/
theorem documented_recurrence_is_false : w (4 * 3 + 2) ≠ 1 := by
  decide

/-- …nor `w(4m+3) = 0`: `w(15) = 1`. -/
theorem documented_recurrence_is_false' : w (4 * 3 + 3) ≠ 0 := by
  decide

end CollatzLabAudit

/-! ## D. Axiom audit of every headline theorem and of the checks above -/
#print axioms CollatzLab.w_mul4
#print axioms CollatzLab.w_mul4_add1
#print axioms CollatzLab.w_mul4_add2
#print axioms CollatzLab.w_mul4_add3
#print axioms CollatzLab.w_binary
#print axioms CollatzLab.all_prefixes_survive_strong
#print axioms CollatzLab.all_prefixes_survive
#print axioms CollatzLab.w_not_eventually_periodic
#print axioms CollatzLab.numIter_equiv
#print axioms CollatzLab.numIter_block4
#print axioms CollatzLab.iter4L_affine_identity
#print axioms CollatzLab.base_tower_identity
#print axioms CollatzLab.preS_mahler_4L
#print axioms CollatzLab.uncancelled_d1_divisible_by_256
#print axioms CollatzLab.isBezout_aTower_bTower
#print axioms CollatzLab.dTower_pos_and_odd
#print axioms CollatzLab.tower_congruence_all
#print axioms CollatzLab.deltaTower_exact_div
#print axioms CollatzLab.pade4_identity
#print axioms CollatzLab.eForm_odd_multiple_of_aTower14
#print axioms CollatzLab.theorem_7_1_part1
#print axioms CollatzLab.hTower_closed_bound
#print axioms CollatzLab.eForm_upper_bound
#print axioms CollatzLab.exponential_bound_from_seed
#print axioms CollatzLab.no_rational_seed_realizes_w
#print axioms CollatzLab.no_int_seed_realizes_w
#print axioms CollatzLab.realizes_shiftWord_pred
#print axioms CollatzLab.no_rational_seed_realizes_shifted_w
#print axioms CollatzLab.no_int_seed_realizes_shifted_w
#print axioms CollatzLab.no_eventually_shifted_w_itinerary
#print axioms CollatzLab.no_int_orbit_enters_shifted_w
#print axioms CollatzLabAudit.w_is_mu_fixed_point
#print axioms CollatzLabAudit.w_unique
#print axioms CollatzLabAudit.w_prefix_256_eq_mu_iterate
#print axioms CollatzLabAudit.realizes_trivial_cycle
#print axioms CollatzLabAudit.realizes_periodic_control
#print axioms CollatzLabAudit.finite_prefix_witness

/-! ## E. The exact statements of the headline theorems, as elaborated -/
#check @CollatzLab.no_rational_seed_realizes_w
#check @CollatzLab.no_rational_seed_realizes_shifted_w
#check @CollatzLab.no_eventually_shifted_w_itinerary
#check @CollatzLab.all_prefixes_survive
#check @CollatzLab.w_not_eventually_periodic
#print CollatzLab.RealizesWord
#print CollatzLab.numStep
#print CollatzLab.seedParity
#eval (List.range 32).map CollatzLab.w
