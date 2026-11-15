import CollatzLab

/-! Issue #31: reviewer-owned semantic interfaces. Compile in the pinned
PR source's Lake environment. Only anonymous examples; no new library API. -/

open CollatzLab CollatzLab.Morphism CollatzLab.RationalHeight CollatzLab.FrontierHeight

-- Independently specified signed controls, including a nontrivial odd q.
example : seedParity 1 (-3) 0 = 1 ∧ seedParity 1 (-3) 1 = 0 ∧
    seedParity 1 (-3) 2 = 0 ∧ seedParity 1 (-3) 11 = 1 := by decide
example : seedParity 5 (-7) 0 = 1 ∧ seedParity 5 (-7) 1 = 0 ∧
    seedParity 5 (-7) 2 = 0 ∧ seedParity 5 (-7) 3 = 0 := by decide
example : seedParity (-5) 7 0 = seedParity 5 (-7) 0 ∧
    seedParity (-5) 7 7 = seedParity 5 (-7) 7 := by decide
example : ¬ RealizesWord 7 (-5) (fun _ => 1) := by
  intro h
  have := h.1
  omega
example : height (-7) (-5) = 7 ∧ height 0 1 = 1 := by decide

example (n : Nat) (p q r s : Int) (hq : q % 2 = 1) (hs : s % 2 = 1) :
    ((∀ j, j < n → seedParity q p j = seedParity s r j) ↔
      (2 : Int)^n ∣ p*s-r*q) := prefix_cross_iff n p q r s hq hs

example (v : Nat → Bool) (n : Nat) (p q : Int) (hq : q % 2 = 1) :
    ((∀ j, j < n → seedParity q p j = bit (v j)) ↔
      (2 : Int)^n ∣ p-residue v n*q) := parity_lattice_iff v n p q hq

example (v : Nat → Bool) (n : Nat) :
    (∃ p q : Int, 0 < q ∧ q % 2 = 1 ∧ Prefix q p v n ∧ height p q = H v n) ∧
      (∀ p q : Int, 0 < q → q % 2 = 1 → Prefix q p v n → H v n ≤ height p q) :=
  H_spec v n

example (v : Nat → Bool) (n : Nat) (p q : Int)
    (positive : 0 < q) (odd : q % 2 = 1) (hprefix : Prefix q p v n)
    (minimum : height p q = H v n) : p.gcd q = 1 :=
  minimizer_primitive positive odd hprefix minimum

example (v : Nat → Bool) :
    (∃ b k : Nat, ∀ n, k ≤ n → H v n ≤ b) ↔
      ∃ p q : Int, 0 < q ∧ q % 2 = 1 ∧ ∀ j, seedParity q p j = bit (v j) :=
  bounded_iff_rational v

example (k : Nat) :
    0 < shadowDen k ∧ shadowDen k % 2 = 1 ∧
      ∀ j, seedParity (shadowDen k) (shadowNum k) j = bit (shadow k j) :=
  shadow_realized k

example (k : Nat) :
    (∀ j, j < matchLength k → seedParity (shadowDen k) (shadowNum k) j =
      bit (word frontierSix j)) ∧
    seedParity (shadowDen k) (shadowNum k) (matchLength k) ≠
      bit (word frontierSix (matchLength k)) := ⟨shadow_prefix k, shadow_failure k⟩

example (k : Nat) : 5*matchLength k+1 = 56*6^k := matchLength_formula k

example (k : Nat) :
    7*((weight (word frontierSix) (3*6^k)+weight (word frontierSix) (6^k) : Nat) : Int) =
      20*(6^k : Nat)-6*(-1 : Int)^k := shadow_weight_sum k

example (k : Nat) : H (word frontierSix) (matchLength k) ≤
    14*6^k*3^(weight (word frontierSix) (3*6^k)+weight (word frontierSix) (6^k)) :=
  H_shadow_upper k

example (k n : Nat) (beyond : matchLength k < n) :
    (2 : Int)^matchLength k ≤
      2*(14*(6^k : Nat)*(3 : Int)^
        (weight (word frontierSix) (3*6^k)+weight (word frontierSix) (6^k)))*
      (H (word frontierSix) n : Int) := H_after_shadow k n beyond

example : H (word frontierSix) 11 = 3 ∧ H (word frontierSix) 12 = 513 :=
  ⟨H_eleven, H_twelve⟩
