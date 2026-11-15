import CollatzLab

/-! Independently stated interfaces: signs, finite quantifiers and actual seeds. -/
namespace CollatzLab.Phase13Signatures
open Morphism RationalHeight FrontierHeight

example (N : Nat) (p q r s : Int) (hq : q % 2 = 1) (hs : s % 2 = 1) :
    (∀ j, j < N → seedParity q p j = seedParity s r j) ↔
      (2 : Int) ^ N ∣ p * s - r * q := prefix_cross_iff N p q r s hq hs

example (v : Nat → Bool) (N : Nat) (p q : Int) (hq : q % 2 = 1) :
    (∀ j, j < N → seedParity q p j = bit (v j)) ↔
      (2 : Int) ^ N ∣ p - residue v N * q := parity_lattice_iff v N p q hq

example (v : Nat → Bool) (N : Nat) :
    (∃ p q : Int, 0 < q ∧ q % 2 = 1 ∧
      (∀ j, j < N → seedParity q p j = bit (v j)) ∧ height p q = H v N) ∧
    (∀ p q : Int, 0 < q → q % 2 = 1 →
      (∀ j, j < N → seedParity q p j = bit (v j)) → H v N ≤ height p q) := H_spec v N

example (v : Nat → Bool) (N : Nat) (p q : Int) (hp : 0 < q) (hq : q % 2 = 1)
    (hv : ∀ j, j < N → seedParity q p j = bit (v j)) (he : height p q = H v N) :
    p.gcd q = 1 := minimizer_primitive hp hq hv he

example (v : Nat → Bool) (N M : Nat) (hn : N ≤ M) : H v N ≤ H v M := H_mono v hn
example (v : Nat → Bool) (N : Nat) : H v (N + 1) ≤ 2 ^ N := H_centered_bound v N

example (v : Nat → Bool) :
    (∃ B K : Nat, ∀ N, K ≤ N → H v N ≤ B) ↔
      ∃ p q : Int, q > 0 ∧ q % 2 = 1 ∧ ∀ j, seedParity q p j = bit (v j) := bounded_iff_rational v

example (k : Nat) : RealizesWord (shadowNum k) (shadowDen k) (fun j => bit (shadow k j)) :=
  shadow_realized k

example (k : Nat) :
    (∀ j, j < matchLength k → seedParity (shadowDen k) (shadowNum k) j = bit (word frontierSix j)) ∧
    seedParity (shadowDen k) (shadowNum k) (matchLength k) ≠ bit (word frontierSix (matchLength k)) :=
  ⟨shadow_prefix k, shadow_failure k⟩

example (k : Nat) :
    5 * matchLength k + 1 = 56 * 6 ^ k ∧
    7 * ((weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k) : Nat) : Int) =
      20 * (6 ^ k : Nat) - 6 * (-1 : Int) ^ k := ⟨matchLength_formula k, shadow_weight_sum k⟩

example (k : Nat) : H (word frontierSix) (matchLength k) ≤
    14 * 6 ^ k * 3 ^ (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k)) :=
  H_shadow_upper k

example (k N : Nat) (hN : matchLength k < N) :
    (2 : Int) ^ matchLength k ≤ 2 *
      (14 * (6 ^ k : Nat) * (3 : Int) ^
        (weight (word frontierSix) (3 * 6 ^ k) + weight (word frontierSix) (6 ^ k))) *
          (H (word frontierSix) N : Int) := H_after_shadow k N hN

example : H (word frontierSix) 11 = 3 ∧ H (word frontierSix) 12 = 513 := ⟨H_eleven, H_twelve⟩

end CollatzLab.Phase13Signatures
