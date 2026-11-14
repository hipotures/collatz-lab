import CollatzLab.Shifted

/-!
The uniform family `mu_L(1) = 1^(L-1)0`, `mu_L(0) = 1^(L-2)01`.
The recursive definition has no seed or arithmetic assumptions.
-/
namespace CollatzLab

/-- The symbol at offset `r` in the image of `b` under `mu_L`. -/
def familyBlock (L : Nat) (b : Int) (r : Nat) : Int :=
  if r < L - 2 then 1 else if r = L - 2 then b else 1 - b

/-- Structural recursion with enough fuel to read the base-`L` digits of `n`. -/
def familyAux (L : Nat) : Nat → Nat → Int
  | 0, _ => 1
  | _ + 1, 0 => 1
  | f + 1, n => familyBlock L (familyAux L f (n / L)) (n % L)

/-- The infinite fixed point beginning in `1`. -/
def familyWord (L n : Nat) : Int := familyAux L n n

namespace Family

variable {L : Nat}

theorem aux_stable (hL : 3 ≤ L) : ∀ f g n, n ≤ f → n ≤ g →
    familyAux L f n = familyAux L g n
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
      simp only [familyAux, hn, aux_stable hL f g (n / L) (by omega) (by omega)]

theorem aux_eq (hL : 3 ≤ L) (f n : Nat) (hf : n ≤ f) :
    familyAux L f n = familyWord L n := aux_stable hL f n n hf (Nat.le_refl n)

theorem word_zero : familyWord L 0 = 1 := rfl

theorem word_rec (hL : 3 ≤ L) (n : Nat) :
    familyWord L n = familyBlock L (familyWord L (n / L)) (n % L) := by
  by_cases hn : n = 0
  · subst n; simp [familyWord, familyAux, familyBlock, show 0 < L - 2 by omega]
  · rw [← aux_eq hL (n + 1) n (by omega)]
    simp only [familyAux, hn, aux_eq hL n (n / L) (Nat.div_le_self ..)]

theorem word_block (hL : 3 ≤ L) (n r : Nat) (hr : r < L) :
    familyWord L (L * n + r) = familyBlock L (familyWord L n) r := by
  rw [word_rec hL]
  have hd : (L * n + r) / L = n := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr]
    omega
  have hm : (L * n + r) % L = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hd, hm]

theorem word_initial (hL : 3 ≤ L) (n r : Nat) (hr : r < L - 2) :
    familyWord L (L * n + r) = 1 := by
  rw [word_block hL n r (by omega)]; simp [familyBlock, hr]

theorem word_penult (hL : 3 ≤ L) (n : Nat) :
    familyWord L (L * n + (L - 2)) = familyWord L n := by
  rw [word_block hL n (L - 2) (by omega)]; simp [familyBlock]

theorem word_last (hL : 3 ≤ L) (n : Nat) :
    familyWord L (L * n + (L - 1)) = 1 - familyWord L n := by
  rw [word_block hL n (L - 1) (by omega)]
  simp [familyBlock, show ¬ L - 1 < L - 2 by omega, show L - 1 ≠ L - 2 by omega]

theorem aux_binary : ∀ f n, familyAux L f n = 0 ∨ familyAux L f n = 1
  | 0, _ => Or.inr rfl
  | _ + 1, 0 => Or.inr rfl
  | f + 1, n => by
    by_cases hn : n = 0
    · subst n; exact Or.inr rfl
    · simp only [familyAux, hn, familyBlock]
      split
      · exact Or.inr rfl
      · split
        · exact aux_binary f (n / L)
        · rcases aux_binary f (n / L) with h | h
          · right; omega
          · left; omega

theorem word_binary (L n : Nat) : familyWord L n = 0 ∨ familyWord L n = 1 :=
  aux_binary n n

/-- The block recurrence uniquely specifies the fixed point, without a seed premise. -/
theorem word_unique (hL : 3 ≤ L) (v : Nat → Int)
    (hv : ∀ n r, r < L → v (L * n + r) = familyBlock L (v n) r) :
    v = familyWord L := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hmod : n % L < L := Nat.mod_lt n (by omega)
    have hn : L * (n / L) + n % L = n := by
      have := Nat.mod_add_div n L; omega
    rw [← hn, hv _ _ hmod, word_block hL _ _ hmod]
    by_cases hsmall : n % L < L - 2
    · simp [familyBlock, hsmall]
    · have hpos : 0 < n := by
        by_cases h : n = 0
        · subst n; simp at hsmall; omega
        · omega
      rw [ih (n / L) (Nat.div_lt_self hpos (by omega))]

end Family

/-- Semantic correspondence with the existing, independently defined 4-automatic word. -/
theorem familyWord_four : familyWord 4 = w := by
  symm
  apply Family.word_unique (by decide)
  intro n r hr
  have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · simp [familyBlock]
  · simp [familyBlock]
  · simp [familyBlock]
  · simp [familyBlock]

/-- A concrete second-iterate prefix of `mu_5`, including its first changed block. -/
theorem familyWord_five_prefix :
    (List.range 25).map (familyWord 5) =
      [1,1,1,1,0, 1,1,1,1,0, 1,1,1,1,0, 1,1,1,1,0, 1,1,1,0,1] := by decide

end CollatzLab
