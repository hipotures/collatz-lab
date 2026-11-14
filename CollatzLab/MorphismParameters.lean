import CollatzLab.MorphismPrefix

/-! Canonical first/last positions and exact finite criterion instances. -/
namespace CollatzLab.Morphism

def firstIndex (P : Nat → Bool) (n : Nat) : Nat := (List.range n).findIdx P
def lastIndex (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if P n then n else lastIndex P n

theorem firstIndex_lt (P : Nat → Bool) (n : Nat)
    (h : ∃ j, j < n ∧ P j = true) : firstIndex P n < n := by
  have hh : ∃ j, j ∈ List.range n ∧ P j = true := by simpa using h
  simpa [firstIndex] using List.findIdx_lt_length.mpr hh

theorem firstIndex_hit (P : Nat → Bool) (n : Nat)
    (h : firstIndex P n < n) : P (firstIndex P n) = true := by
  have hb : (List.range n).findIdx P < (List.range n).length := by simpa [firstIndex] using h
  have hh := List.findIdx_getElem (w := hb)
  simpa [List.getElem_range, firstIndex] using hh

theorem before_firstIndex (P : Nat → Bool) (n j : Nat)
    (h : j < firstIndex P n) : P j = false := by
  have hh := List.not_of_lt_findIdx (xs := List.range n) (p := P) h
  simpa [List.getElem_range] using hh

theorem lastIndex_spec (P : Nat → Bool) : ∀ n,
    (∃ j, j < n ∧ P j = true) →
    lastIndex P n < n ∧ P (lastIndex P n) = true ∧
      (∀ j, j < n → P j = true → j ≤ lastIndex P n)
  | 0, h => by rcases h with ⟨j, hj, _⟩; omega
  | n + 1, h => by
    by_cases hn : P n = true
    · rw [lastIndex, if_pos hn]
      exact ⟨by omega, hn, fun j hj _ => by omega⟩
    · have he : ∃ j, j < n ∧ P j = true := by
        rcases h with ⟨j, hj, hp⟩
        exact ⟨j, by by_cases hjn : j = n; subst j; contradiction; omega, hp⟩
      rcases lastIndex_spec P n he with ⟨ha, hb, hc⟩
      rw [lastIndex, if_neg hn]
      refine ⟨by omega, hb, ?_⟩
      intro j hj hp
      apply hc j (by by_cases hjn : j = n; subst j; contradiction; omega) hp

def t {L : Nat} (M : Images L) := firstIndex (fun j => !(image M true j)) L
def s {L : Nat} (M : Images L) := firstIndex (fun j => image M false j != image M true j) L
def e {L : Nat} (M : Images L) := lastIndex (fun j => image M false j != image M true j) L
def N {L : Nat} (M : Images L) := L * t M + s M
def Criterion {L : Nat} (M : Images L) : Prop :=
  (2 : Int) ^ (L * (L - 1) * N M) > (max (A L) (B M)) ^ (L * L + e M)

theorem t_bounds {L : Nat} (_hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true)
    (hw : weight (image M false) L = weight (image M true) L)
    (hd : M.zero ≠ M.one) : 1 ≤ t M ∧ t M < L := by
  have he : ∃ j, j < L ∧ (!(image M true j)) = true := by
    rcases one_has_zero M hw hd with ⟨j, hj, hz⟩
    exact ⟨j, hj, by simp [hz]⟩
  have ht : t M < L := firstIndex_lt _ _ he
  have hh := firstIndex_hit (fun j => !(image M true j)) L ht
  have hn : t M ≠ 0 := by
    intro hz
    change (!(image M true (t M))) = true at hh
    rw [hz, h1] at hh
    contradiction
  exact ⟨by omega, ht⟩

theorem word_first_block {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (j : Nat) (hj : j < L) :
    word M j = image M true j := by
  simpa [word_zero] using word_block hL M h1 0 j hj

def sigma : Images 3 where
  zero := fun j => decide (1 ≤ j.val)
  one := fun j => decide (j.val < 2)

def thueMorse : Images 2 where
  zero := fun j => decide (j.val = 1)
  one := fun j => decide (j.val = 0)

def secondary : Images 3 where
  zero := fun j => decide (1 ≤ j.val)
  one := fun j => decide (j.val ≠ 1)

theorem sigma_admissible : image sigma true 0 = true ∧
    weight (image sigma false) 3 = weight (image sigma true) 3 ∧
    sigma.zero ≠ sigma.one := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := congrArg (fun f : Fin 3 → Bool => f ⟨0, by decide⟩) h
  change false = true at hh
  contradiction

theorem sigma_criterion : Criterion sigma := by unfold Criterion; decide

theorem thueMorse_admissible : image thueMorse true 0 = true ∧
    weight (image thueMorse false) 2 = weight (image thueMorse true) 2 ∧
    thueMorse.zero ≠ thueMorse.one := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := congrArg (fun f : Fin 2 → Bool => f ⟨0, by decide⟩) h
  change false = true at hh
  contradiction

theorem thueMorse_fails_criterion : ¬ Criterion thueMorse := by unfold Criterion; decide

theorem secondary_fails_criterion : ¬ Criterion secondary := by unfold Criterion; decide

theorem concrete_parameters :
    (t sigma, s sigma, e sigma, N sigma, A 3, B sigma) = (2, 0, 2, 6, 8, 9) ∧
    (t thueMorse, s thueMorse, e thueMorse, N thueMorse, A 2, B thueMorse) =
      (1, 0, 1, 2, 4, 3) := by decide

end CollatzLab.Morphism
