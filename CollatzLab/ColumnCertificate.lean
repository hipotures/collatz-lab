import CollatzLab.WindowCertificate

/-! Finite forced-column certificates for independent eventual aperiodicity. -/
namespace CollatzLab.Morphism

/-- One injective column permits period descent. Opposite forced columns
separate every nonzero residue, independently of the two parent symbols. -/
structure ColumnCertificate {L : Nat} (M : Images L) where
  distinguish : Fin L
  different : image M true distinguish.val ≠ image M false distinguish.val
  separate : Fin L → Fin L
  separates : ∀ r : Fin L, r.val ≠ 0 → ∀ b c : Bool,
    image M b (separate r).val ≠ image M c (((separate r).val + r.val) % L)

theorem column_injective {L : Nat} (M : Images L) (j : Fin L)
    (hd : image M true j.val ≠ image M false j.val) (b c : Bool)
    (he : image M b j.val = image M c j.val) : b = c := by
  cases b <;> cases c
  · rfl
  · exact False.elim (hd he.symm)
  · exact False.elim (hd he)
  · rfl

theorem bit_injective (b c : Bool) (he : bit b = bit c) : b = c := by
  cases b <;> cases c <;> simp [bit] at he ⊢

theorem column_certificate_not_periodic_from {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (cert : ColumnCertificate M) (p : Nat) :
    ∀ start, 1 ≤ p → (∀ n, start ≤ n → word M (n + p) = word M n) → False := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro start hp hper
    have hmul : ∀ n, n ≤ L * n := by
      intro n
      have hh := Nat.mul_le_mul_right n (show 1 ≤ L by omega)
      simpa using hh
    by_cases hz : p % L = 0
    · let d := p / L
      have hdiv : L ∣ p := Nat.dvd_of_mod_eq_zero hz
      have hpos : 1 ≤ d := Nat.div_pos (Nat.le_of_dvd hp hdiv) (by omega)
      have he : L * d = p := by dsimp [d]; have := Nat.mod_add_div p L; omega
      apply ih d (Nat.div_lt_self hp (by omega)) start hpos
      intro n hn
      have hh := hper (L * n + cert.distinguish.val) (by have := hmul n; omega)
      rw [show L * n + cert.distinguish.val + p = L * (n + d) + cert.distinguish.val by
        have := Nat.mul_add L n d; omega,
        word_block hL M h1 _ _ cert.distinguish.isLt,
        word_block hL M h1 _ _ cert.distinguish.isLt] at hh
      exact column_injective M cert.distinguish cert.different _ _ hh
    · let r : Fin L := ⟨p % L, Nat.mod_lt p (by omega)⟩
      let j := cert.separate r
      have hh := hper (L * start + j.val) (by have := hmul start; omega)
      rw [word_rec hL M h1 (L * start + j.val + p), word_block hL M h1 _ _ j.isLt] at hh
      have hm : (L * start + j.val + p) % L = (j.val + r.val) % L := by
        dsimp [r]
        rw [Nat.add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      rw [hm] at hh
      exact cert.separates r hz (word M start) (word M ((L * start + j.val + p) / L)) hh.symm

theorem column_certificate_not_eventually_periodic {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (cert : ColumnCertificate M) :
    ¬ EventuallyPeriodic (parityWord M) := by
  rintro ⟨start, p, hp, hper⟩
  apply column_certificate_not_periodic_from hL M h1 cert p start hp
  intro n hn
  exact bit_injective _ _ (hper n hn)

/-- All infinite premises of this criterion follow from the two finite
certificates. The numerical comparison is an exact integer inequality. -/
theorem no_rational_seed_finite_certificates {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (columns : ColumnCertificate M)
    {h R : Nat} (hh : 1 ≤ h) (windows : WindowCertificate M h)
    (hw : ∀ xs ∈ windows.language, listImageWeight M xs ≤ R)
    (hgap : (3 : Int) ^ R < (2 : Int) ^ (L * h)) (p q : Int) :
    ¬ RealizesWord p q (parityWord M) :=
  no_rational_seed_window_certificate hL M h1 hh windows hw hgap
    (column_certificate_not_eventually_periodic hL M h1 columns) p q

end CollatzLab.Morphism
