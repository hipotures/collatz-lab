import CollatzLab.MorphismContraction

/-! Finite substitution-language certificates checked by ordinary reduction. -/
namespace CollatzLab.Morphism

def window (v : Nat → Bool) (h a : Nat) : List Bool :=
  List.ofFn (fun j : Fin h => v (a + j.val))

/-- Read a child window at offset `r` in the substituted parent list. Missing
parent entries default to zero; the correctness theorem proves none are read. -/
def expandWindow {L : Nat} (M : Images L) (h : Nat) (xs : List Bool) (r : Nat) : List Bool :=
  List.ofFn (fun j : Fin h =>
    image M ((xs[(r + j.val) / L]?).getD false) ((r + j.val) % L))

theorem window_parent_index {L h r j : Nat} (hL : 1 ≤ L) (hr : r < L) (hj : j < h) :
    (r + j) / L < h := by
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  cases h with
  | zero => omega
  | succ h =>
    have hm := Nat.mul_le_mul_left h hL
    simp only [Nat.mul_one] at hm
    rw [Nat.succ_mul]
    omega

theorem window_expand {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (h a r : Nat) (hr : r < L) :
    window (word M) h (L * a + r) = expandWindow M h (window (word M) h a) r := by
  apply congrArg List.ofFn
  funext j
  have hi := window_parent_index (by omega : 1 ≤ L) hr j.isLt
  simp only [window, expandWindow, List.getElem?_ofFn, dif_pos hi, Option.getD_some]
  rw [word_rec hL M h1, show L * a + r + j.val = L * a + (r + j.val) by omega,
    Nat.mul_add_div (by omega), Nat.mul_add_mod]

/-- A finite closed over-approximation to every length-`h` source window.
Concrete fields can be discharged by kernel evaluation of finite lists. -/
structure WindowCertificate {L : Nat} (M : Images L) (h : Nat) where
  language : List (List Bool)
  initial : window (word M) h 0 ∈ language
  closed : ∀ xs ∈ language, ∀ r : Fin L, expandWindow M h xs r.val ∈ language

/-- Strong induction on the starting index proves coverage of the infinite
fixed point from a finite closure certificate. No finite-prefix heuristic. -/
theorem window_certificate_covers {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) {h : Nat} (cert : WindowCertificate M h) (a : Nat) :
    window (word M) h a ∈ cert.language := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases ha : a = 0
    · subst a; exact cert.initial
    · have hp := ih (a / L) (Nat.div_lt_self (by omega) (by omega))
      have hm : a % L < L := Nat.mod_lt a (by omega)
      have he : L * (a / L) + a % L = a := by have := Nat.mod_add_div a L; omega
      have hh := window_expand hL M h1 h (a / L) (a % L) hm
      rw [he] at hh
      rw [hh]
      exact cert.closed _ hp ⟨a % L, hm⟩

def listImageWeight {L : Nat} (M : Images L) : List Bool → Nat
  | [] => 0
  | b :: xs => weight (image M b) L + listImageWeight M xs

theorem imageWeightSum_start {L : Nat} (M : Images L) (a : Nat) : ∀ h,
    imageWeightSum M a (h + 1) =
      weight (image M (word M a)) L + imageWeightSum M (a + 1) h
  | 0 => by simp [imageWeightSum]
  | h + 1 => by
    rw [imageWeightSum, imageWeightSum_start M a h, imageWeightSum]
    rw [show a + (h + 1) = a + 1 + h by omega]
    omega

theorem window_image_weight {L : Nat} (M : Images L) : ∀ h a,
    listImageWeight M (window (word M) h a) = imageWeightSum M a h
  | 0, a => by simp [window, listImageWeight, imageWeightSum]
  | h + 1, a => by
    rw [window, List.ofFn_succ, listImageWeight]
    change weight (image M (word M (a + 0))) L +
      listImageWeight M (List.ofFn (fun j : Fin h => word M (a + (j.val + 1)))) = _
    have he : (fun j : Fin h => word M (a + (j.val + 1))) =
        (fun j : Fin h => word M (a + 1 + j.val)) := by
      funext j; congr 1; omega
    rw [he, ← window, window_image_weight M h (a + 1), imageWeightSum_start]
    simp

/-- Finite language weight bounds imply the uniform infinite source-window
bound needed by variable-multiplier contraction. -/
theorem window_certificate_weight_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) {h R : Nat} (cert : WindowCertificate M h)
    (hw : ∀ xs ∈ cert.language, listImageWeight M xs ≤ R) (a : Nat) :
    imageWeightSum M a h ≤ R := by
  rw [← window_image_weight]
  exact hw _ (window_certificate_covers hL M h1 cert a)

theorem no_rational_seed_window_certificate {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) {h R : Nat} (hh : 1 ≤ h)
    (cert : WindowCertificate M h) (hw : ∀ xs ∈ cert.language, listImageWeight M xs ≤ R)
    (hgap : (3 : Int) ^ R < (2 : Int) ^ (L * h))
    (haper : ¬ EventuallyPeriodic (parityWord M)) (p q : Int) :
    ¬ RealizesWord p q (parityWord M) :=
  no_rational_seed_block_contraction hL M h1 h R hh
    (fun n => window_certificate_weight_bound hL M h1 cert hw (h * n)) hgap haper p q

def finiteOffset (xs : List Bool) : Int := offset (fun j => (xs[j]?).getD false) xs.length

theorem window_offset (v : Nat → Bool) (h a : Nat) :
    finiteOffset (window v h a) = offset (fun j => v (a + j)) h := by
  simp only [finiteOffset, window, List.length_ofFn]
  apply (common_prefix _ _ h ?_).2
  intro j hj
  simp [List.getElem?_ofFn, hj]

theorem window_source_expand {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (h a : Nat) :
    window (word M) (L * h) (L * a) =
      expandWindow M (L * h) (window (word M) h a) 0 := by
  apply congrArg List.ofFn
  funext j
  have hi : j.val / L < h :=
    (Nat.div_lt_iff_lt_mul (by omega)).2 (by simp [Nat.mul_comm])
  simp only [window, expandWindow, Nat.zero_add, List.getElem?_ofFn, dif_pos hi,
    Option.getD_some]
  rw [word_rec hL M h1, Nat.mul_add_div (by omega), Nat.mul_add_mod]

/-- A finite table of expanded offsets bounds every corresponding infinite
source-aligned chunk, with all boundary crossings already certified. -/
theorem window_certificate_offset_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) {h : Nat} (cert : WindowCertificate M h) (D : Int)
    (hd : ∀ xs ∈ cert.language, finiteOffset (expandWindow M (L * h) xs 0) ≤ D) (a : Nat) :
    offset (fun j => word M (L * a + j)) (L * h) ≤ D := by
  rw [← window_offset, window_source_expand hL M h1]
  exact hd _ (window_certificate_covers hL M h1 cert a)

end CollatzLab.Morphism
