import CollatzLab.ColumnCertificate

/-! Serializable finite data and a decidable, kernel-checked validation contract. -/
namespace CollatzLab.Morphism

structure FiniteContractionEntry where
  length : Nat
  one : List Bool
  zero : List Bool
  blocks : Nat
  cap : Nat
  language : List (List Bool)
  distinguish : Nat
  separate : List Nat
  deriving DecidableEq

def FiniteContractionEntry.toImages (e : FiniteContractionEntry) : Images e.length where
  one := fun j => (e.one[j.val]?).getD false
  zero := fun j => (e.zero[j.val]?).getD false

def FiniteContractionEntry.separation (e : FiniteContractionEntry) (r : Nat) : Nat :=
  (e.separate[r]?).getD 0

/-- Every condition is finite and decidable. Infinite rational and word
properties appear only in the soundness theorem below. -/
def FiniteContractionEntry.Valid (e : FiniteContractionEntry) : Prop :=
  2 ≤ e.length ∧ 1 ≤ e.blocks ∧ e.one.length = e.length ∧ e.zero.length = e.length ∧
  e.separate.length = e.length ∧
  weight (image e.toImages true) e.length ≠ weight (image e.toImages false) e.length ∧
  image e.toImages true 0 = true ∧ e.distinguish < e.length ∧
  image e.toImages true e.distinguish ≠ image e.toImages false e.distinguish ∧
  (∀ r : Fin e.length, e.separation r.val < e.length) ∧
  (∀ r : Fin e.length, r.val ≠ 0 → ∀ b c : Bool,
    image e.toImages b (e.separation r.val) ≠
      image e.toImages c ((e.separation r.val + r.val) % e.length)) ∧
  window (word e.toImages) e.blocks 0 ∈ e.language ∧
  (∀ xs ∈ e.language, xs.length = e.blocks) ∧
  (∀ xs ∈ e.language, ∀ r : Fin e.length,
    expandWindow e.toImages e.blocks xs r.val ∈ e.language) ∧
  (∀ xs ∈ e.language, listImageWeight e.toImages xs ≤ e.cap) ∧
  (3 : Int) ^ e.cap < (2 : Int) ^ (e.length * e.blocks)

instance (e : FiniteContractionEntry) : Decidable e.Valid := by
  unfold FiniteContractionEntry.Valid
  infer_instance

theorem finite_entry_literal_images (e : FiniteContractionEntry) (hv : e.Valid) :
    List.ofFn e.toImages.one = e.one ∧ List.ofFn e.toImages.zero = e.zero := by
  rcases hv with ⟨_, _, hone, hzero, _⟩
  constructor
  · apply List.ext_get (by simp only [List.length_ofFn]; exact hone.symm)
    intro i _ hi
    simp [FiniteContractionEntry.toImages, List.getElem_ofFn, List.getElem?_eq_getElem hi]
  · apply List.ext_get (by simp only [List.length_ofFn]; exact hzero.symm)
    intro i _ hi
    simp [FiniteContractionEntry.toImages, List.getElem_ofFn, List.getElem?_eq_getElem hi]

/-- Successful finite validation constructs both independent certificates and
therefore excludes every actual rational Collatz realization. -/
theorem finite_entry_no_rational_seed (e : FiniteContractionEntry) (hv : e.Valid) (p q : Int) :
    ¬ RealizesWord p q (parityWord e.toImages) := by
  rcases hv with ⟨hL, hh, _, _, _, _, h1, hj, hdiff, hsep, hcols, hinit, _, hclosed, hw, hgap⟩
  let columns : ColumnCertificate e.toImages := {
    distinguish := ⟨e.distinguish, hj⟩
    different := hdiff
    separate := fun r => ⟨e.separation r.val, hsep r⟩
    separates := hcols }
  let windows : WindowCertificate e.toImages e.blocks := {
    language := e.language
    initial := hinit
    closed := hclosed }
  exact no_rational_seed_finite_certificates hL e.toImages h1 columns hh windows hw hgap p q

end CollatzLab.Morphism
