import CollatzLab.FiniteCatalogueThree
import CollatzLab.FiniteCatalogueFour
import CollatzLab.FiniteCatalogueFive
import CollatzLab.FiniteCatalogueSix
import CollatzLab.SignedContraction

/-! A bounded catalogue of 222 distinct kernel-checked unequal-weight exclusions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace CollatzLab.Morphism

def contractionCatalogue : List FiniteContractionEntry :=
  catalogueThree ++ catalogueFour ++ catalogueFive ++ catalogueSix

theorem contractionCatalogue_length : contractionCatalogue.length = 222 := by decide

theorem contractionCatalogue_distinct :
    (contractionCatalogue.map (fun e => (e.length, e.one, e.zero))).Nodup := by decide

theorem contractionCatalogue_valid (e : FiniteContractionEntry) (he : e ∈ contractionCatalogue) :
    e.Valid := by
  simp only [contractionCatalogue, List.mem_append] at he
  rcases he with ((h | h) | h) | h
  · exact catalogueThree_valid e h
  · exact catalogueFour_valid e h
  · exact catalogueFive_valid e h
  · exact catalogueSix_valid e h

theorem contractionCatalogue_bounds (e : FiniteContractionEntry) (he : e ∈ contractionCatalogue) :
    3 ≤ e.length ∧ e.length ≤ 6 ∧ e.blocks ≤ 8 := by
  simp only [contractionCatalogue, List.mem_append] at he
  rcases he with ((h | h) | h) | h
  · have := catalogueThree_bounds e h; omega
  · have := catalogueFour_bounds e h; omega
  · have := catalogueFive_bounds e h; omega
  · have := catalogueSix_bounds e h; omega

theorem no_rational_seed_contractionCatalogue (e : FiniteContractionEntry)
    (he : e ∈ contractionCatalogue) (p q : Int) :
    ¬ RealizesWord p q (parityWord e.toImages) :=
  finite_entry_no_rational_seed e (contractionCatalogue_valid e he) p q

theorem no_rational_seed_shifted_contractionCatalogue (e : FiniteContractionEntry)
    (he : e ∈ contractionCatalogue) (t : Nat) (p q : Int) :
    ¬ RealizesWord p q (shiftWord (parityWord e.toImages) t) :=
  no_rational_seed_shifts_of_exclusion _ (parity_binary _)
    (no_rational_seed_contractionCatalogue e he) t p q

theorem no_eventually_shifted_contractionCatalogue (e : FiniteContractionEntry)
    (he : e ∈ contractionCatalogue) (s t : Nat) (p q : Int) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = parityWord e.toImages (t + j)) :=
  no_eventually_shifted_itinerary_odd_denominator _ (parity_binary _)
    (no_rational_seed_contractionCatalogue e he) s t p q ho

end CollatzLab.Morphism
