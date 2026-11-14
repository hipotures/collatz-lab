import CollatzLab.Unequal100110
import CollatzLab.Unequal110100

/-! Sign normalization uses the existing rational itinerary equivalence only. -/
namespace CollatzLab

theorem seedParity_neg_both (p q : Int) (ho : q % 2 = 1) (n : Nat) :
    seedParity (-q) (-p) n = seedParity q p n := by
  have hn : (-q) % 2 = 1 := by omega
  exact (numIter_equiv (p := -p) (q := -q) (p' := p) (q' := q)
    hn ho (by family_ring) n).2

/-- Any signed odd denominator has a positive odd representation with the same
entire itinerary. No coprimality or positivity condition on the numerator. -/
theorem positive_odd_denominator_normalization (p q : Int) (ho : q % 2 = 1) :
    ∃ p' q' : Int, 0 < q' ∧ q' % 2 = 1 ∧ p * q' = p' * q ∧
      ∀ n, seedParity q' p' n = seedParity q p n := by
  by_cases hq : 0 < q
  · exact ⟨p, q, hq, ho, rfl, fun _ => rfl⟩
  · exact ⟨-p, -q, by omega, by omega, by family_ring, seedParity_neg_both p q ho⟩

theorem no_eventually_shifted_itinerary_odd_denominator (v : Nat → Int)
    (hv : ∀ n, v n = 0 ∨ v n = 1) (hex : ∀ p q, ¬ RealizesWord p q v)
    (s t : Nat) (p q : Int) (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = v (t + j)) := by
  intro ht
  rcases positive_odd_denominator_normalization p q ho with ⟨p', q', hq', ho', _, he⟩
  apply no_eventually_shifted_itinerary_of_exclusion v hv hex s t p' q' hq' ho'
  intro j
  rw [he]
  exact ht j

theorem no_eventually_shifted_unequal_100_110_signed_denominator (s t : Nat) (p q : Int)
    (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.unequal100110 (t + j)) :=
  no_eventually_shifted_itinerary_odd_denominator _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_100_110 s t p q ho

theorem no_eventually_shifted_unequal_110_100_signed_denominator (s t : Nat) (p q : Int)
    (ho : q % 2 = 1) :
    ¬ (∀ j, seedParity q p (s + j) = Morphism.parityWord Morphism.unequal110100 (t + j)) :=
  no_eventually_shifted_itinerary_odd_denominator _ (Morphism.parity_binary _)
    no_rational_seed_realizes_unequal_110_100 s t p q ho

end CollatzLab
