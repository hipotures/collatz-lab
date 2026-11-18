import CollatzLab.PrimeObstructions

/-! Independent interface signature check for `CollatzLab.PrimeObstructions`. -/
open CollatzLab Morphism FrontierHeight ShadowCancellation PrimeObstructions

example (k : Nat) :
    7 * ((weight (word frontierSix) (6 ^ k) : Nat) : Int) =
      5 * (6 ^ k : Nat) + 2 * (-1 : Int) ^ k :=
  weight_pow_six_formula k

example (k : Nat) (hk : 2 ≤ k) :
    weight (word frontierSix) (6 ^ k) % 4 = 2 :=
  weight_pow_six_mod_four k hk

example (k : Nat) (hk : 1 ≤ k) :
    weight (word frontierSix) (6 ^ k) % 3 ≠ 0 :=
  weight_pow_six_mod_three_ne_zero k hk

example {p s k : Nat} (hp : 5 ≤ p) (hs : 2 ≤ s)
    (hs_dvd : 2 ^ s ∣ p - 1) (hk2 : 2 ≤ k) (hks : s ≤ k)
    (hF2 : ((2 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hF3 : ((3 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hdvd : (p : Int) ∣ tailDen k) :
    ((3 : Int) ^ ((p - 1) / 2 ^ (s - 1))) % (p : Int) = 1 :=
  two_primary_obstruction hp hs hs_dvd hk2 hks hF2 hF3 hdvd

example {p u k : Nat} (hp : 5 ≤ p)
    (hu_dvd : 3 ^ u ∣ p - 1) (hk1 : 1 ≤ k) (hku : u ≤ k)
    (hF2 : ((2 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hF3 : ((3 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hdvd : (p : Int) ∣ tailDen k) :
    ((3 : Int) ^ ((p - 1) / 3 ^ u)) % (p : Int) = 1 :=
  three_primary_obstruction hp hu_dvd hk1 hku hF2 hF3 hdvd

example {p k : Nat} (hp : 5 ≤ p) (hk : 1 ≤ k)
    (h4 : 4 ∣ p - 1)
    (hF2 : ((2 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hF3 : ((3 : Int) ^ (p - 1)) % (p : Int) = 1)
    (hnonres : ((3 : Int) ^ ((p - 1) / 2)) % (p : Int) = (p : Int) - 1) :
    ¬ (p ∣ Int.gcd (shadowNum k) (shadowDen k)) :=
  shadow_gcd_not_dvd_of_mod_four_nonresidue hp hk h4 hF2 hF3 hnonres

example {m : Nat} (hm : 0 < m) (f : AffMap m) (hf : f.Reduced) (j : Nat) :
    subIter (f, AffMap.id m) j = (AffMap.pow f (uSeq j), AffMap.pow f (vSeq j)) :=
  abelian_trap hm f hf j

example {m d j : Nat} (hm : 0 < m) (f : AffMap m) (hf : f.Reduced)
    (hord : AffMap.pow f d = AffMap.id m) (hdvd : d ∣ vSeq j) :
    (subIter (f, AffMap.id m) j).2 = AffMap.id m :=
  abelian_trap_id_of_dvd hm f hf hord hdvd
