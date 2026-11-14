import CollatzLab
open CollatzLab CollatzLab.Morphism

-- The strongest no-go has no rational-realization premise.
example (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    (2 : Int) ^ min (m + ell) (n + f) ∣ returnDet v m n :=
  returnDet_automatic v m n ell f hm hn

example (v : Nat → Bool) (m n ell f : Nat)
    (hm : ∀ j, j < ell → v (m + j) = v j)
    (hn : ∀ j, j < f → v (n + j) = v j) :
    absInt (returnDet v m n) < (2 : Int) ^ min (m + ell) (n + f) ↔
      returnDet v m n = 0 := returnDet_small_iff_zero v m n ell f hm hn

example (v : Nat → Bool) (N : Nat) :
    ∃ p q : Int, RealizesWord p q (fun j => bit (finiteWord v N j)) := finiteWord_realized N v

example (m ell : Nat) (hm : 1 ≤ m)
    (h : ∀ j, j < ell → parityWord frontierSix (m + j) = parityWord frontierSix j) :
    5 * ell + 1 ≤ 2 * m := frontierSix_return_bound m ell hm h

example : ¬ EventuallyPeriodic (parityWord frontierSix) := frontierSix_not_eventually_periodic

example : ¬ ∃ t k R : Nat, 1 ≤ k ∧
    (∀ n, weight (fun j => word frontierSix (t + k * n + j)) k ≤ R) ∧
    (3 : Int) ^ R < (2 : Int) ^ k := frontierSix_no_uniform_contraction
