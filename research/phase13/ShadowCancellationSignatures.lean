import CollatzLab.ShadowCancellation

/-! Independently stated interfaces for 3-adic non-cancellation, exact shadow minima,
plateaux, and the unconditional two-shadow lower bound dichotomy. -/
namespace CollatzLab.Phase13ShadowCancellationSignatures
open Morphism RationalHeight FrontierHeight ShadowCancellation

example (n : Nat) :
    offset (word frontierSix) (6 * (n + 1)) % 3 =
      if word frontierSix n then 2 else 1 :=
  offset_six_block_mod_three n

example (k : Nat) :
    offset (word frontierSix) (6 ^ (k + 1)) % 3 = 2 ∧
    offset (word frontierSix) (3 * 6 ^ (k + 1)) % 3 = 1 ∧
    shadowNum (k + 1) % 3 = 2 :=
  ⟨offset_period_mod_three k, offset_preperiod_mod_three k, shadowNum_mod_three k⟩

example (k : Nat) :
    IsBezout ((3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1))) (shadowNum (k + 1)) :=
  isBezout_preperiod_shadowNum k

example (k : Nat) (p q : Int) (hq : 0 < q)
    (heq : p * shadowDen (k + 1) = shadowNum (k + 1) * q) :
    (3 : Int) ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ∣ q ∧
    3 ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ≤ height p q :=
  ⟨preperiod_dvd_of_shadow_eq k heq, preperiod_le_height_of_shadow_eq k hq heq⟩

example (k : Nat) :
    (shadowNum (k + 1)).gcd (shadowDen (k + 1)) =
      (offset (word frontierSix) (6 ^ (k + 1))).gcd
        ((3 : Int) ^ weight (word frontierSix) (6 ^ (k + 1)) - (2 : Int) ^ (6 ^ (k + 1))) ∧
    ((shadowNum (k + 1)).gcd (shadowDen (k + 1)) : Int) ≤
      (3 : Int) ^ weight (word frontierSix) (6 ^ (k + 1)) - (2 : Int) ^ (6 ^ (k + 1)) :=
  ⟨shadow_gcd_eq_tail_gcd k, shadow_gcd_bound k⟩

example (k : Nat) :
    ((shadowNum k).gcd (shadowDen k)) * H (word frontierSix) (matchLength k) =
      height (shadowNum k) (shadowDen k) :=
  H_shadow_exact k

example (k : Nat) :
    3 ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ≤
      H (word frontierSix) (matchLength (k + 1)) :=
  H_shadow_lower k

example (k N : Nat) (hlo : matchLength k < N) (hhi : N ≤ matchLength (k + 1)) :
    3 ^ weight (word frontierSix) (3 * 6 ^ (k + 1)) ≤ H (word frontierSix) N ∨
      ((2 : Int) ^ matchLength k ≤
        2 * (shadowCap k : Int) * (H (word frontierSix) N : Int) ∧
       (2 : Int) ^ N ≤
        2 * (shadowCap (k + 1) : Int) * (H (word frontierSix) N : Int)) :=
  H_two_shadow_dichotomy k N hlo hhi

example (k N : Nat) (hhi : N ≤ matchLength k)
    (hsmall : 2 * height (shadowNum k) (shadowDen k) *
      height (shadowNum k) (shadowDen k) < 2 ^ N) :
    H (word frontierSix) N = H (word frontierSix) (matchLength k) :=
  H_shadow_plateau k N hhi hsmall

example : H (word frontierSix) 67 = 297087259 ∧
    (∀ N, 59 ≤ N → N ≤ 67 → H (word frontierSix) N = 297087259) ∧
    (∀ N, 67 < N → 248368026765 ≤ H (word frontierSix) N) :=
  ⟨H_sixty_seven, H_level_one_plateau, H_after_sixty_seven⟩

end CollatzLab.Phase13ShadowCancellationSignatures
