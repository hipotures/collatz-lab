import CollatzLab.MorphismBalance
import CollatzLab.SparseFamily
import CollatzLab.ExponentialGap

/-! Exact spectral threshold statements, with effective integer witnesses. -/
namespace CollatzLab.Morphism

/-- The Phase 10 balance identity solved for the selected power-image count.
No primitivity, positivity of D or spectral gap is required for this equality. -/
theorem power_image_count {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (k a : Nat) :
    frequencyDen M * (weight (fun j => word M (L ^ k * a + j)) (L ^ k) : Int) =
      (weight (image M false) L : Int) * (L ^ k : Nat) +
        weightDelta M ^ k * (frequencyDen M * bit (word M a) -
          (weight (image M false) L : Int)) := by
  have hh := balance_power hL M h1 k a 1
  simp only [Nat.mul_one, balance] at hh
  have hb : (weight (fun j => word M (a + j)) 1 : Int) = bit (word M a) := by
    cases hb : word M a <;> simp [weight, bit, hb]
  rw [hb] at hh
  simp only [Int.natCast_one, Int.mul_one] at hh
  omega

/-- For the fixed point beginning at 1, positive D already supplies a strict
spectral gap. Primitivity is unnecessary, but prolongability is essential. -/
theorem prolongable_spectral_gap {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M) :
    absInt (weightDelta M) < (L : Int) := by
  have h0 := weight_le (image M false) L
  have h1' := weight_le (image M true) L
  have hp := weight_positive hL M h1
  unfold frequencyDen at hD
  unfold weightDelta absInt
  split <;> omega

/-- D=0 forces both images to preserve their parent letter everywhere. -/
theorem frequencyDen_zero_images {L : Nat} (M : Images L) (hD : frequencyDen M = 0) :
    weight (image M false) L = 0 ∧ weight (image M true) L = L := by
  have hh := weight_le (image M true) L
  unfold frequencyDen at hD
  omega

/-- Summing a uniform chunk cap gives a bound at every multiple of its length. -/
theorem weight_chunks_bound (v : Nat → Bool) (k R : Nat)
    (hb : ∀ n, weight (fun j => v (k * n + j)) k ≤ R) : ∀ m,
    weight v (k * m) ≤ m * R
  | 0 => by simp [weight]
  | m + 1 => by
    rw [Nat.mul_succ, weight_segment, Nat.succ_mul]
    have hi := weight_chunks_bound v k R hb m
    have hh := hb m
    omega

/-- A shifted partition controls the original prefix, with its finite initial
weight retained explicitly rather than discarded in an average argument. -/
theorem weight_prefix_shift_bound (v : Nat → Bool) (t k R : Nat)
    (hb : ∀ n, weight (fun j => v (t + k * n + j)) k ≤ R) (m : Nat) :
    weight v (k * m) ≤ weight v t + m * R := by
  have hs := weight_chunks_bound (fun j => v (t + j)) k R
    (by intro n; simpa only [Nat.add_assoc] using hb n) m
  have hm := weight_mono v (show k * m ≤ t + k * m by omega)
  rw [weight_segment] at hm
  omega

/-- Every uniformly bounded shifted partition has cap density at least the
exact spectral frequency r0/D. This is proved with a finite amplification
witness; no real limit or unquantified average is a premise. -/
theorem uniform_chunks_frequency_necessary {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M)
    (t k R : Nat)
    (hb : ∀ n, weight (fun j => word M (t + k * n + j)) k ≤ R) :
    (weight (image M false) L : Int) * (k : Int) ≤ frequencyDen M * (R : Int) := by
  let D := frequencyDen M
  let r := (weight (image M false) L : Int)
  let B := max 1 (absInt (weightDelta M))
  let Z := D * (weight (word M) k : Int) - r * (k : Int)
  let T := D * (weight (word M) t : Int)
  let C := absInt Z + T
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBL : B < (L : Int) := by
    have := prolongable_spectral_gap hL M h1 hD
    dsimp [B]; omega
  have hT : 0 ≤ T := Int.mul_nonneg (by dsimp [D]; omega) (by omega)
  have hC : 0 ≤ C := by have := absInt_nonneg Z; dsimp [C]; omega
  let e := (B * (C + 1)).toNat + 1
  have he : B * (C + 1) ≤ (e : Int) := by
    have hp := Int.mul_nonneg (by omega : 0 ≤ B) (by omega : 0 ≤ C + 1)
    have hh := Int.toNat_of_nonneg hp
    dsimp [e]; omega
  have hamp := amplify_integer_gap (L : Int) B (C + 1) hBL hB (by omega) e (by dsimp [e]; omega) he
  let S := ((L ^ e : Nat) : Int)
  have hS : 0 < S := by
    dsimp [S]; exact Int.ofNat_lt.mpr (Nat.pow_pos (by omega))
  have hBP : 1 ≤ B ^ e := Family.pow_ge_one hB e
  have hdelta : absInt (weightDelta M ^ e) ≤ B ^ e := by
    rw [absInt_pow_eq]
    exact pow_le_pow_of_le (absInt_nonneg _) (by dsimp [B]; omega) e
  have hZ := Int.mul_le_mul_of_nonneg_right hdelta (absInt_nonneg Z)
  rw [← absInt_mul] at hZ
  have hzlo : -(B ^ e * absInt Z) ≤ weightDelta M ^ e * Z := by
    have hlo : -absInt (weightDelta M ^ e * Z) ≤ weightDelta M ^ e * Z := by
      unfold absInt; split <;> omega
    omega
  have hbal := balance_power hL M h1 e 0 k
  simp only [Nat.mul_zero, balance, Nat.zero_add] at hbal
  change D * (weight (word M) (L ^ e * k) : Int) -
    r * ((L ^ e * k : Nat) : Int) = weightDelta M ^ e * Z at hbal
  rw [Int.natCast_mul] at hbal
  have hbound := weight_prefix_shift_bound (word M) t k R hb (L ^ e)
  rw [Nat.mul_comm k (L ^ e)] at hbound
  have hbD := Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hbound) (show 0 ≤ D by dsimp [D]; omega)
  simp only [Int.natCast_add, Int.natCast_mul] at hbD
  by_cases hn : (weight (image M false) L : Int) * (k : Int) ≤ frequencyDen M * (R : Int)
  · exact hn
  apply False.elim
  have hmargin : D * (R : Int) + 1 ≤ r * (k : Int) := by dsimp [D, r]; omega
  have hmul := Int.mul_le_mul_of_nonneg_right hmargin (show 0 ≤ S by omega)
  have hTS := Int.mul_le_mul_of_nonneg_left hBP hT
  have hsmall : S ≤ C * B ^ e := by
    dsimp [S, C, T] at *
    family_ring
  have hpow : ((L : Int) ^ e) = S := by dsimp [S]; rw [Int.natCast_pow]
  rw [hpow] at hamp
  have hstrict := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ 2 by decide)
    (show 0 ≤ B ^ e by omega)
  family_ring

end CollatzLab.Morphism

namespace CollatzLab

/-- Integer comparison with a rational slope gives a contraction certificate. -/
theorem rational_ratio_contraction (s d R S : Nat) (_hd : 1 ≤ d) (hS : 1 ≤ S)
    (hgap : (3 : Int) ^ s < (2 : Int) ^ d) (hcap : d * R ≤ s * S) :
    (3 : Int) ^ R < (2 : Int) ^ S := by
  have hg := positive_pow_strict ((2 : Int) ^ d) ((3 : Int) ^ s)
    (Family.pow_ge_one (by decide) _) hgap S hS
  rw [int_pow_mul, int_pow_mul] at hg
  have hc := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) hcap)
  simp only [Int.natCast_pow] at hc
  change (3 : Int) ^ (d * R) ≤ (3 : Int) ^ (s * S) at hc
  by_cases hh : (3 : Int) ^ R < (2 : Int) ^ S
  · exact hh
  · have hm := pow_le_pow_of_le (pow_nonneg_of_nonneg (x := (2 : Int)) (by decide) S)
      (show (2 : Int) ^ S ≤ (3 : Int) ^ R by omega) d
    rw [int_pow_mul, int_pow_mul, Nat.mul_comm R d, Nat.mul_comm S d] at hm
    omega

/-- A supercritical rational lower slope cannot be a contracting cap density. -/
theorem rational_ratio_no_contraction (s d R S : Nat) (hd : 1 ≤ d) (hS : 1 ≤ S)
    (hgap : (2 : Int) ^ d < (3 : Int) ^ s) (hcap : s * S ≤ d * R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ S := by
  have hg := positive_pow_strict ((3 : Int) ^ s) ((2 : Int) ^ d)
    (Family.pow_ge_one (by decide) _) hgap S hS
  rw [int_pow_mul, int_pow_mul] at hg
  have hc := Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 3) (by decide) hcap)
  simp only [Int.natCast_pow] at hc
  change (3 : Int) ^ (s * S) ≤ (3 : Int) ^ (d * R) at hc
  intro hh
  have hm := positive_pow_strict ((2 : Int) ^ S) ((3 : Int) ^ R)
    (Family.pow_ge_one (by decide) _) hh d hd
  rw [int_pow_mul, int_pow_mul, Nat.mul_comm R d, Nat.mul_comm S d] at hm
  omega

/-- The putative critical equality is impossible for every rational frequency
with positive denominator. This is the exact integer content of log irrationality. -/
theorem rational_threshold_ne (s d : Nat) (hd : 1 ≤ d) :
    (3 : Int) ^ s ≠ (2 : Int) ^ d := by
  have ho := odd_pow (x := (3 : Int)) (by decide) s
  have he := Family.even_pow (x := (2 : Int)) (by decide) hd
  omega

end CollatzLab

namespace CollatzLab.Morphism

/-- Supercritical spectral frequency rules out every fixed-length contracting
partition, including partitions beginning after any finite shift. -/
theorem spectral_no_uniform_contraction {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (d : Nat) (hd : 1 ≤ d)
    (hD : frequencyDen M = (d : Int))
    (hgap : (2 : Int) ^ d < (3 : Int) ^ weight (image M false) L)
    (t k R : Nat) (hk : 1 ≤ k)
    (hb : ∀ n, weight (fun j => word M (t + k * n + j)) k ≤ R) :
    ¬ (3 : Int) ^ R < (2 : Int) ^ k := by
  have hn := uniform_chunks_frequency_necessary hL M h1 (by rw [hD]; omega) t k R hb
  rw [hD] at hn
  have hc : weight (image M false) L * k ≤ d * R := by
    exact Int.ofNat_le.mp (by simpa only [Int.natCast_mul] using hn)
  exact rational_ratio_no_contraction _ d R k hd hk hgap hc

/-- Uniform signed discrepancy for each power image. The larger explicit
constant D+r0 avoids assumptions about either parent letter being present. -/
theorem power_image_discrepancy_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M) (k a : Nat) :
    absInt (frequencyDen M *
      (weight (fun j => word M (L ^ k * a + j)) (L ^ k) : Int) -
      (weight (image M false) L : Int) * (L ^ k : Nat)) ≤
      absInt (weightDelta M) ^ k * (frequencyDen M + (weight (image M false) L : Int)) := by
  have hh := power_image_count hL M h1 k a
  have he : frequencyDen M *
      (weight (fun j => word M (L ^ k * a + j)) (L ^ k) : Int) -
      (weight (image M false) L : Int) * (L ^ k : Nat) =
      weightDelta M ^ k * (frequencyDen M * bit (word M a) -
        (weight (image M false) L : Int)) := by omega
  rw [he, absInt_mul, absInt_pow_eq]
  have hb : absInt (frequencyDen M * bit (word M a) -
      (weight (image M false) L : Int)) ≤ frequencyDen M + (weight (image M false) L : Int) := by
    cases ha : word M a <;> simp only [bit, ha, Bool.false_eq_true, if_false, if_true,
      Int.mul_zero, Int.mul_one]
    all_goals unfold absInt; split <;> omega
  exact Int.mul_le_mul_of_nonneg_left hb (pow_nonneg_of_nonneg (absInt_nonneg _) k)

/-- Any strict rational upper slope is attained as a uniform cap by a finite
power image. The proof constructs its level using the integer base gap L>B. -/
theorem exists_power_ratio_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M)
    (s d : Nat) (hd : 1 ≤ d)
    (hmargin : (d : Int) * (weight (image M false) L : Int) < frequencyDen M * (s : Int)) :
    ∃ k R : Nat, d * R ≤ s * L ^ k ∧
      ∀ a, weight (fun j => word M (L ^ k * a + j)) (L ^ k) ≤ R := by
  let D := frequencyDen M
  let r := (weight (image M false) L : Int)
  let B := max 1 (absInt (weightDelta M))
  let C := (d : Int) * (D + r) + D * (d : Int)
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBL : B < (L : Int) := by
    have := prolongable_spectral_gap hL M h1 hD
    dsimp [B]; omega
  have hC : 1 ≤ C := by
    have h0 := Int.mul_nonneg (show 0 ≤ (d : Int) by omega) (show 0 ≤ D + r by dsimp [D, r]; omega)
    have h1' := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ (d : Int) by omega)
      (show 0 ≤ D by dsimp [D]; omega)
    dsimp [C]; omega
  let k := (B * C).toNat + 1
  have hk : B * C ≤ (k : Int) := by
    have hp := Int.mul_nonneg (by omega : 0 ≤ B) (by omega : 0 ≤ C)
    have hh := Int.toNat_of_nonneg hp
    dsimp [k]; omega
  have hamp := amplify_integer_gap (L : Int) B C hBL hB hC k (by dsimp [k]; omega) hk
  let S := L ^ k
  let R := s * S / d
  refine ⟨k, R, ?_, ?_⟩
  · dsimp [R, S]
    have hh := Nat.mul_div_le (s * L ^ k) d
    simpa only [Nat.mul_comm d] using hh
  · intro a
    have hp := power_image_discrepancy_bound hL M h1 hD k a
    have hdelta := pow_le_pow_of_le (absInt_nonneg (weightDelta M))
      (show absInt (weightDelta M) ≤ B by dsimp [B]; omega) k
    have hc0 : 0 ≤ D + r := by dsimp [D, r]; omega
    have hp' := Int.mul_le_mul_of_nonneg_right hdelta hc0
    have habs : absInt (D * (weight (fun j => word M (S * a + j)) S : Int) - r * (S : Int)) ≤
        B ^ k * (D + r) := Int.le_trans hp hp'
    have hupper : D * (weight (fun j => word M (S * a + j)) S : Int) ≤
        r * (S : Int) + B ^ k * (D + r) := by
      have hh : D * (weight (fun j => word M (S * a + j)) S : Int) - r * (S : Int) ≤
          absInt (D * (weight (fun j => word M (S * a + j)) S : Int) - r * (S : Int)) := by
        unfold absInt; split <;> omega
      omega
    have hfloor : (s : Int) * (S : Int) - (d : Int) ≤ (d : Int) * (R : Int) := by
      have hm := Nat.mod_add_div (s * S) d
      have hr := Nat.mod_lt (s * S) (by omega : 0 < d)
      have hn : s * S ≤ d * R + d := by
        dsimp only [R]
        omega
      have hh := Int.ofNat_le.mpr hn
      simp only [Int.natCast_add, Int.natCast_mul] at hh
      omega
    have hBP := Family.pow_ge_one hB k
    have hmargin' : (d : Int) * r + 1 ≤ D * (s : Int) := by dsimp [D, r]; omega
    have hposS : 0 ≤ (S : Int) := by omega
    have hmul := Int.mul_le_mul_of_nonneg_right hmargin' hposS
    have hbdy := Int.mul_le_mul_of_nonneg_left hBP
      (show 0 ≤ D * (d : Int) from Int.mul_nonneg (by dsimp [D]; omega) (by omega))
    have hds := Int.mul_le_mul_of_nonneg_left hupper (show 0 ≤ (d : Int) by omega)
    have hf := Int.mul_le_mul_of_nonneg_left hfloor (show 0 ≤ D by dsimp [D]; omega)
    have hpow : (L : Int) ^ k = (S : Int) := by dsimp [S]; rw [Int.natCast_pow]
    rw [hpow] at hamp
    have hfinal : (d : Int) * D * (weight (fun j => word M (S * a + j)) S : Int) ≤
        (d : Int) * D * (R : Int) := by
      dsimp [C] at hamp
      family_ring
    have hdD : 0 < (d : Int) * D := Int.mul_pos (by omega) (by dsimp [D]; omega)
    exact Int.ofNat_le.mp (Int.le_of_mul_le_mul_left hfinal hdD)

/-- A rational separating slope and the spectral margin construct a finite
contracting power-block certificate; this is an existence theorem, not a cutoff. -/
theorem exists_contracting_power_of_ratio {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (hD : 0 < frequencyDen M)
    (s d : Nat) (hd : 1 ≤ d)
    (hmargin : (d : Int) * (weight (image M false) L : Int) < frequencyDen M * (s : Int))
    (hgap : (3 : Int) ^ s < (2 : Int) ^ d) :
    ∃ k R : Nat, (3 : Int) ^ R < (2 : Int) ^ (L ^ k) ∧
      ∀ a, weight (fun j => word M (L ^ k * a + j)) (L ^ k) ≤ R := by
  rcases exists_power_ratio_bound hL M h1 hD s d hd hmargin with ⟨k, R, hcap, hw⟩
  exact ⟨k, R, rational_ratio_contraction s d R (L ^ k) hd (Nat.pow_pos (by omega)) hgap hcap, hw⟩

end CollatzLab.Morphism

namespace CollatzLab

/-- A strict integer base gap has a rational separating slope with a positive
frequency margin. The explicit multiplier t=3*3^r+1 avoids real logarithms. -/
theorem rational_gap_thickening (r d : Nat) (hd : 1 ≤ d)
    (hgap : (3 : Int) ^ r < (2 : Int) ^ d) :
    ∃ s d' : Nat, 1 ≤ d' ∧ d' * r < d * s ∧ (3 : Int) ^ s < (2 : Int) ^ d' := by
  let t := 3 * 3 ^ r + 1
  have ht : (t : Int) = 3 * (3 : Int) ^ r + 1 := by
    dsimp [t]
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.natCast_one]
    rfl
  have htpos : 1 ≤ t := by dsimp [t]; omega
  refine ⟨r * t + 1, d * t, Nat.mul_pos hd htpos, ?_, ?_⟩
  · have he : d * (r * t + 1) = d * t * r + d := by
      rw [Nat.mul_add, Nat.mul_one]
      congr 1
      ac_rfl
    rw [he]
    omega
  · have ha := amplify_integer_gap ((2 : Int) ^ d) ((3 : Int) ^ r) 3 hgap
      (Family.pow_ge_one (by decide) _) (by decide) t htpos (by omega)
    have hp := pow_pos_of_pos (x := (3 : Int) ^ r) (pow_pos_of_pos (by decide) _) t
    rw [Int.pow_succ, ← int_pow_mul, ← int_pow_mul]
    omega

end CollatzLab

namespace CollatzLab.Morphism

/-- Every strictly subcritical prolongable substitution with D>0 has a finite
power-block contraction certificate. No primitivity assumption or bounded
search is used. The proof above specifies an effective (large) witness level. -/
theorem subcritical_has_contracting_power {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (d : Nat) (hd : 1 ≤ d)
    (hD : frequencyDen M = (d : Int))
    (hgap : (3 : Int) ^ weight (image M false) L < (2 : Int) ^ d) :
    ∃ k R : Nat, (3 : Int) ^ R < (2 : Int) ^ (L ^ k) ∧
      ∀ a, weight (fun j => word M (L ^ k * a + j)) (L ^ k) ≤ R := by
  rcases rational_gap_thickening (weight (image M false) L) d hd hgap with
    ⟨s, d', hd', hmargin, hg⟩
  apply exists_contracting_power_of_ratio hL M h1 (by rw [hD]; omega) s d' hd' ?_ hg
  rw [hD]
  exact Int.ofNat_lt.mpr hmargin

/-- Exact boundary of fixed-length uniform contraction for every prolongable
binary uniform substitution with D>0, including nonprimitive and constant words.
The critical equality is impossible; arbitrary finite shifts do not help. -/
theorem uniform_contraction_iff_subcritical {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (d : Nat) (hd : 1 ≤ d)
    (hD : frequencyDen M = (d : Int)) :
    (∃ t k R : Nat, 1 ≤ k ∧
      (∀ n, weight (fun j => word M (t + k * n + j)) k ≤ R) ∧
      (3 : Int) ^ R < (2 : Int) ^ k) ↔
        (3 : Int) ^ weight (image M false) L < (2 : Int) ^ d := by
  constructor
  · rintro ⟨t, k, R, hk, hb, hg⟩
    have hne := rational_threshold_ne (weight (image M false) L) d hd
    by_cases hh : (3 : Int) ^ weight (image M false) L < (2 : Int) ^ d
    · exact hh
    · have hsuper : (2 : Int) ^ d < (3 : Int) ^ weight (image M false) L := by omega
      exact False.elim (spectral_no_uniform_contraction hL M h1 d hd hD hsuper t k R hk hb hg)
  · intro hg
    rcases subcritical_has_contracting_power hL M h1 d hd hD hg with ⟨k, R, hgap, hw⟩
    exact ⟨0, L ^ k, R, Nat.pow_pos (by omega), by simpa only [Nat.zero_add] using hw, hgap⟩

end CollatzLab.Morphism

namespace CollatzLab.Morphism

theorem frequencyDen_nonnegative {L : Nat} (M : Images L) : 0 ≤ frequencyDen M := by
  have hh := weight_le (image M true) L
  unfold frequencyDen
  omega

/-- The exceptional D=0 case has the constant-one selected fixed point, so its
spectral ratio is undefined and it cannot be treated by dividing by D. -/
theorem frequencyDen_zero_word {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (hD : frequencyDen M = 0) (n : Nat) : word M n = true := by
  have hw := (frequencyDen_zero_images M hD).2
  have hfull := (weight_full_iff (image M true) L).1 hw
  have h1 := hfull 0 (by omega)
  have hh := word_unique hL M h1 (fun _ => true) rfl
    (by intro a j hj; exact (hfull j hj).symm)
  exact (congrFun hh n).symm

end CollatzLab.Morphism

namespace CollatzLab.Morphism

/-- Exact characteristic polynomial of the binary incidence matrix, independent
of any Perron theorem or analytic assumption. -/
theorem binary_incidence_characteristic (L r0 r1 x : Int) :
    (x - (L - r0)) * (x - r1) - (L - r1) * r0 =
      (x - L) * (x - (r1 - r0)) := by family_ring

end CollatzLab.Morphism
