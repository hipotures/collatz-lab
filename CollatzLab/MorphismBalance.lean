import CollatzLab.MorphismContraction

/-! Exact incidence-eigenvalue identities and finite power-block certificates. -/
namespace CollatzLab.Morphism

def weightDelta {L : Nat} (M : Images L) : Int :=
  (weight (image M true) L : Int) - (weight (image M false) L : Int)

def frequencyDen {L : Nat} (M : Images L) : Int :=
  (L : Int) - (weight (image M true) L : Int) + (weight (image M false) L : Int)

def balance {L : Nat} (M : Images L) (a h : Nat) : Int :=
  frequencyDen M * (weight (fun j => word M (a + j)) h : Int) -
    (weight (image M false) L : Int) * (h : Int)

/-- The selected image-weight sum is an exact affine function of the source
one-count, including a negative weight difference. -/
theorem imageWeightSum_affine {L : Nat} (M : Images L) (a : Nat) : ∀ h,
    (imageWeightSum M a h : Int) = (weight (image M false) L : Int) * (h : Int) +
      weightDelta M * (weight (fun j => word M (a + j)) h : Int)
  | 0 => by simp [imageWeightSum, weight]
  | h + 1 => by
    rw [imageWeightSum, weight]
    simp only [Int.natCast_add, Int.natCast_one, imageWeightSum_affine M a h]
    cases hb : word M (a + h) <;> simp only [hb, Bool.false_eq_true, if_false,
      if_true, Int.natCast_zero, Int.natCast_one]
    all_goals unfold weightDelta; family_ring

/-- The non-Perron incidence eigenvalue multiplies the exact integer balance
under substitution of an arbitrary aligned source window. -/
theorem balance_step {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (a h : Nat) :
    balance M (L * a) (L * h) = weightDelta M * balance M a h := by
  unfold balance
  rw [weight_source_blocks hL M h1, imageWeightSum_affine, Int.natCast_mul]
  unfold frequencyDen weightDelta
  family_ring

/-- Exact finite spectral identity at every substitution level. No limiting
frequency, primitivity, recurrence, or analytic convergence is assumed. -/
theorem balance_power {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) : ∀ k a h,
    balance M (L ^ k * a) (L ^ k * h) = weightDelta M ^ k * balance M a h
  | 0, a, h => by simp [Int.pow_zero]
  | k + 1, a, h => by
    have ha : L ^ (k + 1) * a = L * (L ^ k * a) := by
      simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hh : L ^ (k + 1) * h = L * (L ^ k * h) := by
      simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [ha, hh, balance_step hL M h1, balance_power hL M h1 k a h, Int.pow_succ]
    ac_rfl

/-- Two exact integer comparisons certify all aligned power-block one-counts.
The sign of the second eigenvalue and every parent symbol are covered. -/
theorem spectral_weight_bound {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (k R : Nat) (hD : 0 < frequencyDen M)
    (hzero : (weight (image M false) L : Int) * (L ^ k : Nat) +
      weightDelta M ^ k * (-(weight (image M false) L : Int)) ≤ frequencyDen M * (R : Int))
    (hone : (weight (image M false) L : Int) * (L ^ k : Nat) +
      weightDelta M ^ k * (frequencyDen M - (weight (image M false) L : Int)) ≤
        frequencyDen M * (R : Int)) (a : Nat) :
    weight (fun j => word M (L ^ k * a + j)) (L ^ k) ≤ R := by
  have hh := balance_power hL M h1 k a 1
  simp only [Nat.mul_one] at hh
  have hbase : balance M a 1 = if word M a then
      frequencyDen M - (weight (image M false) L : Int) else
      -(weight (image M false) L : Int) := by
    unfold balance
    cases hb : word M a <;> simp [weight, hb]
  rw [hbase] at hh
  unfold balance at hh
  have hmul : frequencyDen M * (weight (fun j => word M (L ^ k * a + j)) (L ^ k) : Int) ≤
      frequencyDen M * (R : Int) := by
    cases hb : word M a <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at hh
    all_goals omega
  exact Int.ofNat_le.mp (Int.le_of_mul_le_mul_left hmul (by omega))

theorem no_rational_seed_spectral_certificate {L : Nat} (hL : 2 ≤ L) (M : Images L)
    (h1 : image M true 0 = true) (k R : Nat) (hD : 0 < frequencyDen M)
    (hzero : (weight (image M false) L : Int) * (L ^ k : Nat) +
      weightDelta M ^ k * (-(weight (image M false) L : Int)) ≤ frequencyDen M * (R : Int))
    (hone : (weight (image M false) L : Int) * (L ^ k : Nat) +
      weightDelta M ^ k * (frequencyDen M - (weight (image M false) L : Int)) ≤
        frequencyDen M * (R : Int))
    (hgap : (3 : Int) ^ R < (2 : Int) ^ (L ^ k))
    (haper : ¬ EventuallyPeriodic (parityWord M)) (p q : Int) :
    ¬ RealizesWord p q (parityWord M) :=
  no_rational_seed_uniform_block_contraction (word M) (L ^ k) R
    (Nat.pow_pos (by omega)) (spectral_weight_bound hL M h1 k R hD hzero hone) hgap haper p q

/-- Aligned block bounds also control every unaligned finite window, with an
explicit boundary term. This is a uniform statement over both start and length. -/
theorem weight_window_from_aligned (v : Nat → Bool) (S T : Nat) (hS : 1 ≤ S)
    (hb : ∀ n, weight (fun j => v (S * n + j)) S ≤ T) (a h : Nat) :
    weight (fun j => v (a + j)) h ≤ (h / S + 2) * T := by
  have hblocks : ∀ m n, weight (fun j => v (S * n + j)) (S * m) ≤ m * T := by
    intro m
    induction m with
    | zero => intro n; simp [weight]
    | succ m ih =>
      intro n
      rw [Nat.mul_succ, weight_segment]
      have he : (fun j => v (S * n + (S * m + j))) =
          (fun j => v (S * (n + m) + j)) := by
        funext j; congr 1; rw [Nat.mul_add]; omega
      rw [he, Nat.succ_mul]
      have := ih n
      have := hb (n + m)
      omega
  let b := S * (a / S)
  let r := a % S
  have ha : b + r = a := by dsimp [b, r]; have := Nat.mod_add_div a S; omega
  have hr : r < S := Nat.mod_lt a (by omega)
  have hh : h % S < S := Nat.mod_lt h (by omega)
  have hd := Nat.mod_add_div h S
  have hcover : r + h ≤ S * (h / S + 2) := by rw [Nat.mul_add, Nat.mul_comm S 2]; omega
  have hle := weight_mono (fun j => v (b + j)) hcover
  have hseg := weight_segment (fun j => v (b + j)) r h
  have he : (fun j => v (b + (r + j))) = (fun j => v (a + j)) := by
    funext j; congr 1; omega
  rw [he] at hseg
  have hbound := hblocks (h / S + 2) (a / S)
  dsimp [b] at hle hseg
  omega

end CollatzLab.Morphism
