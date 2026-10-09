module

public import RoughRegime.LatticePenalties


@[expose] public section
/-! Finite constants for the geometric level scales in the lattice prior.
Their existence is derived from convergent concrete series. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Filter
open scoped BigOperators

 theorem summable_shifted_polynomial_geometric (N : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun b : ℕ => ((b : ℝ) + 1) ^ N * r ^ b) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one N (r := r)
    (by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1)
  have hshift := (summable_nat_add_iff 1).mpr hs
  have hmul := hshift.mul_right r⁻¹
  convert hmul using 1
  ext b
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hr0.ne', mul_one]

 theorem mismatchWeight_linear_bound (d b : ℕ) (hd : 0 < d) :
    mismatchWeight d b ≤ (2 * Real.log (d : ℝ) + 4) * ((b : ℝ) + 1) := by
  have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hlb := Real.log_le_sub_one_of_pos (by positivity : 0 < (b : ℝ) + 2)
  unfold mismatchWeight
  nlinarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ))]

 theorem summable_weighted_band (d : ℕ) (hd : 0 < d) (C r : ℝ)
    (hC : 0 ≤ C) (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun b : ℕ => mismatchWeight d b * (C * ((b : ℝ) + 1) ^ 3 * r ^ b)) := by
  have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hs := (summable_shifted_polynomial_geometric 4 r hr0 hr1).mul_left
    ((2 * Real.log (d : ℝ) + 4) * C)
  apply Summable.of_nonneg_of_le
    (fun b => mul_nonneg (mismatchWeight_nonneg d b hd) (by positivity)) _ hs
  intro b
  have hb := mul_le_mul_of_nonneg_right (mismatchWeight_linear_bound d b hd)
    (by positivity : 0 ≤ C * ((b : ℝ) + 1) ^ 3 * r ^ b)
  convert hb using 1; ring

 def totalMismatchWeight (J d : ℕ) : ℝ :=
  ∑ _q : Fin d, ∑ i : Fin J, mismatchWeight d i.val

 theorem totalMismatchWeight_nonneg (J d : ℕ) (hd : 0 < d) : 0 ≤ totalMismatchWeight J d := by
  unfold totalMismatchWeight
  exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun i _ => mismatchWeight_nonneg d i.val hd))

 theorem totalMismatchWeight_polynomial_bound (J d : ℕ) (hd : 0 < d) :
    totalMismatchWeight J d ≤ (d : ℝ) * (2 * Real.log (d : ℝ) + 4) * ((J : ℝ) + 1) ^ 2 := by
  have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hC : 0 ≤ 2 * Real.log (d : ℝ) + 4 := by linarith
  have hsum : (∑ i : Fin J, mismatchWeight d i.val) ≤
      (J : ℝ) * ((2 * Real.log (d : ℝ) + 4) * ((J : ℝ) + 1)) := by
    calc
      _ ≤ ∑ _i : Fin J, (2 * Real.log (d : ℝ) + 4) * ((J : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply (mismatchWeight_linear_bound d i.val hd).trans
        apply mul_le_mul_of_nonneg_left _ hC
        exact_mod_cast (show i.val + 1 ≤ J + 1 by omega)
      _ = _ := by simp
  unfold totalMismatchWeight
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
  apply hb.trans
  nlinarith [mul_nonneg (Nat.cast_nonneg d) hC]

/-- The total entropy weight is bounded by a fixed multiple of any chosen
positive exponential scale. -/
 theorem totalMismatchWeight_geometric_bound (d : ℕ) (hd : 0 < d) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ J, totalMismatchWeight J d * r ^ J ≤ D := by
  let C : ℝ := (d : ℝ) * (2 * Real.log (d : ℝ) + 4)
  have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := (summable_shifted_polynomial_geometric 2 r hr0 hr1).mul_left C
  refine ⟨∑' b : ℕ, C * (((b : ℝ) + 1) ^ 2 * r ^ b), tsum_nonneg (fun b => by positivity), ?_⟩
  intro J
  apply (mul_le_mul_of_nonneg_right (totalMismatchWeight_polynomial_bound J d hd) (by positivity)).trans
  have hh := hs.le_tsum J (fun b hb => by positivity)
  convert hh using 1; dsimp [C]; ring

/-- The finite sum of weighted Fourier band widths is bounded uniformly in
 the number of levels, with a constant obtained from a genuine summable series. -/
 theorem weighted_band_sum_bound (d : ℕ) (hd : 0 < d) (C r : ℝ)
    (hC : 0 ≤ C) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ J (m : ℝ), 0 ≤ m →
      (∑ _q : Fin d, ∑ i : Fin J,
        mismatchWeight d i.val * (C * ((i.val : ℝ) + 1) ^ 3 * r ^ i.val * m)) ≤ A * m := by
  let f : ℕ → ℝ := fun b => mismatchWeight d b * (C * ((b : ℝ) + 1) ^ 3 * r ^ b)
  have hs : Summable f := summable_weighted_band d hd C r hC hr0 hr1
  have hf : ∀ b, 0 ≤ f b := fun b => mul_nonneg (mismatchWeight_nonneg d b hd) (by positivity)
  refine ⟨(d : ℝ) * ∑' b, f b, mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg hf), ?_⟩
  intro J m hm
  have hsum : (∑ i : Fin J, f i.val) ≤ ∑' b, f b := by
    rw [Fin.sum_univ_eq_sum_range f J]
    exact hs.sum_le_tsum _ (fun b hb => hf b)
  have hb := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
  have hb' := mul_le_mul_of_nonneg_right hb hm
  convert hb' using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have heq : (∑ i : Fin J, mismatchWeight d i.val * (C * ((i.val : ℝ) + 1) ^ 3 * r ^ i.val * m)) =
      (∑ i : Fin J, f i.val) * m := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f]
    ring
  rw [heq]
  ring

 def sourceGamma (gammaStar : ℝ) (b : ℕ) : ℝ := gammaStar / ((b : ℝ) + 1) ^ 2
 def sourceLambda (lambdaStar : ℝ) (b : ℕ) : ℝ := lambdaStar * ((b : ℝ) + 1)
 def sourceEta (gammaStar lambdaStar alpha0 m : ℝ) (b : ℕ) : ℝ :=
  sourceGamma gammaStar b * (2 : ℝ) ^ ((b : ℝ) * alpha0) / (sourceLambda lambdaStar b * m)

 theorem sourceEta_pos (gammaStar lambdaStar alpha0 m : ℝ) (b : ℕ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (hm : 0 < m) :
    0 < sourceEta gammaStar lambdaStar alpha0 m b := by
  unfold sourceEta sourceGamma sourceLambda
  positivity

 theorem sourceGamma_le_quarter (gammaStar : ℝ) (b : ℕ)
    (_hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4) : sourceGamma gammaStar b ≤ 1 / 4 := by
  unfold sourceGamma
  have hb1 : (1 : ℝ) ≤ (b : ℝ) + 1 := by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ))]
  have hs : (1 : ℝ) ≤ ((b : ℝ) + 1) ^ 2 := one_le_pow₀ hb1
  apply (div_le_iff₀ (by positivity : 0 < ((b : ℝ) + 1) ^ 2)).2
  nlinarith

 theorem sourceLambda_ge_one (lambdaStar : ℝ) (b : ℕ) (hlam : 1 ≤ lambdaStar) :
    1 ≤ sourceLambda lambdaStar b := by
  unfold sourceLambda
  nlinarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ))]

 theorem source_band_geometric (Q b : ℕ) (gammaStar lambdaStar alpha0 m : ℝ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (hm : 0 < m) :
    6 * (Q : ℝ) / sourceEta gammaStar lambdaStar alpha0 m b =
      (6 * Q * lambdaStar / gammaStar) * ((b : ℝ) + 1) ^ 3 * ((2 : ℝ) ^ (-alpha0)) ^ b * m := by
  have hpow : ((2 : ℝ) ^ (-alpha0)) ^ b = ((2 : ℝ) ^ ((b : ℝ) * alpha0))⁻¹ := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hpow]
  unfold sourceEta sourceGamma sourceLambda
  field_simp

/-- All source entropy and band penalties have a uniform constant C_E,
independent of J, M, or the amplitude scale m. -/
 theorem source_pattern_budget_bound (d Q : ℕ) (hd : 0 < d)
    (gammaStar lambdaStar alpha0 s0 : ℝ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (ha : 0 < alpha0) (hs0 : 0 < s0) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (J : ℕ) (m M k : ℝ),
      0 < m → m ≤ M → 0 ≤ k → k ≤ Real.sqrt M →
      m = (((2 : ℝ) ^ (-(s0 / 2))) ^ J)⁻¹ ^ 2 →
      (∑ _q : Fin d, ∑ i : Fin J, mismatchWeight d i.val *
        (k + 6 * Q / sourceEta gammaStar lambdaStar alpha0 m i.val)) ≤ CE * M := by
  let r := (2 : ℝ) ^ (-alpha0)
  let t := (2 : ℝ) ^ (-(s0 / 2))
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht1 : t < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hC : 0 ≤ 6 * (Q : ℝ) * lambdaStar / gammaStar := by positivity
  obtain ⟨A, hA, hband⟩ := weighted_band_sum_bound d hd (6 * Q * lambdaStar / gammaStar) r hC hr0 hr1
  obtain ⟨D, hD, hweight⟩ := totalMismatchWeight_geometric_bound d hd t ht0 ht1
  refine ⟨A + D, add_nonneg hA hD, ?_⟩
  intro J m M k hm hmM hk hkM hmscale
  have hM : 0 ≤ M := hm.le.trans hmM
  have htin : 0 ≤ (t ^ J)⁻¹ := by positivity
  have hsqrt : (t ^ J)⁻¹ ≤ Real.sqrt M := by
    have heq : m = (t ^ J)⁻¹ ^ 2 := hmscale
    have hh := Real.sq_sqrt hM
    nlinarith [Real.sqrt_nonneg M]
  have hw : totalMismatchWeight J d ≤ D * (t ^ J)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right (hweight J) htin
    simpa only [mul_assoc, mul_inv_cancel₀ (pow_pos ht0 J).ne', mul_one] using hh
  have hw' := hw.trans (mul_le_mul_of_nonneg_left hsqrt hD)
  have hkbound : totalMismatchWeight J d * k ≤ D * M := by
    have hh := mul_le_mul hw' hkM hk (mul_nonneg hD (Real.sqrt_nonneg M))
    simpa only [mul_assoc, Real.mul_self_sqrt hM] using hh
  have hband' := hband J m hm.le
  have hbandM := hband'.trans (mul_le_mul_of_nonneg_left hmM hA)
  simp_rw [source_band_geometric Q _ gammaStar lambdaStar alpha0 m hγ hlam hm,
    mul_add, Finset.sum_add_distrib]
  have heq : (∑ _q : Fin d, ∑ i : Fin J, mismatchWeight d i.val * k) = totalMismatchWeight J d * k := by
    unfold totalMismatchWeight
    simp_rw [Finset.sum_mul]
  rw [heq]
  change totalMismatchWeight J d * k +
    (∑ _q : Fin d, ∑ i : Fin J, mismatchWeight d i.val *
      ((6 * Q * lambdaStar / gammaStar) * ((i.val : ℝ) + 1) ^ 3 * r ^ i.val * m)) ≤ _
  nlinarith

 theorem source_m_scale_identity (J : ℕ) (s0 : ℝ) :
    (2 : ℝ) ^ ((J : ℝ) * s0) = (((2 : ℝ) ^ (-(s0 / 2))) ^ J)⁻¹ ^ 2 := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

 theorem source_pattern_budget_bound_exact (d Q : ℕ) (hd : 0 < d)
    (gammaStar lambdaStar alpha0 s0 : ℝ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (ha : 0 < alpha0) (hs0 : 0 < s0) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (J M k : ℕ),
      (2 : ℝ) ^ ((J : ℝ) * s0) ≤ M → (k : ℝ) ≤ Real.sqrt M →
      (∑ _q : Fin d, ∑ i : Fin J, mismatchWeight d i.val *
        ((k : ℝ) + 6 * Q / sourceEta gammaStar lambdaStar alpha0 ((2 : ℝ) ^ ((J : ℝ) * s0)) i.val)) ≤ CE * M := by
  obtain ⟨CE, hCE, hbound⟩ := source_pattern_budget_bound d Q hd gammaStar lambdaStar alpha0 s0 hγ hlam ha hs0
  refine ⟨CE, hCE, ?_⟩
  intro J M k hmM hkM
  exact hbound J _ M k (Real.rpow_pos_of_pos (by norm_num) _) hmM (Nat.cast_nonneg _) hkM
    (source_m_scale_identity J s0)

end RoughRegime.LatticePriors
