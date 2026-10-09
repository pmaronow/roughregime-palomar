module

public import RoughRegime.SoftDigits
public import RoughRegime.DyadicTensor


@[expose] public section
/-! The source's exponential digit-mismatch integral under the actual
Lebesgue law on the unit cube, including all coordinates and levels. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open RoughRegime.DyadicDigits

 def softDigitPenalty (U : SmoothStep) (J d : ℕ) (γ Ω : Fin d → Fin J → ℝ)
    (t : Fin d → Fin J → Bool) (x : Fin d → ℝ) : ℝ :=
  ∏ q, ∏ i, Real.exp (-Ω q i * |softDigit U (γ q i) ((2 : ℝ) ^ (J - i.val) * x q) -
    if t q i then 1 else 0|)

 theorem softDigitPenalty_nonneg (U : SmoothStep) (J d : ℕ) (γ Ω : Fin d → Fin J → ℝ)
    (t : Fin d → Fin J → Bool) (x : Fin d → ℝ) :
    0 ≤ softDigitPenalty U J d γ Ω t x := by
  unfold softDigitPenalty
  positivity

 theorem softDigitPenalty_le_one (U : SmoothStep) (J d : ℕ) (γ Ω : Fin d → Fin J → ℝ)
    (t : Fin d → Fin J → Bool) (hΩ : ∀ q i, 0 ≤ Ω q i) (x : Fin d → ℝ) :
    softDigitPenalty U J d γ Ω t x ≤ 1 := by
  unfold softDigitPenalty
  apply Finset.prod_le_one₀
  · intro q hq
    positivity
  · intro q hq
    apply Finset.prod_le_one₀
    · intro i hi
      positivity
    · intro i hi
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hΩ q i)) (abs_nonneg _)

 theorem softDigitPenalty_continuous (U : SmoothStep) (J d : ℕ) (γ Ω : Fin d → Fin J → ℝ)
    (t : Fin d → Fin J → Bool) (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4) :
    Continuous (softDigitPenalty U J d γ Ω t) := by
  unfold softDigitPenalty
  apply continuous_finsetProd
  intro q hq
  apply continuous_finsetProd
  intro i hi
  exact Real.continuous_exp.comp (continuous_const.mul
    ((((softDigit_smooth U (γ q i) (hγ q i) (hγ1 q i)).continuous.comp
      (continuous_const.mul (continuous_apply q))).sub continuous_const).abs))

 private theorem unitUniform_mem_Ico : ∀ᵐ y ∂unitUniform, y ∈ Ico (0 : ℝ) 1 := by
  have heq : unitUniform = volume.restrict (Ico (0 : ℝ) 1) := by
    exact (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  rw [heq]
  exact ae_restrict_mem measurableSet_Ico

 theorem cubeUniform_mem_Ico (d : ℕ) :
    ∀ᵐ x ∂cubeUniform d, ∀ q, x q ∈ Ico (0 : ℝ) 1 := by
  apply eventually_all.mpr
  intro q
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin d => unitUniform) (i := q)).eventually
    unitUniform_mem_Ico

 private theorem softDigit_penalty_bound (U : SmoothStep) (J : ℕ) (i : Fin J)
    (γ Ω y : ℝ) (t : Bool) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hΩ : 0 ≤ Ω)
    (hy : y ∈ Ico (0 : ℝ) 1) :
    Real.exp (-Ω * |softDigit U γ ((2 : ℝ) ^ (J - i.val) * y) - if t then 1 else 0|) ≤
      if pointBits J y i = t then 1 else Real.exp (-Ω / 2) := by
  by_cases heq : pointBits J y i = t
  · rw [ite_eq_left heq]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΩ) (abs_nonneg _)
  · rw [ite_eq_right heq]
    have hc : (1 / 2 : ℝ) ≤ |softDigit U γ ((2 : ℝ) ^ (J - i.val) * y) - if t then 1 else 0| := by
      have hh := pointBits_eq_digit J y hy i
      rw [hh] at heq
      cases t with
      | false =>
        have hd : digit (J - i.val) y = 1 := by simpa using heq
        have hwrong : (0 : ℤ) ≠ Int.floor ((2 : ℝ) ^ (J - i.val) * y) % 2 := by
          change _ ≠ digit (J - i.val) y
          omega
        simpa only [Bool.false_eq_true, ↓reduceIte, Int.cast_zero] using
          softDigit_wrong_cost U γ _ 0 hγ hγ1 (Or.inl rfl) hwrong
      | true =>
        have hd : digit (J - i.val) y ≠ 1 := by simpa using heq
        have hwrong : (1 : ℤ) ≠ Int.floor ((2 : ℝ) ^ (J - i.val) * y) % 2 := by
          exact Ne.symm hd
        simpa only [↓reduceIte, Int.cast_one] using
          softDigit_wrong_cost U γ _ 1 hγ hγ1 (Or.inr rfl) hwrong
    apply Real.exp_le_exp.mpr
    nlinarith

/-- Each full string costs exactly one factor (1+exp(-Omega/2))/2 per
digit when averaged over the actual cube. -/
 theorem integral_softDigitPenalty_le (U : SmoothStep) (J d : ℕ)
    (γ Ω : Fin d → Fin J → ℝ) (t : Fin d → Fin J → Bool)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4) (hΩ : ∀ q i, 0 ≤ Ω q i) :
    (∫ x, softDigitPenalty U J d γ Ω t x ∂cubeUniform d) ≤
      (((2 : ℝ) ^ (-(J : ℤ))) ^ d) *
        (∏ q, ∏ i, (1 + Real.exp (-Ω q i / 2))) := by
  let f : Fin d → Fin J → Bool → ℝ := fun q i b =>
    if b = t q i then 1 else Real.exp (-Ω q i / 2)
  have hf0 (q : Fin d) (i : Fin J) (b : Bool) : 0 ≤ f q i b := by
    unfold f
    split_ifs <;> positivity
  have hf1 (q : Fin d) (i : Fin J) (b : Bool) : f q i b ≤ 1 := by
    unfold f
    split_ifs
    · exact le_rfl
    · exact Real.exp_le_one_iff.mpr (by linarith [hΩ q i])
  have hsoft : Integrable (softDigitPenalty U J d γ Ω t) (cubeUniform d) := by
    apply Integrable.of_bound (softDigitPenalty_continuous U J d γ Ω t hγ hγ1).aestronglyMeasurable 1
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg
      (softDigitPenalty_nonneg U J d γ Ω t x)]; exact softDigitPenalty_le_one U J d γ Ω t hΩ x)
  have hhard : Integrable (fun x => ∏ q, ∏ i, f q i (cubeBits J d x q i)) (cubeUniform d) := by
    have hm : Measurable (fun b : Fin d → Fin J → Bool => ∏ q, ∏ i, f q i (b q i)) :=
      measurable_of_countable _
    apply Integrable.of_bound (hm.comp (cubeBits_measurable J d)).aestronglyMeasurable 1
    apply ae_of_all
    intro x
    change ‖∏ q, ∏ i, f q i (cubeBits J d x q i)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun q _ =>
      Finset.prod_nonneg (fun i _ => hf0 q i _)))]
    exact Finset.prod_le_one₀ (fun q _ => Finset.prod_nonneg (fun i _ => hf0 q i _))
      (fun q _ => Finset.prod_le_one₀ (fun i _ => hf0 q i _) (fun i _ => hf1 q i _))
  have hmono : (∫ x, softDigitPenalty U J d γ Ω t x ∂cubeUniform d) ≤
      ∫ x, (∏ q, ∏ i, f q i (cubeBits J d x q i)) ∂cubeUniform d := by
    apply integral_mono_ae hsoft hhard
    filter_upwards [cubeUniform_mem_Ico d] with x hx
    unfold softDigitPenalty
    apply Finset.prod_le_prod₀
    · intro q hq
      positivity
    · intro q hq
      apply Finset.prod_le_prod₀
      · intro i hi
        positivity
      · intro i hi
        exact softDigit_penalty_bound U J i (γ q i) (Ω q i) (x q) (t q i)
          (hγ q i) (hγ1 q i) (hΩ q i) (hx q)
  rw [integral_cube_digit_product_real] at hmono
  have hsum (q : Fin d) (i : Fin J) : f q i true + f q i false = 1 + Real.exp (-Ω q i / 2) := by
    cases ht : t q i <;> simp [f, ht, add_comm]
  simpa only [hsum] using hmono

 theorem integral_softDigitPenalty_exp_bound (U : SmoothStep) (J d : ℕ)
    (γ Ω : Fin d → Fin J → ℝ) (t : Fin d → Fin J → Bool)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4) (hΩ : ∀ q i, 0 ≤ Ω q i) :
    (∫ x, softDigitPenalty U J d γ Ω t x ∂cubeUniform d) ≤
      (((2 : ℝ) ^ (-(J : ℤ))) ^ d) *
        Real.exp (∑ q, ∑ i, Real.exp (-Ω q i / 2)) := by
  apply (integral_softDigitPenalty_le U J d γ Ω t hγ hγ1 hΩ).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro q hq
    positivity
  · intro q hq
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      linarith [Real.add_one_le_exp (Real.exp (-Ω q i / 2))]

/-- The exact logarithmic penalty weights chosen in the paper. -/
 def mismatchWeight (d b : ℕ) : ℝ := 2 * Real.log (d : ℝ) + 4 * Real.log ((b : ℝ) + 2)

 theorem mismatchWeight_nonneg (d b : ℕ) (hd : 0 < d) : 0 ≤ mismatchWeight d b := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd := Real.log_nonneg hd1
  have hlogb := Real.log_nonneg (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ))] : (1 : ℝ) ≤ (b : ℝ) + 2)
  unfold mismatchWeight
  linarith

 theorem exp_neg_mismatchWeight_half (d b : ℕ) (hd : 0 < d) :
    Real.exp (-mismatchWeight d b / 2) = (d : ℝ)⁻¹ * (((b : ℝ) + 2) ^ 2)⁻¹ := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have hb0 : 0 < (b : ℝ) + 2 := by positivity
  unfold mismatchWeight
  have heq : -(2 * Real.log (d : ℝ) + 4 * Real.log ((b : ℝ) + 2)) / 2 =
      -(Real.log (d : ℝ) + (Real.log ((b : ℝ) + 2) + Real.log ((b : ℝ) + 2))) := by ring
  rw [heq, Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_log hd0, Real.exp_log hb0]
  simp only [pow_two, mul_inv_rev]
  ring

 theorem sum_reciprocal_squares_le_one (J : ℕ) :
    (∑ i ∈ Finset.range J, (((i : ℝ) + 2) ^ 2)⁻¹) ≤ 1 - ((J : ℝ) + 1)⁻¹ := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have ht : (((J : ℝ) + 2) ^ 2)⁻¹ ≤ ((J : ℝ) + 1)⁻¹ - ((J : ℝ) + 2)⁻¹ := by
      have h1 : 0 < (J : ℝ) + 1 := by positivity
      have h2 : 0 < (J : ℝ) + 2 := by positivity
      field_simp
      nlinarith
    push_cast
    have heq : (J : ℝ) + 1 + 1 = (J : ℝ) + 2 := by ring
    rw [heq]
    linarith

 theorem sum_mismatch_exp_le_one (J d : ℕ) (hd : 0 < d) :
    (∑ _q : Fin d, ∑ i : Fin J, Real.exp (-mismatchWeight d i.val / 2)) ≤ 1 := by
  simp_rw [exp_neg_mismatchWeight_half d _ hd]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
  change (∑ i : Fin J, (((i.val : ℝ) + 2) ^ 2)⁻¹) ≤ 1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (((i : ℝ) + 2) ^ 2)⁻¹) J]
  exact (sum_reciprocal_squares_le_one J).trans (by linarith [inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (J : ℝ) + 1)])

/-- The concrete source weights yield the exact cell-count saving exp(1)/R,
where R=2^(dJ). -/
 theorem integral_softDigitPenalty_source_bound (U : SmoothStep) (J d : ℕ)
    (γ : Fin d → Fin J → ℝ) (t : Fin d → Fin J → Bool) (hd : 0 < d)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4) :
    (∫ x, softDigitPenalty U J d γ (fun _ i => mismatchWeight d i.val) t x ∂cubeUniform d) ≤
      (((2 : ℝ) ^ (-(J : ℤ))) ^ d) * Real.exp 1 := by
  apply (integral_softDigitPenalty_exp_bound U J d γ (fun _ i => mismatchWeight d i.val) t
    hγ hγ1 (fun _ i => mismatchWeight_nonneg d i.val hd)).trans
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sum_mismatch_exp_le_one J d hd)) (by positivity)

end RoughRegime.LatticePriors
