module

public import RoughRegime.ConditionalExamples


@[expose] public section
/-! Extended prediction loss and the infimum over all measurable predictors.
Non-square-integrable predictors have infinite loss, so this removes the L2
restriction on the candidate predictors in the optimal-prediction assertion
of Example 2. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RoughRegime.Prediction

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

def squaredLoss (μ : Measure Ω) (Y f : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((Y x - f x) ^ 2) ∂μ

theorem eLpNorm_squared (μ : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

theorem mean_predictor_loss (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    [SigmaFinite (μ.trim hm)] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    squaredLoss μ Y (μ[Y | m]) = ENNReal.ofReal (∫ x, condVar m Y μ x ∂μ) := by
  unfold squaredLoss condVar
  rw [integral_condExp hm]
  have hsq : Integrable (fun x ↦ (Y x - (μ[Y | m]) x) ^ 2) μ :=
    (hY.sub (hY.condExp one_le_two)).integrable_sq
  exact (ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall fun x ↦ sq_nonneg _)).symm

/-- All measurable predictors are covered, including those with infinite loss. -/
theorem conditional_mean_minimizes_extended_loss (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    [SigmaFinite (μ.trim hm)] (Y f : Ω → ℝ) (hY : MemLp Y 2 μ)
    (hf : StronglyMeasurable[m] f) :
    ENNReal.ofReal (∫ x, condVar m Y μ x ∂μ) ≤ squaredLoss μ Y f := by
  by_cases hf2 : MemLp f 2 μ
  · have hsq : Integrable (fun x ↦ (Y x - f x) ^ 2) μ := (hY.sub hf2).integrable_sq
    unfold squaredLoss
    rw [← ofReal_integral_eq_lintegral_ofReal hsq
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (RoughRegime.ConditionalExamples.conditional_variance_is_optimal_prediction_loss hm Y f hY hf2 hf)
  · have herror : ¬MemLp (Y - f) 2 μ := by
      intro he
      apply hf2
      have hh := hY.sub he
      have hfun : Y - (Y - f) = f := by
        funext x
        simp
      rw [hfun] at hh
      exact hh
    have hmeas : AEStronglyMeasurable (Y - f) μ :=
      hY.aestronglyMeasurable.sub (hf.mono hm).aestronglyMeasurable
    have hnorm : eLpNorm (Y - f) 2 μ = ∞ := by
      by_contra hn
      exact herror (lt_top_iff_ne_top.mpr hn)
    have hloss : squaredLoss μ Y f = ∞ := by
      unfold squaredLoss
      have h := eLpNorm_squared μ (Y - f) hmeas
      rw [hnorm] at h
      simpa only [Pi.sub_apply, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] using h.symm
    rw [hloss]
    exact le_top

/-- The exact smallest possible prediction MSE asserted in Example 2. -/
theorem optimal_prediction_loss (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    [SigmaFinite (μ.trim hm)] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    (⨅ f : {f : Ω → ℝ // StronglyMeasurable[m] f}, squaredLoss μ Y f.1) =
      ENNReal.ofReal (∫ x, condVar m Y μ x ∂μ) := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨μ[Y | m], stronglyMeasurable_condExp⟩
      (mean_predictor_loss hm Y hY).le
  · apply le_iInf
    intro f
    exact conditional_mean_minimizes_extended_loss hm Y f.1 hY f.2

end RoughRegime.Prediction
