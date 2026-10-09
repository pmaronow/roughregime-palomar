module

public import RoughRegime.Conditional


@[expose] public section
/-! Conditional covariance, conditional variance and explained variance in
Example 2. These statements use actual conditional expectations and mathlib's
conditional variance. The loss statements cover all square-integrable
predictors measurable with respect to the covariate information. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.ConditionalExamples

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

def conditionalCovariance (m : MeasurableSpace Ω) (U V : Ω → ℝ)
    (μ : @Measure Ω mΩ) : Ω → ℝ :=
  μ[(U - μ[U | m]) * (V - μ[V | m]) | m]

theorem mean_conditional_covariance (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    [SigmaFinite (μ.trim hm)] (U V : Ω → ℝ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    (∫ x, conditionalCovariance m U V μ x ∂μ) =
      (∫ x, U x * V x ∂μ) - ∫ x, (μ[U | m]) x * (μ[V | m]) x ∂μ := by
  have hUm : MemLp (μ[U | m]) 2 μ := hU.condExp one_le_two
  have hVm : MemLp (μ[V | m]) 2 μ := hV.condExp one_le_two
  have huv : Integrable (fun x ↦ U x * V x) μ := memLp_one_iff_integrable.mp (hU.mul hV)
  have humv : Integrable (fun x ↦ U x * (μ[V | m]) x) μ :=
    memLp_one_iff_integrable.mp (hU.mul hVm)
  have hvmU : Integrable (fun x ↦ V x * (μ[U | m]) x) μ :=
    memLp_one_iff_integrable.mp (hV.mul hUm)
  have hmm : Integrable (fun x ↦ (μ[U | m]) x * (μ[V | m]) x) μ :=
    memLp_one_iff_integrable.mp (hUm.mul hVm)
  have hmuV : Integrable (fun x ↦ (μ[U | m]) x * V x) μ := by
    simpa only [mul_comm] using hvmU
  have hiU := RoughRegime.Conditional.integral_mul_condExp hm U (μ[V | m])
    (hU.integrable one_le_two) stronglyMeasurable_condExp humv
  have hiV : (∫ x, (μ[U | m]) x * V x ∂μ) =
      ∫ x, (μ[U | m]) x * (μ[V | m]) x ∂μ := by
    have h := RoughRegime.Conditional.integral_mul_condExp hm V (μ[U | m])
      (hV.integrable one_le_two) stronglyMeasurable_condExp hvmU
    simpa only [mul_comm] using h
  unfold conditionalCovariance
  rw [integral_condExp hm]
  have he : (U - μ[U | m]) * (V - μ[V | m]) =
      (fun x ↦ (U x * V x - U x * (μ[V | m]) x - (μ[U | m]) x * V x) +
        (μ[U | m]) x * (μ[V | m]) x) := by
    funext x
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  rw [he, integral_add (f := fun x ↦ U x * V x - U x * (μ[V | m]) x -
      (μ[U | m]) x * V x) (g := fun x ↦ (μ[U | m]) x * (μ[V | m]) x)
      ((huv.sub humv).sub hmuV) hmm,
    integral_sub (f := fun x ↦ U x * V x - U x * (μ[V | m]) x)
      (g := fun x ↦ (μ[U | m]) x * V x) (huv.sub humv) hmuV,
    integral_sub huv humv, hiU, hiV]
  ring

theorem mean_conditional_variance (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    [SigmaFinite (μ.trim hm)] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    (∫ x, condVar m Y μ x ∂μ) =
      (∫ x, Y x ^ 2 ∂μ) - ∫ x, (μ[Y | m]) x ^ 2 ∂μ := by
  have hce : Integrable (fun x ↦ (μ[Y | m]) x ^ 2) μ :=
    (hY.condExp one_le_two).integrable_sq
  calc
    _ = ∫ x, (μ[Y ^ 2 | m]) x - (μ[Y | m]) x ^ 2 ∂μ :=
      integral_congr_ae (condVar_ae_eq_condExp_sq_sub_sq_condExp hm hY)
    _ = _ := by
      rw [integral_sub integrable_condExp hce, integral_condExp hm]
      rfl

theorem explained_variance (hm : m ≤ mΩ) [IsProbabilityMeasure μ]
    [SigmaFinite (μ.trim hm)] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    variance (μ[Y | m]) μ = (∫ x, (μ[Y | m]) x ^ 2 ∂μ) - (∫ x, Y x ∂μ) ^ 2 := by
  rw [variance_eq_sub (hY.condExp one_le_two), integral_condExp hm]
  rfl

theorem conditional_variance_is_optimal_prediction_loss (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    (Y f : Ω → ℝ) (hY : MemLp Y 2 μ) (hf : MemLp f 2 μ)
    (hfmeas : StronglyMeasurable[m] f) :
    (∫ x, condVar m Y μ x ∂μ) ≤ ∫ x, (Y x - f x) ^ 2 ∂μ := by
  unfold condVar
  rw [integral_condExp hm]
  have hmY : MemLp (μ[Y | m]) 2 μ := hY.condExp one_le_two
  exact RoughRegime.Conditional.conditional_mean_minimizes_loss hm Y f (μ[Y | m])
    (hY.integrable one_le_two) hfmeas stronglyMeasurable_condExp Filter.EventuallyEq.rfl
    hY.integrable_sq (memLp_one_iff_integrable.mp (hY.mul hf))
    (memLp_one_iff_integrable.mp (hY.mul hmY)) hf.integrable_sq hmY.integrable_sq
    (memLp_one_iff_integrable.mp (hmY.mul hf))

end RoughRegime.ConditionalExamples
