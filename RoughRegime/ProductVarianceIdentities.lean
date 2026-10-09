module

public import RoughRegime.ProductVarianceUpper
public import RoughRegime.Prediction


@[expose] public section
/-! Exact population total-variance and R-squared identities for actual
bounded-response probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace RoughRegime.Applications.Products

theorem conditionalVarianceTarget_identity (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) :
    conditionalVarianceTarget A P = responseSecondMoment A P - quadraticTarget A P := by
  exact ConditionalExamples.mean_conditional_variance measurable_fst.comap_le _
    (Applications.bounded_memLp (P : Measure (Model.Observation A BoundedResponse))
      ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd)
      (measurable_subtype_coe.comp measurable_snd) 1 (fun o => response_bound o.2))

theorem responseVariance_decomposition (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) :
    responseVariance A P = conditionalVarianceTarget A P + explainedTarget A P := by
  rw [responseVariance_identity, conditionalVarianceTarget_identity, explainedTarget_identity]
  ring

theorem determination_as_residual_fraction (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse))
    (hvar : responseVariance A P ≠ 0) :
    determinationTarget A P = 1 - conditionalVarianceTarget A P / responseVariance A P := by
  unfold determinationTarget
  have he := responseVariance_decomposition A P
  field_simp
  linarith

theorem determination_quadratic_reverse (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse))
    (hvar : responseVariance A P ≠ 0) :
    quadraticTarget A P = responseVariance A P * determinationTarget A P + (responseMean A P)^2 := by
  unfold determinationTarget
  rw [mul_div_cancel₀ _ hvar, explainedTarget_identity]
  ring

end RoughRegime.Applications.Products
