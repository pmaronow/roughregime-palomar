module

public import RoughRegime.ApplicationTrialBrackets
public import RoughRegime.ProductVarianceUpper


@[expose] public section
/-! Literal variance of the trial CATE, identified with the actual explained
variance in the bounded-response experiment by the two explicit kernels. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.Trial

theorem cateVariance_eq (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Response)) (hP : P ∈ modelClass A) :
    cateVariance A P = Products.explainedTarget A (forwardLaw A P) := by
  obtain ⟨W⟩ := hP
  unfold cateVariance Products.explainedTarget
  rw [variance_congr (W.cate_ae A P),variance_congr (W.forward_conditional A P)]
  symm
  exact variance_map (W.measurableF.comp measurable_fst).aemeasurable
    (forward_measurable A.d).aemeasurable

theorem cateVariance_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hd : A.δ ≤ 1) (hab : A.α = A.β) :
    Model.UpperBracket (cateVariance A) (modelClass A) A.bracketParameters (A.nu : ℝ) := by
  obtain ⟨hν,C,hC,n0,hn0,hupper⟩ := Products.explained_upperBracket A hM hd
  apply Model.upperBracket_congr_target _ (fun P => Products.explainedTarget A (forwardLaw A P))
    _ _ _ (cateVariance_eq A)
  refine ⟨hν,C,hC,n0,hn0,?_⟩
  intro n hn
  rw [(transformed_risks_eq A hab n (Products.explainedTarget A) 0).2]
  exact hupper n hn

end RoughRegime.Applications.Trial
