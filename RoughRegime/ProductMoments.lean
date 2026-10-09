module

public import RoughRegime.ProductBrackets
public import RoughRegime.ObservableMeanUpper


@[expose] public section
/-! Actual conditional and unconditional moments of bounded real responses. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.Products

abbrev responseMean (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  ∫ o, (o.2 : ℝ) ∂(P : Measure (Model.Observation A BoundedResponse))

abbrev responseSecondMoment (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  ∫ o, (o.2 : ℝ)^2 ∂(P : Measure (Model.Observation A BoundedResponse))

def responseVariance (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  variance (fun o => (o.2 : ℝ)) (P : Measure (Model.Observation A BoundedResponse))

def explainedTarget (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  variance ((P : Measure (Model.Observation A BoundedResponse))[
    ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd) | Model.covariateInformation A BoundedResponse])
    (P : Measure (Model.Observation A BoundedResponse))

theorem bounded_conditional_mean (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) :
    ∀ᵐ o ∂(P : Measure (Model.Observation A BoundedResponse)),
      ((P : Measure (Model.Observation A BoundedResponse))[
        ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd) |
          Model.covariateInformation A BoundedResponse]) o ∈ Icc (-1) 1 := by
  have hi : Integrable ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd)
      (P : Measure (Model.Observation A BoundedResponse)) :=
    Integrable.of_mem_Icc (-1) 1 (measurable_subtype_coe.comp measurable_snd).aemeasurable
      (Filter.Eventually.of_forall (fun o => o.2.property))
  have hlo := condExp_mono (m := Model.covariateInformation A BoundedResponse)
    (integrable_const (-1 : ℝ)) hi (Filter.Eventually.of_forall (fun o => o.2.property.1))
  have hhi := condExp_mono (m := Model.covariateInformation A BoundedResponse)
    hi (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall (fun o => o.2.property.2))
  rw [condExp_const measurable_fst.comap_le] at hlo hhi
  filter_upwards [hlo,hhi] with o hlo hhi
  exact ⟨hlo,hhi⟩

theorem quadraticTarget_range (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : quadraticTarget A P ∈ Icc 0 1 := by
  have hY := Applications.bounded_memLp (P : Measure (Model.Observation A BoundedResponse))
    ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd) (measurable_subtype_coe.comp measurable_snd)
    1 (fun o => response_bound o.2)
  have hi := (hY.condExp (m := Model.covariateInformation A BoundedResponse) one_le_two).integrable_sq
  have hs : ∀ᵐ o ∂(P : Measure (Model.Observation A BoundedResponse)),
      ((P : Measure (Model.Observation A BoundedResponse))[
        ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd) |
          Model.covariateInformation A BoundedResponse]) o ^ 2 ≤ 1 := by
    filter_upwards [bounded_conditional_mean A P] with o ho
    nlinarith only [ho.1,ho.2]
  refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
  have h := integral_mono_ae hi (integrable_const (1 : ℝ)) hs
  simpa only [quadraticTarget, integral_const,probReal_univ,one_smul,pow_two] using h

theorem responseMean_range (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : responseMean A P ∈ Icc (-1) 1 := by
  have hi : Integrable (fun o : Model.Observation A BoundedResponse => (o.2 : ℝ))
      (P : Measure (Model.Observation A BoundedResponse)) :=
    Integrable.of_mem_Icc (-1) 1 (measurable_subtype_coe.comp measurable_snd).aemeasurable
      (Filter.Eventually.of_forall (fun o => o.2.property))
  constructor
  · have h := integral_mono_ae (integrable_const (-1 : ℝ)) hi
      (Filter.Eventually.of_forall (fun o => o.2.property.1))
    simpa only [integral_const,probReal_univ,one_smul] using h
  · have h := integral_mono_ae hi (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall (fun o => o.2.property.2))
    simpa only [integral_const,probReal_univ,one_smul] using h

theorem responseVariance_identity (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) :
    responseVariance A P = responseSecondMoment A P - (responseMean A P)^2 := by
  exact variance_eq_sub (Applications.bounded_memLp
    (P : Measure (Model.Observation A BoundedResponse)) (fun o => (o.2 : ℝ))
    (measurable_subtype_coe.comp measurable_snd) 1 (fun o => response_bound o.2))

theorem responseVariance_range (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : responseVariance A P ∈ Icc 0 1 := by
  have h := variance_le_sq_of_bounded (μ := (P : Measure (Model.Observation A BoundedResponse)))
    (a := (-1 : ℝ)) (b := 1) (Filter.Eventually.of_forall (fun o => o.2.property))
    (measurable_subtype_coe.comp measurable_snd).aemeasurable
  refine ⟨variance_nonneg _ _,?_⟩
  norm_num at h
  exact h

theorem explainedTarget_identity (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) :
    explainedTarget A P = quadraticTarget A P - (responseMean A P)^2 :=
  ConditionalExamples.explained_variance measurable_fst.comap_le _
    (Applications.bounded_memLp (P : Measure (Model.Observation A BoundedResponse))
      ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd) (measurable_subtype_coe.comp measurable_snd)
      1 (fun o => response_bound o.2))

theorem explainedTarget_range (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : explainedTarget A P ∈ Icc 0 1 := by
  refine ⟨variance_nonneg _ _,?_⟩
  rw [explainedTarget_identity]
  linarith [(quadraticTarget_range A P).2,sq_nonneg (responseMean A P)]

theorem square_lipschitz_on_unit (a b : ℝ) (ha : a ∈ Icc (-1) 1) (hb : b ∈ Icc (-1) 1) :
    |a^2-b^2| ≤ 2*|a-b| := by
  have hab : |a+b| ≤ 2 := abs_le.mpr ⟨by linarith [ha.1,hb.1],by linarith [ha.2,hb.2]⟩
  calc
    _ = |(a-b)*(a+b)| := by congr 1; ring
    _ = |a-b| *|a+b| := abs_mul _ _
    _ ≤ |a-b| *2 := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    _ = _ := by ring

end RoughRegime.Applications.Products
