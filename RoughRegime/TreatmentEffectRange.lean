module

public import RoughRegime.ApplicationTreatmentUpper


@[expose] public section
/-! Actual ATT and ATU ranges derived from bounded outcomes and overlap. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000

theorem regression_measurable (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) : Measurable (regression d j P) := by
  unfold regression
  exact (stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable.div
    (stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable

theorem conditionalEffect_range (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (hP : P ∈ treatmentClass A β1 hβ1) (j : Bool) : conditionalEffect A.d j P ∈ Icc (-1) 1 := by
  obtain ⟨⟨W0⟩,⟨W1⟩⟩ := hP
  let μ := (P : Measure (Model.Covariate A.d × TreatmentResponse))
  have h0 : ∀ᵐ o ∂μ,regression A.d false P o ∈ Icc 0 1 := by
    filter_upwards [W0.regression_eq A false P,W0.regression_range A false P] with o he hr
    exact he.symm ▸ hr
  have h1 : ∀ᵐ o ∂μ,regression A.d true P o ∈ Icc 0 1 := by
    filter_upwards [W1.regression_eq (parametersWithBeta A β1 hβ1) true P,
      W1.regression_range (parametersWithBeta A β1 hβ1) true P] with o he hr
    exact he.symm ▸ hr
  let f := fun o : Model.Covariate A.d × TreatmentResponse =>
    armIndicator j o.2*(regression A.d true P o-regression A.d false P o)
  have hf : Measurable f := ((armIndicator_measurable j).comp measurable_snd).mul
    ((regression_measurable A.d true P).sub (regression_measurable A.d false P))
  have hbounds : ∀ᵐ o ∂μ,-armIndicator j o.2≤f o ∧ f o≤armIndicator j o.2 := by
    filter_upwards [h0,h1] with o h0 h1
    have hi := armIndicator_range j o.2
    constructor
    · dsimp only [f]
      nlinarith [mul_nonneg hi.1 h0.1,mul_nonneg hi.1 h1.1,
        mul_nonneg hi.1 (sub_nonneg.mpr h0.2)]
    · dsimp only [f]
      nlinarith [mul_nonneg hi.1 h0.1,mul_nonneg hi.1 h1.1,
        mul_nonneg hi.1 (sub_nonneg.mpr h1.2)]
  have hfi : Integrable f μ := Integrable.of_mem_Icc (-1) 1 hf.aemeasurable (by
    filter_upwards [hbounds] with o ho
    have hi := armIndicator_range j o.2
    exact ⟨by linarith [ho.1,hi.2],ho.2.trans hi.2⟩)
  have hi : Integrable (fun o=>armIndicator j o.2) μ := Integrable.of_mem_Icc 0 1
    ((armIndicator_measurable j).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o=>armIndicator_range j o.2))
  have hlo := integral_mono_ae hi.neg hfi (hbounds.mono (fun _ h=>h.1))
  have hhi := integral_mono_ae hfi hi (hbounds.mono (fun _ h=>h.2))
  have hp : 0<armProbability A.d j P := by
    cases j
    · exact A.hδ.trans_le (armProbability_range A false P W0).1
    · exact A.hδ.trans_le (armProbability_range (parametersWithBeta A β1 hβ1) true P W1).1
  change (∫ o,f o ∂μ)/armProbability A.d j P ∈ Icc (-1) 1
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa only [Pi.neg_apply,integral_neg,armProbability,μ,neg_mul,one_mul] using hlo
  · apply (div_le_iff₀ hp).mpr
    simpa only [armProbability,μ,one_mul] using hhi

end RoughRegime.Applications.MAR
