module

public import RoughRegime.TreatmentMomentPilot


@[expose] public section
/-! The source ATT/ATU identities in precisely the actual pilot coordinates. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000

theorem attReconstruct_relation (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (hP : P ∈ treatmentClass A β1 hβ1) :
    armMean A.d false P=attReconstruct (projIcc (-1) 1 (by norm_num) (att A.d P))
      ⟨Applications.momentMean (P : Measure (Model.Covariate A.d × TreatmentResponse)) (effectPilot A.d),by exact effectPilot_mean_range A.d P⟩ := by
  rw [projIcc_of_mem (by norm_num : (-1:ℝ)≤1) (conditionalEffect_range A β1 hβ1 P hP true)]
  change armMean A.d false P=(∫o,(o.2.2:ℝ) ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)))-armProbability A.d true P*att A.d P
  obtain ⟨⟨W0⟩,⟨W1⟩⟩ := hP
  have hp : armProbability A.d true P≠0 :=
    (A.hδ.trans_le (armProbability_range (parametersWithBeta A β1 hβ1) true P W1).1).ne'
  rw [att_observable_identity A P W0 W1]
  field_simp [hp]
  ring

theorem atuReconstruct_relation (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (hP : P ∈ treatmentClass A β1 hβ1) :
    armMean A.d true P=atuReconstruct (projIcc (-1) 1 (by norm_num) (atu A.d P))
      ⟨Applications.momentMean (P : Measure (Model.Covariate A.d × TreatmentResponse)) (effectPilot A.d),by exact effectPilot_mean_range A.d P⟩ := by
  rw [projIcc_of_mem (by norm_num : (-1:ℝ)≤1) (conditionalEffect_range A β1 hβ1 P hP false)]
  change armMean A.d true P=(∫o,(o.2.2:ℝ) ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)))+(1-armProbability A.d true P)*atu A.d P
  obtain ⟨⟨W0⟩,⟨W1⟩⟩ := hP
  have hp : armProbability A.d false P≠0 := (A.hδ.trans_le (armProbability_range A false P W0).1).ne'
  have hpc : 1-armProbability A.d true P≠0 := by rw [←armProbability_complement]; exact hp
  rw [atu_observable_identity A P W0 W1]
  field_simp [hpc]
  ring

end RoughRegime.Applications.MAR
