module

public import RoughRegime.SeparatedTreatmentMoments
public import RoughRegime.TreatmentReverseRelations


@[expose] public section
/-! The actual bounded treatment moment pilot and exact ATT/ATU reverse
identities on the literal separated class. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.SeparatedTreatment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem Witness.toMARClass (A : Model.Parameters) (S : InverseSetup A) (hδ : A.δ≤1/2)
    (β1 : ℝ) (hβ1 : 0<β1) (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (W : Witness A β1 hβ1 P) :
    P∈MAR.treatmentClass (inverseParameters A S hδ A.β A.hβ) β1 hβ1 :=
  ⟨⟨(W.controlArm A β1 hβ1 P).toMAR A S hδ A.β A.hβ false P⟩,
    ⟨(W.treatedArm A β1 hβ1 P).toMAR A S hδ β1 hβ1 true P⟩⟩

theorem conditionalEffect_range (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ≤1/2) (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (hP : P∈modelClass A β1 hβ1) (j : Bool) : MAR.conditionalEffect A.d j P∈Icc (-1) 1 := by
  obtain ⟨S⟩ := exists_inverseSetup A
  obtain ⟨W⟩ := hP
  exact MAR.conditionalEffect_range (inverseParameters A S hδ A.β A.hβ) β1 hβ1 P
    (W.toMARClass A S hδ β1 hβ1 P) j

theorem attReconstruct_relation (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ≤1/2) (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (hP : P∈modelClass A β1 hβ1) :
    MAR.armMean A.d false P=MAR.attReconstruct (projIcc (-1) 1 (by norm_num) (MAR.att A.d P))
      ⟨Applications.momentMean (P : Measure (Model.Covariate A.d×MAR.TreatmentResponse)) (MAR.effectPilot A.d),
        MAR.effectPilot_mean_range A.d P⟩ := by
  obtain ⟨S⟩ := exists_inverseSetup A
  obtain ⟨W⟩ := hP
  exact MAR.attReconstruct_relation (inverseParameters A S hδ A.β A.hβ) β1 hβ1 P
    (W.toMARClass A S hδ β1 hβ1 P)

theorem atuReconstruct_relation (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ≤1/2) (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse))
    (hP : P∈modelClass A β1 hβ1) :
    MAR.armMean A.d true P=MAR.atuReconstruct (projIcc (-1) 1 (by norm_num) (MAR.atu A.d P))
      ⟨Applications.momentMean (P : Measure (Model.Covariate A.d×MAR.TreatmentResponse)) (MAR.effectPilot A.d),
        MAR.effectPilot_mean_range A.d P⟩ := by
  obtain ⟨S⟩ := exists_inverseSetup A
  obtain ⟨W⟩ := hP
  exact MAR.atuReconstruct_relation (inverseParameters A S hδ A.β A.hβ) β1 hβ1 P
    (W.toMARClass A S hδ β1 hβ1 P)

end RoughRegime.Applications.SeparatedTreatment
