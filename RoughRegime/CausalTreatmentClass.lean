module

public import RoughRegime.CausalRealTreatment
public import RoughRegime.CausalWaldClass


@[expose] public section
/-! The source observed treatment class supplies the positivity used in
real-potential ATE, ATT and ATU identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem treatmentClass_selection_positive (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure Ω) (X : Ω→Model.Covariate A.d) (T : Ω→Bool)
    (Y : Ω→Applications.MAR.Outcome) (hX : Measurable X) (hT : Measurable T) (hY : Measurable Y)
    (hclass : P.map (treatmentObservation A.d X T Y)∈Applications.MAR.treatmentClass A β1 hβ1) :
    ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘T|
      MeasurableSpace.comap X inferInstance] ω≠0 := by
  intro j
  cases j
  · exact armClass_selector_positive A P false X T Y hX hT hY hclass.1
  · exact armClass_selector_positive (Applications.MAR.parametersWithBeta A β1 hβ1)
      P true X T Y hX hT hY hclass.2

variable [StandardBorelSpace Ω]

theorem real_ate_class_identification (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure Ω) (X : Ω→Model.Covariate A.d) (T : Ω→Bool)
    (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hX : Measurable X) (hT : Measurable T) (hY : Measurable Y) (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if T ω then Y1 ω else Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le T (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hclass : P.map (treatmentObservation A.d X T Y)∈Applications.MAR.treatmentClass A β1 hβ1) :
    Applications.MAR.ate A.d (P.map (treatmentObservation A.d X T Y))=
      ∫ ω,Y1 ω-Y0 ω ∂(P:Measure Ω) :=
  real_ate_potential_identification A.d P X T Y Y0 Y1 hX hT hY hY0 hY1 hc hex
    (treatmentClass_selection_positive A β1 hβ1 P X T Y hX hT hY hclass)

theorem real_conditionalEffect_class_identification (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure Ω) (j : Bool) (X : Ω→Model.Covariate A.d) (T : Ω→Bool)
    (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hX : Measurable X) (hT : Measurable T) (hY : Measurable Y) (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if T ω then Y1 ω else Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le T (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hclass : P.map (treatmentObservation A.d X T Y)∈Applications.MAR.treatmentClass A β1 hβ1) :
    Applications.MAR.conditionalEffect A.d j (P.map (treatmentObservation A.d X T Y))=
      ∫ ω,Y1 ω-Y0 ω ∂(cond (P:Measure Ω) {ω|T ω=j}) :=
  real_conditionalEffect_potential_identification A.d P j X T Y Y0 Y1 hX hT hY hY0 hY1 hc hex
    (treatmentClass_selection_positive A β1 hβ1 P X T Y hX hT hY hclass)

end RoughRegime.Causal
