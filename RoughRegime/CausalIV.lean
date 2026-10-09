module

public import RoughRegime.CausalTreatment
public import RoughRegime.ApplicationWald


@[expose] public section
/-! Binary instrumental-variable consistency and conditional randomization.
All observed variables are actual measurable functions of potential data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev IVLatent := Bool×Bool×Applications.MAR.Outcome×Applications.MAR.Outcome

def latentTreatment (j : Bool) (z : IVLatent) : Bool := if j then z.2.1 else z.1
def latentOutcome (j : Bool) (z : IVLatent) : Applications.MAR.Outcome :=
  if latentTreatment j z then z.2.2.2 else z.2.2.1

theorem latentTreatment_measurable (j : Bool) : Measurable (latentTreatment j) := by
  cases j
  · exact measurable_fst
  · exact measurable_snd.fst

theorem latentOutcome_measurable (j : Bool) : Measurable (latentOutcome j) := by
  exact measurable_snd.snd.snd.ite
    (measurableSet_eq_fun (latentTreatment_measurable j) measurable_const) measurable_snd.snd.fst

structure IVData (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  X : Ω→Model.Covariate d
  Z : Ω→Bool
  A0 : Ω→Bool
  A1 : Ω→Bool
  Y0 : Ω→Applications.MAR.Outcome
  Y1 : Ω→Applications.MAR.Outcome
  hX : Measurable X
  hZ : Measurable Z
  hA0 : Measurable A0
  hA1 : Measurable A1
  hY0 : Measurable Y0
  hY1 : Measurable Y1

namespace IVData
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def latent (D : IVData d Ω) (ω : Ω) : IVLatent := (D.A0 ω,D.A1 ω,D.Y0 ω,D.Y1 ω)
theorem latent_measurable (D : IVData d Ω) : Measurable D.latent :=
  D.hA0.prodMk (D.hA1.prodMk (D.hY0.prodMk D.hY1))

def potentialTreatment (D : IVData d Ω) (j : Bool) : Ω→Bool := latentTreatment j∘D.latent
def potentialOutcome (D : IVData d Ω) (j : Bool) : Ω→Applications.MAR.Outcome := latentOutcome j∘D.latent

theorem potentialTreatment_measurable (D : IVData d Ω) (j : Bool) : Measurable (D.potentialTreatment j) :=
  (latentTreatment_measurable j).comp D.latent_measurable

theorem potentialOutcome_measurable (D : IVData d Ω) (j : Bool) : Measurable (D.potentialOutcome j) :=
  (latentOutcome_measurable j).comp D.latent_measurable

def observedTreatment (D : IVData d Ω) (ω : Ω) : Bool := if D.Z ω then D.A1 ω else D.A0 ω
def observedOutcome (D : IVData d Ω) (ω : Ω) : Applications.MAR.Outcome :=
  if D.observedTreatment ω then D.Y1 ω else D.Y0 ω

theorem observedTreatment_measurable (D : IVData d Ω) : Measurable D.observedTreatment :=
  D.hA1.ite (measurableSet_eq_fun D.hZ measurable_const) D.hA0

theorem observedOutcome_measurable (D : IVData d Ω) : Measurable D.observedOutcome :=
  D.hY1.ite (measurableSet_eq_fun D.observedTreatment_measurable measurable_const) D.hY0

def observation (D : IVData d Ω) (ω : Ω) : Model.Covariate d×Applications.Wald.Response :=
  (D.X ω,D.Z ω,D.observedTreatment ω,D.observedOutcome ω)

theorem observation_measurable (D : IVData d Ω) : Measurable D.observation :=
  D.hX.prodMk (D.hZ.prodMk (D.observedTreatment_measurable.prodMk D.observedOutcome_measurable))

def complierSet (D : IVData d Ω) : Set Ω := {ω | D.A0 ω=false ∧ D.A1 ω=true}
def effect (D : IVData d Ω) (ω : Ω) : ℝ := (D.Y1 ω:ℝ)-(D.Y0 ω:ℝ)

theorem complierSet_measurable (D : IVData d Ω) : MeasurableSet D.complierSet :=
  (measurableSet_eq_fun D.hA0 measurable_const).inter (measurableSet_eq_fun D.hA1 measurable_const)

theorem effect_measurable (D : IVData d Ω) : Measurable D.effect :=
  (measurable_subtype_coe.comp D.hY1).sub (measurable_subtype_coe.comp D.hY0)

theorem effect_integrable (D : IVData d Ω) (P : ProbabilityMeasure Ω) : Integrable D.effect (P:Measure Ω) := by
  apply Integrable.of_mem_Icc (-1) 1 D.effect_measurable.aemeasurable
  exact Eventually.of_forall (fun ω=>by dsimp only [effect];constructor <;> linarith [(D.Y0 ω).property.1,(D.Y0 ω).property.2,(D.Y1 ω).property.1,(D.Y1 ω).property.2])

theorem treatment_consistency (D : IVData d Ω) (j : Bool) (ω : Ω) (hZ : D.Z ω=j) :
    D.observedTreatment ω=D.potentialTreatment j ω := by
  cases j <;> simp [observedTreatment,potentialTreatment,latentTreatment,latent,hZ]

theorem outcome_consistency (D : IVData d Ω) (j : Bool) (ω : Ω) (hZ : D.Z ω=j) :
    D.observedOutcome ω=D.potentialOutcome j ω := by
  cases j <;> simp [observedOutcome,observedTreatment,potentialOutcome,latentOutcome,latentTreatment,latent,hZ]

theorem monotone_outcome_difference (D : IVData d Ω) (ω : Ω) (hmono : D.A0 ω≤D.A1 ω) :
    (D.potentialOutcome true ω:ℝ)-(D.potentialOutcome false ω:ℝ)=D.complierSet.indicator D.effect ω := by
  cases h0 : D.A0 ω <;> cases h1 : D.A1 ω
  · simp [potentialOutcome,latentOutcome,latentTreatment,latent,h0,h1,complierSet]
  · simp [potentialOutcome,latentOutcome,latentTreatment,latent,h0,h1,complierSet,effect]
  · simp only [h0,h1] at hmono
    contradiction
  · simp [potentialOutcome,latentOutcome,latentTreatment,latent,h0,h1,complierSet]

theorem monotone_treatment_difference (D : IVData d Ω) (ω : Ω) (hmono : D.A0 ω≤D.A1 ω) :
    (Applications.MAR.bitOutcome (D.potentialTreatment true ω):ℝ)-
      (Applications.MAR.bitOutcome (D.potentialTreatment false ω):ℝ)=D.complierSet.indicator (fun _=>1) ω := by
  cases h0 : D.A0 ω <;> cases h1 : D.A1 ω
  · simp [potentialTreatment,latentTreatment,latent,h0,h1,complierSet,Applications.MAR.bitOutcome]
  · simp [potentialTreatment,latentTreatment,latent,h0,h1,complierSet,Applications.MAR.bitOutcome]
  · simp only [h0,h1] at hmono
    contradiction
  · simp [potentialTreatment,latentTreatment,latent,h0,h1,complierSet,Applications.MAR.bitOutcome]

end IVData
end RoughRegime.Causal
