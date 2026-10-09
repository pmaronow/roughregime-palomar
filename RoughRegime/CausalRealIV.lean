module

public import RoughRegime.CausalPotentialRange
public import RoughRegime.CausalConditionalWaldWitness
public import RoughRegime.CausalWaldWeights


@[expose] public section
/-! Real potential outcomes for IV identification. Only the actual observed
outcome is bounded; no restriction is imposed on never-observed potentials. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev RealIVLatent := Bool×Bool×ℝ×ℝ

structure RealIVData (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  X : Ω→Model.Covariate d
  Z : Ω→Bool
  A0 : Ω→Bool
  A1 : Ω→Bool
  Y0 : Ω→ℝ
  Y1 : Ω→ℝ
  Y : Ω→Applications.MAR.Outcome
  hX : Measurable X
  hZ : Measurable Z
  hA0 : Measurable A0
  hA1 : Measurable A1
  hY0 : Measurable Y0
  hY1 : Measurable Y1
  hY : Measurable Y

namespace RealIVData
variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

def latent (D : RealIVData d Ω) (ω : Ω) : RealIVLatent := (D.A0 ω,D.A1 ω,D.Y0 ω,D.Y1 ω)
theorem latent_measurable (D : RealIVData d Ω) : Measurable D.latent :=
  D.hA0.prodMk (D.hA1.prodMk (D.hY0.prodMk D.hY1))

def treatment (D : RealIVData d Ω) (ω : Ω) : Bool := if D.Z ω then D.A1 ω else D.A0 ω

def potentialOutcome (D : RealIVData d Ω) (j : Bool) (ω : Ω) : ℝ :=
  if (if j then D.A1 ω else D.A0 ω) then D.Y1 ω else D.Y0 ω

theorem potentialOutcome_measurable (D : RealIVData d Ω) (j : Bool) : Measurable (D.potentialOutcome j) := by
  cases j
  · exact D.hY1.ite (measurableSet_eq_fun D.hA0 measurable_const) D.hY0
  · exact D.hY1.ite (measurableSet_eq_fun D.hA1 measurable_const) D.hY0

def observation (D : RealIVData d Ω) (ω : Ω) : Model.Covariate d×Applications.Wald.Response :=
  (D.X ω,D.Z ω,D.treatment ω,D.Y ω)

theorem treatment_measurable (D : RealIVData d Ω) : Measurable D.treatment :=
  D.hA1.ite (measurableSet_eq_fun D.hZ measurable_const) D.hA0

theorem observation_measurable (D : RealIVData d Ω) : Measurable D.observation :=
  D.hX.prodMk (D.hZ.prodMk (D.treatment_measurable.prodMk D.hY))

def complierSet (D : RealIVData d Ω) : Set Ω := {ω|D.A0 ω=false∧D.A1 ω=true}
def effect (D : RealIVData d Ω) (ω : Ω) : ℝ := D.Y1 ω-D.Y0 ω

theorem effect_measurable (D : RealIVData d Ω) : Measurable D.effect := D.hY1.sub D.hY0
theorem complierSet_measurable (D : RealIVData d Ω) : MeasurableSet D.complierSet :=
  (measurableSet_eq_fun D.hA0 measurable_const).inter (measurableSet_eq_fun D.hA1 measurable_const)

def bounded (D : RealIVData d Ω) : IVData d Ω where
  X := D.X
  Z := D.Z
  A0 := D.A0
  A1 := D.A1
  Y0 := clipOutcome∘D.Y0
  Y1 := clipOutcome∘D.Y1
  hX := D.hX
  hZ := D.hZ
  hA0 := D.hA0
  hA1 := D.hA1
  hY0 := clipOutcome_measurable.comp D.hY0
  hY1 := clipOutcome_measurable.comp D.hY1

 theorem bounded_observation_ae (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω) :
    D.bounded.observation=ᵐ[(P:Measure Ω)] D.observation := by
  filter_upwards [hc] with ω hω
  have hy : D.bounded.observedOutcome ω=D.Y ω := by
    rw [←clipOutcome_subtype (D.Y ω),hω]
    change (if D.treatment ω then clipOutcome (D.Y1 ω) else clipOutcome (D.Y0 ω))=
      clipOutcome (if D.treatment ω then D.Y1 ω else D.Y0 ω)
    cases D.treatment ω <;> rfl
  exact congrArg (fun y:Applications.MAR.Outcome=>(D.X ω,D.Z ω,D.treatment ω,y)) hy

 theorem bounded_law_eq (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω) :
    P.map D.bounded.observation=P.map D.observation := by
  apply Subtype.ext
  exact Measure.map_congr (D.bounded_observation_ae P hc)

variable [StandardBorelSpace Ω]

 theorem bounded_exchangeable (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω)) :
    CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.bounded.latent (P:Measure Ω) :=
  hex.comp measurable_id (measurable_fst.prodMk (measurable_snd.fst.prodMk
    ((clipOutcome_measurable.comp measurable_snd.snd.fst).prodMk
      (clipOutcome_measurable.comp measurable_snd.snd.snd))))

 theorem potential_outcome_range (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘D.Z|
      MeasurableSpace.comap D.X inferInstance] ω≠0) (j : Bool) :
    ∀ᵐ ω ∂(P:Measure Ω),D.potentialOutcome j ω∈Icc (0:ℝ) 1 := by
  have hj : Measurable (fun z:RealIVLatent=>if (if j then z.2.1 else z.1) then z.2.2.2 else z.2.2.1) := by
    cases j
    · exact measurable_snd.snd.snd.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_snd.snd.fst
    · exact measurable_snd.snd.snd.ite (measurableSet_eq_fun measurable_snd.fst measurable_const) measurable_snd.snd.fst
  apply selected_potential_range (P:Measure Ω) _ D.hX.comap_le D.Z (fun ω=>(D.Y ω:ℝ))
    (D.potentialOutcome j) j D.hZ (D.potentialOutcome_measurable j)
    (Eventually.of_forall (fun ω=>(D.Y ω).property))
  · filter_upwards [hc] with ω hω
    intro hZ
    simpa only [potentialOutcome,treatment,hZ] using hω
  · exact hex.comp measurable_id hj
  · exact hpositive j

 theorem complier_potential_ranges (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘D.Z|
      MeasurableSpace.comap D.X inferInstance] ω≠0) :
    ∀ᵐ ω ∂(P:Measure Ω),ω∈D.complierSet→D.Y0 ω∈Icc (0:ℝ) 1∧D.Y1 ω∈Icc (0:ℝ) 1 := by
  filter_upwards [D.potential_outcome_range P hc hex hpositive false,
    D.potential_outcome_range P hc hex hpositive true] with ω h0 h1
  intro hC
  exact ⟨by simpa [potentialOutcome,hC.1] using h0,by simpa [potentialOutcome,hC.2] using h1⟩

 theorem complier_effect_eq_bounded (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘D.Z|
      MeasurableSpace.comap D.X inferInstance] ω≠0) :
    D.complierSet.indicator D.effect=ᵐ[(P:Measure Ω)] D.bounded.complierSet.indicator D.bounded.effect := by
  filter_upwards [D.complier_potential_ranges P hc hex hpositive] with ω hω
  change D.complierSet.indicator D.effect ω=D.complierSet.indicator D.bounded.effect ω
  by_cases hC:ω∈D.complierSet
  · have hY := hω hC
    rw [Set.indicator_of_mem hC,Set.indicator_of_mem hC]
    change D.Y1 ω-D.Y0 ω=(clipOutcome (D.Y1 ω):ℝ)-(clipOutcome (D.Y0 ω):ℝ)
    rw [clipOutcome_coe_eq _ hY.2,clipOutcome_coe_eq _ hY.1]
  · simp [hC]

 theorem wald_identification (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : RealIVData A.d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘D.Z|
      MeasurableSpace.comap D.X inferInstance] ω≠0)
    (hmono : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω)
    (hC : (P:Measure Ω) D.complierSet≠0) :
    Applications.Wald.target A (P.map D.observation)=∫ ω,D.effect ω ∂(cond (P:Measure Ω) D.complierSet) := by
  have h := D.bounded.wald_identification A P (D.bounded_exchangeable P hex) hpositive hmono hC
  rw [D.bounded_law_eq P hc] at h
  have he := D.complier_effect_eq_bounded P hc hex hpositive
  have hmem : ∀ᵐ ω ∂cond (P:Measure Ω) D.complierSet,ω∈D.complierSet := by
    exact ae_cond_mem D.complierSet_measurable
  apply h.trans
  apply integral_congr_ae
  filter_upwards [he.filter_mono cond_absolutelyContinuous.ae_le,hmem] with ω hω hC
  simpa only [show D.bounded.complierSet=D.complierSet from rfl,Set.indicator_of_mem hC] using hω.symm

end RealIVData
end RoughRegime.Causal
