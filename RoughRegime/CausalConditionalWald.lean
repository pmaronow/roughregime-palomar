module

public import RoughRegime.CausalIVOneSided
public import RoughRegime.CausalHomogeneity


@[expose] public section
/-! The actual average conditional Wald target identifies the conditional
complier effect. The source mean-homogeneity assumption then gives the ATE. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.IVData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

def conditionalComplierEffect (P : ProbabilityMeasure Ω) (D : IVData d Ω) (ω : Ω) : ℝ :=
  (P:Measure Ω)[D.complierSet.indicator D.effect|MeasurableSpace.comap D.X inferInstance] ω/
    (P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|MeasurableSpace.comap D.X inferInstance] ω

theorem conditionalWald_complier_identification (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (honesided : ∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω) :
    Applications.ConditionalWald.target d (P.map D.observation)=
      ∫ ω,D.conditionalComplierEffect P ω ∂(P:Measure Ω) := by
  let μ := (P:Measure Ω)
  let m : MeasurableSpace (Model.Covariate d×Applications.ConditionalWald.Response) :=
    MeasurableSpace.comap Prod.fst inferInstance
  let : MeasurableSpace (Model.Covariate d×Applications.ConditionalWald.Response) :=
    (inferInstance:MeasurableSpace (Model.Covariate d)).prod (inferInstance:MeasurableSpace Applications.ConditionalWald.Response)
  have hV : Integrable (Applications.ConditionalWald.outcomeScore∘Prod.snd∘D.observation) μ := by
    apply Integrable.of_mem_Icc (-2) 2
      ((Applications.ConditionalWald.outcomeScore_measurable.comp measurable_snd).comp D.observation_measurable).aemeasurable
    exact Eventually.of_forall (fun ω=>by
      cases hZ : D.Z ω <;> simp [Applications.ConditionalWald.outcomeScore,Applications.ConditionalWald.instrument,
        Applications.ConditionalWald.bit,Applications.ConditionalWald.outcome,observation,Function.comp_apply,hZ] <;>
        constructor <;> linarith [(D.observedOutcome ω).property.1,(D.observedOutcome ω).property.2])
  have hD : Integrable (Applications.ConditionalWald.treatmentScore∘Prod.snd∘D.observation) μ := by
    apply Integrable.of_mem_Icc 0 2
      ((Applications.ConditionalWald.treatmentScore_measurable.comp measurable_snd).comp D.observation_measurable).aemeasurable
    exact Eventually.of_forall (fun ω=>by
      cases hA : D.observedTreatment ω <;> norm_num [Applications.ConditionalWald.treatmentScore,
        Applications.ConditionalWald.treatment,Applications.ConditionalWald.bit,observation,Function.comp_apply,hA])
  have he := conditional_ratio_map_integral μ D.observation D.observation_measurable m measurable_fst.comap_le
    (Applications.ConditionalWald.outcomeScore∘Prod.snd) (Applications.ConditionalWald.treatmentScore∘Prod.snd)
    (Applications.ConditionalWald.outcomeScore_measurable.comp measurable_snd)
    (Applications.ConditionalWald.treatmentScore_measurable.comp measurable_snd) hV hD
  change Applications.ConditionalWald.target d (P.map D.observation)=_ at he
  have hinfo : MeasurableSpace.comap D.observation m=MeasurableSpace.comap D.X inferInstance := by
    rw [MeasurableSpace.comap_comp];rfl
  rw [hinfo] at he
  exact he.trans (integral_congr_ae (by
    filter_upwards [D.oneSided_outcome_score P hex hbalance honesided,
      D.oneSided_treatment_score P hex hbalance honesided] with ω hV hD
    exact congrArg₂ (fun a b:ℝ=>a/b) hV hD))

theorem conditionalWald_ate_of_homogeneity (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (honesided : ∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω)
    (hcomplier : ∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|MeasurableSpace.comap D.X inferInstance] ω≠0)
    (hhom : (P:Measure Ω)[D.effect|MeasurableSpace.comap (fun ω=>(D.X ω,D.A1 ω)) inferInstance]=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[D.effect|MeasurableSpace.comap D.X inferInstance]) :
    Applications.ConditionalWald.target d (P.map D.observation)=∫ ω,D.effect ω ∂(P:Measure Ω) := by
  let μ := (P:Measure Ω)
  let m1 := MeasurableSpace.comap D.X inferInstance
  let : MeasurableSpace Ω := mΩ
  let m2 := MeasurableSpace.comap (fun ω=>(D.X ω,D.A1 ω)) inferInstance
  let : MeasurableSpace Ω := mΩ
  let g : Ω→ℝ := binaryIndicator true∘D.A1
  have hm12 : m1 ≤ m2 := MeasurableSpace.comap_le_comap_of_eq_comp Prod.fst measurable_fst rfl
  have hm2 : m2 ≤ mΩ := (D.hX.prodMk D.hA1).comap_le
  have hg : StronglyMeasurable[m2] g := by
    exact ((binaryIndicator_measurable true).comp
      (measurable_snd.comp (comap_measurable (fun ω=>(D.X ω,D.A1 ω))))).stronglyMeasurable
  have hgb : ∀ᵐ ω ∂μ,‖g ω‖≤(1:ℝ) := Eventually.of_forall (fun ω=>by
    cases hA : D.A1 ω <;> norm_num [g,binaryIndicator,hA])
  have hfac := selected_effect_of_mean_homogeneity μ m1 m2 hm12 hm2 g D.effect hg 1 hgb
    (D.effect_integrable P) hhom
  have h0 := D.no_always_takers P hex hbalance honesided
  have hcg : D.complierSet.indicator (fun _=>(1:ℝ))=ᵐ[μ] g := by
    filter_upwards [h0] with ω hω
    cases hA : D.A1 ω <;> simp [complierSet,g,binaryIndicator,hω,hA]
  have hce : D.complierSet.indicator D.effect=ᵐ[μ] fun ω=>g ω*D.effect ω := by
    filter_upwards [h0] with ω hω
    cases hA : D.A1 ω <;> simp [complierSet,g,binaryIndicator,hω,hA]
  have htarget := D.conditionalWald_complier_identification P hex hbalance honesided
  rw [htarget,← integral_condExp D.hX.comap_le (f:=D.effect)]
  apply integral_congr_ae
  filter_upwards [condExp_congr_ae hcg (m:=m1),condExp_congr_ae hce (m:=m1),hfac,hcomplier] with ω hq hy hfac hqpos
  change μ[D.complierSet.indicator D.effect|m1] ω /
    μ[D.complierSet.indicator (fun _=>(1:ℝ))|m1] ω=μ[D.effect|m1] ω
  rw [hy,hfac,← hq]
  exact mul_div_cancel_left₀ _ hqpos

end RoughRegime.Causal.IVData
