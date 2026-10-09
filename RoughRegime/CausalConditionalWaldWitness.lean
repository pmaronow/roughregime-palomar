module

public import RoughRegime.CausalConditionalComplier


@[expose] public section
/-! The source conditional-Wald class supplies instrument balance, one-sided
uptake and strictly positive first stage. Its literal regression b is the
actual covariate-conditional complier effect. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.IVData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

 theorem witness_pullback (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
    (W : Applications.ConditionalWald.Witness A (P.map D.observation)) :
    ((P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ)) ∧
    (∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω) ∧
    ((P:Measure Ω)[Applications.ConditionalWald.treatmentScore∘Prod.snd∘D.observation|
      MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] W.q∘D.X) ∧
    ((P:Measure Ω)[Applications.ConditionalWald.outcomeScore∘Prod.snd∘D.observation|
      MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun ω=>W.q (D.X ω)*W.b (D.X ω)) ∧
    (∀ᵐ ω ∂(P:Measure Ω),A.δ≤W.q (D.X ω)) := by
  let μ := (P:Measure Ω)
  let T := D.observation
  let m := Model.covariateInformation A Applications.ConditionalWald.Response
  let : MeasurableSpace (Model.Covariate A.d×Applications.ConditionalWald.Response) :=
    (inferInstance:MeasurableSpace (Model.Covariate A.d)).prod
      (inferInstance:MeasurableSpace Applications.ConditionalWald.Response)
  have hm : m ≤ (inferInstance:MeasurableSpace (Model.Covariate A.d×Applications.ConditionalWald.Response)) := measurable_fst.comap_le
  have hinfo : MeasurableSpace.comap T m=MeasurableSpace.comap D.X inferInstance := by
    rw [MeasurableSpace.comap_comp];rfl
  have hi : Integrable (Applications.ConditionalWald.instrument∘Prod.snd∘T) μ := by
    apply Integrable.of_mem_Icc 0 1
      ((Applications.ConditionalWald.instrument_measurable.comp measurable_snd).comp D.observation_measurable).aemeasurable
    exact Eventually.of_forall (fun ω=>Applications.ConditionalWald.bit_range (D.Z ω))
  have hD : Integrable (Applications.ConditionalWald.treatmentScore∘Prod.snd∘T) μ := by
    apply Integrable.of_mem_Icc 0 2
      ((Applications.ConditionalWald.treatmentScore_measurable.comp measurable_snd).comp D.observation_measurable).aemeasurable
    exact Eventually.of_forall (fun ω=>by
      cases hA : D.observedTreatment ω <;> norm_num [Applications.ConditionalWald.treatmentScore,
        Applications.ConditionalWald.treatment,Applications.ConditionalWald.bit,T,observation,Function.comp_apply,hA])
  have hV : Integrable (Applications.ConditionalWald.outcomeScore∘Prod.snd∘T) μ := by
    apply Integrable.of_mem_Icc (-2) 2
      ((Applications.ConditionalWald.outcomeScore_measurable.comp measurable_snd).comp D.observation_measurable).aemeasurable
    exact Eventually.of_forall (fun ω=>by
      cases hZ : D.Z ω <;> simp [Applications.ConditionalWald.outcomeScore,Applications.ConditionalWald.instrument,
        Applications.ConditionalWald.bit,Applications.ConditionalWald.outcome,observation,Function.comp_apply,hZ] <;>
        constructor <;> linarith [(D.observedOutcome ω).property.1,(D.observedOutcome ω).property.2])
  have hCEi := condExp_map_pullback μ T D.observation_measurable m hm
    (Applications.ConditionalWald.instrument∘Prod.snd)
    (Applications.ConditionalWald.instrument_measurable.comp measurable_snd) hi
  have hCED := condExp_map_pullback μ T D.observation_measurable m hm
    (Applications.ConditionalWald.treatmentScore∘Prod.snd)
    (Applications.ConditionalWald.treatmentScore_measurable.comp measurable_snd) hD
  have hCEV := condExp_map_pullback μ T D.observation_measurable m hm
    (Applications.ConditionalWald.outcomeScore∘Prod.snd)
    (Applications.ConditionalWald.outcomeScore_measurable.comp measurable_snd) hV
  rw [hinfo] at hCEi hCED hCEV
  have hWi : (fun ω=>((μ.map T)[Applications.ConditionalWald.instrument∘Prod.snd|m]) (T ω))=ᵐ[μ]
      fun _=>(1/2:ℝ) := ae_of_ae_map D.observation_measurable.aemeasurable W.instrumentHalf
  have hWD : (fun ω=>((μ.map T)[Applications.ConditionalWald.treatmentScore∘Prod.snd|m]) (T ω))=ᵐ[μ]
      W.q∘D.X := ae_of_ae_map D.observation_measurable.aemeasurable W.momentD
  have hWV : (fun ω=>((μ.map T)[Applications.ConditionalWald.outcomeScore∘Prod.snd|m]) (T ω))=ᵐ[μ]
      fun ω=>W.q (D.X ω)*W.b (D.X ω) := ae_of_ae_map D.observation_measurable.aemeasurable W.momentV
  have hsideObs : ∀ᵐ ω ∂μ,Applications.ConditionalWald.treatment (T ω).2≤
      Applications.ConditionalWald.instrument (T ω).2 :=
    ae_of_ae_map D.observation_measurable.aemeasurable W.oneSided
  have hside : ∀ᵐ ω ∂μ,D.observedTreatment ω≤D.Z ω := by
    filter_upwards [hsideObs] with ω hω
    change (if D.observedTreatment ω then 1 else 0:ℝ)≤(if D.Z ω then 1 else 0) at hω
    cases hA : D.observedTreatment ω <;> cases hZ : D.Z ω
    all_goals simp only [hA,hZ] at hω ⊢
    all_goals first | decide | norm_num at hω
  have hobs : ∀ᵐ o ∂((P.map T):Measure (Model.Covariate A.d×Applications.ConditionalWald.Response)),A.δ≤W.q o.1 := by
    apply ae_of_ae_map (f:=Prod.fst) (p:=fun x=>A.δ≤W.q x) measurable_fst.aemeasurable
    rw [W.marginal]
    exact (W.overlap.mono (fun x hx=>hx.1)).filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  have hfull : ∀ᵐ ω ∂μ,A.δ≤W.q (D.X ω) :=
    ae_of_ae_map D.observation_measurable.aemeasurable hobs
  have hselector : (Applications.ConditionalWald.instrument∘Prod.snd)∘T=D.selector true := rfl
  rw [hselector] at hCEi
  exact ⟨hCEi.symm.trans hWi,hside,hCED.symm.trans hWD,hCEV.symm.trans hWV,hfull⟩

variable [StandardBorelSpace Ω]

 theorem witness_complier_identification (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
    (W : Applications.ConditionalWald.Witness A (P.map D.observation))
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω)) :
    (∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω) ∧
    (W.b∘D.X=ᵐ[(P:Measure Ω)] (cond (P:Measure Ω) D.complierSet)[D.effect|
      MeasurableSpace.comap D.X inferInstance]) := by
  obtain ⟨hb,hs,hD,hV,hpositive⟩ := D.witness_pullback A P W
  have hscoreD := D.oneSided_treatment_score P hex hb hs
  have hscoreV := D.oneSided_outcome_score P hex hb hs
  have hq : ∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω := by
    filter_upwards [hscoreD,hD,hpositive] with ω hs hD hp
    rw [← hs,hD]
    exact A.hδ.trans_le hp
  have he : W.b∘D.X=ᵐ[(P:Measure Ω)] D.conditionalComplierEffect P := by
    filter_upwards [hscoreD,hscoreV,hD,hV,hpositive] with ω hsd hsv hd hv hp
    dsimp only [conditionalComplierEffect,Function.comp_apply]
    rw [← hsv,← hsd,hd,hv]
    exact (mul_div_cancel_left₀ _ (ne_of_gt (A.hδ.trans_le hp))).symm
  exact ⟨hq,he.trans (D.conditionalComplierEffect_eq_conditional_mean P hq)⟩

 theorem witness_ate_of_homogeneity (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
    (W : Applications.ConditionalWald.Witness A (P.map D.observation))
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hhom : (P:Measure Ω)[D.effect|MeasurableSpace.comap (fun ω=>(D.X ω,D.A1 ω)) inferInstance]=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[D.effect|MeasurableSpace.comap D.X inferInstance]) :
    Applications.ConditionalWald.target A.d (P.map D.observation)=∫ ω,D.effect ω ∂(P:Measure Ω) := by
  obtain ⟨hb,hs,_⟩ := D.witness_pullback A P W
  have hq := (D.witness_complier_identification A P W hex).1
  exact D.conditionalWald_ate_of_homogeneity P hex hb hs (hq.mono (fun _ h=>ne_of_gt h)) hhom

end RoughRegime.Causal.IVData
