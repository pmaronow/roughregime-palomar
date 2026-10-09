module

public import RoughRegime.CausalIVBalanced


@[expose] public section
/-! One-sided uptake under a genuinely randomized balanced instrument implies
absence of always-takers and identifies the actual conditional Wald scores. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.IVData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem no_always_takers (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (honesided : ∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω) :
    ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω=false := by
  let μ := (P:Measure Ω)
  let info := MeasurableSpace.comap D.X inferInstance
  let : MeasurableSpace Ω := mΩ
  let f : Ω→ℝ := fun ω=>(Applications.MAR.bitOutcome (D.potentialTreatment false ω):ℝ)
  let g : Ω→ℝ := fun ω=>D.selector false ω*(Applications.MAR.bitOutcome (D.observedTreatment ω):ℝ)
  have hg : g=ᵐ[μ] 0 := by
    filter_upwards [honesided] with ω hω
    cases hZ : D.Z ω
    · have hA : D.observedTreatment ω=false := by
        cases hA : D.observedTreatment ω
        · rfl
        · simp only [hZ,hA] at hω
          contradiction
      simp [g,selector,binaryIndicator,hZ,hA,Applications.MAR.bitOutcome]
    · simp [g,selector,binaryIndicator,hZ]
  have hgc := condExp_congr_ae hg (m:=info)
  rw [condExp_zero] at hgc
  have hfc : μ[f|info]=ᵐ[μ] 0 := by
    filter_upwards [hgc,D.selected_treatment_conditional P false hex,D.balanced_selectors P hbalance false] with ω hz hsel hb
    change μ[g|info] ω=_ at hsel
    change μ[D.selector false|info] ω=(1/2:ℝ) at hb
    change μ[g|info] ω=0 at hz
    change μ[f|info] ω=0
    rw [hz,hb] at hsel
    linarith
  have hf : Integrable f μ := boundedOutcome_integrable P _
    ((measurable_of_countable Applications.MAR.bitOutcome).comp (D.potentialTreatment_measurable false))
  have hfi : ∫ ω,f ω ∂μ=0 := by
    rw [← integral_condExp D.hX.comap_le (f:=f),integral_congr_ae hfc]
    simp
  have hfzero : f=ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg
    (fun ω=>(Applications.MAR.bitOutcome (D.potentialTreatment false ω)).property.1) hf).mp hfi
  filter_upwards [hfzero] with ω hω
  change (Applications.MAR.bitOutcome (D.A0 ω):ℝ)=0 at hω
  cases hA : D.A0 ω
  · rfl
  · norm_num [hA,Applications.MAR.bitOutcome] at hω

theorem oneSided_outcome_score (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (honesided : ∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω) :
    (P:Measure Ω)[Applications.ConditionalWald.outcomeScore∘Prod.snd∘D.observation|
      MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[D.complierSet.indicator D.effect|MeasurableSpace.comap D.X inferInstance] := by
  have h0 := D.no_always_takers P hex hbalance honesided
  have hmono : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω := h0.mono (fun ω hω=>by simp [hω])
  have hd := condExp_sub (boundedOutcome_integrable P _ (D.potentialOutcome_measurable true))
    (boundedOutcome_integrable P _ (D.potentialOutcome_measurable false)) (MeasurableSpace.comap D.X inferInstance)
  have he : (fun ω=>(D.potentialOutcome true ω:ℝ)-(D.potentialOutcome false ω:ℝ))=ᵐ[(P:Measure Ω)] D.complierSet.indicator D.effect :=
    hmono.mono (fun ω hω=>D.monotone_outcome_difference ω hω)
  exact (D.balanced_outcome_score P hex hbalance).trans
    (hd.symm.trans (condExp_congr_ae he))

theorem oneSided_treatment_score (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (honesided : ∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω) :
    (P:Measure Ω)[Applications.ConditionalWald.treatmentScore∘Prod.snd∘D.observation|
      MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[D.complierSet.indicator (fun _=>1)|MeasurableSpace.comap D.X inferInstance] := by
  have h0 := D.no_always_takers P hex hbalance honesided
  have hd := condExp_add (boundedOutcome_integrable P _
    ((measurable_of_countable Applications.MAR.bitOutcome).comp (D.potentialTreatment_measurable true)))
    (boundedOutcome_integrable P _ ((measurable_of_countable Applications.MAR.bitOutcome).comp
      (D.potentialTreatment_measurable false))) (MeasurableSpace.comap D.X inferInstance)
  have he : (fun ω=>(Applications.MAR.bitOutcome (D.potentialTreatment true ω):ℝ)+
    (Applications.MAR.bitOutcome (D.potentialTreatment false ω):ℝ))=ᵐ[(P:Measure Ω)] D.complierSet.indicator (fun _=>1) := by
    filter_upwards [h0] with ω hω
    cases h1 : D.A1 ω <;> simp [potentialTreatment,latentTreatment,latent,complierSet,hω,h1,Applications.MAR.bitOutcome]
  exact (D.balanced_treatment_score P hex hbalance).trans
    (hd.symm.trans (condExp_congr_ae he))

end RoughRegime.Causal.IVData
