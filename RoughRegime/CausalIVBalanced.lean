module

public import RoughRegime.CausalIVConditional


@[expose] public section
/-! Balanced instrument scores derive the literal conditional Wald
numerator and first-stage moments from actual randomized potential data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.IVData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

 theorem balanced_selectors (P : ProbabilityMeasure Ω) (D : IVData d Ω)
     (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
     (j : Bool) : (P:Measure Ω)[D.selector j|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ) := by
   cases j
   · exact balanced_indicator_false (P:Measure Ω) _ D.hX.comap_le D.Z D.hZ hbalance
   · exact hbalance

 theorem selected_observed_integrable (P : ProbabilityMeasure Ω) (D : IVData d Ω)
     (Y : Ω→Applications.MAR.Outcome) (hY : Measurable Y) (j : Bool) :
     Integrable (fun ω=>D.selector j ω*(Y ω:ℝ)) (P:Measure Ω) :=
   (D.selector_integrable P j).mul_bdd (c:=1) (measurable_subtype_coe.comp hY).aestronglyMeasurable
     (Eventually.of_forall (fun ω=>by
       simpa only [Real.norm_eq_abs,abs_of_nonneg (Y ω).property.1] using (Y ω).property.2))

variable [StandardBorelSpace Ω]

 theorem balanced_outcome_score (P : ProbabilityMeasure Ω) (D : IVData d Ω)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
     (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ)) :
     (P:Measure Ω)[Applications.ConditionalWald.outcomeScore∘Prod.snd∘D.observation|
       MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)]
       fun ω=>(P:Measure Ω)[(fun ω=>(D.potentialOutcome true ω:ℝ))|MeasurableSpace.comap D.X inferInstance] ω-
         (P:Measure Ω)[(fun ω=>(D.potentialOutcome false ω:ℝ))|MeasurableSpace.comap D.X inferInstance] ω := by
   let μ := (P:Measure Ω)
   let info := MeasurableSpace.comap D.X inferInstance
   let : MeasurableSpace Ω := mΩ
   let f (j : Bool) : Ω→ℝ := fun ω=>D.selector j ω*(D.observedOutcome ω:ℝ)
   let : MeasurableSpace Ω := mΩ
   have hscore : Applications.ConditionalWald.outcomeScore∘Prod.snd∘D.observation=(2:ℝ)•(f true-f false) := by
     funext ω
     change 2*(2*(if D.Z ω then 1 else 0)-1)*(D.observedOutcome ω:ℝ)=
       2*((if D.Z ω=true then 1 else 0)*(D.observedOutcome ω:ℝ)-
         (if D.Z ω=false then 1 else 0)*(D.observedOutcome ω:ℝ))
     cases D.Z ω <;> simp only [Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,zero_mul,one_mul] <;> ring
   rw [hscore]
   have hs := condExp_smul (μ:=μ) (2:ℝ) (f true-f false) info
   have hd := condExp_sub (D.selected_observed_integrable P D.observedOutcome D.observedOutcome_measurable true)
     (D.selected_observed_integrable P D.observedOutcome D.observedOutcome_measurable false) info
   filter_upwards [hs,hd,D.selected_outcome_conditional P true hex,D.selected_outcome_conditional P false hex,
     D.balanced_selectors P hbalance true,D.balanced_selectors P hbalance false] with ω hs hd h1 h0 hb1 hb0
   dsimp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply] at hs hd
   change μ[f true|info] ω=_ at h1
   change μ[f false|info] ω=_ at h0
   rw [hs,hd,h1,h0,hb1,hb0]
   ring

 theorem balanced_treatment_score (P : ProbabilityMeasure Ω) (D : IVData d Ω)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
     (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ)) :
     (P:Measure Ω)[Applications.ConditionalWald.treatmentScore∘Prod.snd∘D.observation|
       MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)]
       fun ω=>(P:Measure Ω)[(fun ω=>(Applications.MAR.bitOutcome (D.potentialTreatment true ω):ℝ))|
         MeasurableSpace.comap D.X inferInstance] ω+
         (P:Measure Ω)[(fun ω=>(Applications.MAR.bitOutcome (D.potentialTreatment false ω):ℝ))|
           MeasurableSpace.comap D.X inferInstance] ω := by
   let μ := (P:Measure Ω)
   let info := MeasurableSpace.comap D.X inferInstance
   let : MeasurableSpace Ω := mΩ
   let y := Applications.MAR.bitOutcome∘D.observedTreatment
   let f (j : Bool) : Ω→ℝ := fun ω=>D.selector j ω*(y ω:ℝ)
   let : MeasurableSpace Ω := mΩ
   have hy : Measurable y := (measurable_of_countable Applications.MAR.bitOutcome).comp D.observedTreatment_measurable
   have hscore : Applications.ConditionalWald.treatmentScore∘Prod.snd∘D.observation=(2:ℝ)•(f true+f false) := by
     funext ω
     cases hZ : D.Z ω <;> cases hA : D.observedTreatment ω <;>
       simp [Applications.ConditionalWald.treatmentScore,Applications.ConditionalWald.treatment,Applications.ConditionalWald.bit,
         observation,selector,binaryIndicator,Function.comp_apply,f,y,hZ,hA,Applications.MAR.bitOutcome]
   rw [hscore]
   have hs := condExp_smul (μ:=μ) (2:ℝ) (f true+f false) info
   have hd := condExp_add (D.selected_observed_integrable P y hy true) (D.selected_observed_integrable P y hy false) info
   filter_upwards [hs,hd,D.selected_treatment_conditional P true hex,D.selected_treatment_conditional P false hex,
     D.balanced_selectors P hbalance true,D.balanced_selectors P hbalance false] with ω hs hd h1 h0 hb1 hb0
   dsimp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply] at hs hd
   change μ[f true|info] ω=_ at h1
   change μ[f false|info] ω=_ at h0
   rw [hs,hd,h1,h0,hb1,hb0]
   ring

end RoughRegime.Causal.IVData
