module

public import RoughRegime.CausalWald


@[expose] public section
/-! Conditional selection identities for the actual binary IV law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem binaryIndicator_complement (b : Bool) : binaryIndicator false b=1-binaryIndicator true b := by
  cases b <;> norm_num [binaryIndicator]

theorem balanced_indicator_false {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Z : Ω→Bool) (hZ : Measurable[mΩ] Z)
    (hbalance : μ[binaryIndicator true∘Z|m]=ᵐ[μ] fun _=>(1/2:ℝ)) :
    μ[binaryIndicator false∘Z|m]=ᵐ[μ] fun _=>(1/2:ℝ) := by
  let : MeasurableSpace Ω := mΩ
  have hir : Integrable (binaryIndicator true∘Z) μ := Integrable.of_mem_Icc 0 1
    ((binaryIndicator_measurable true).comp hZ).aemeasurable
    (Eventually.of_forall (fun ω=>binaryIndicator_range true (Z ω)))
  have hr : binaryIndicator false∘Z=(fun _=>(1:ℝ))-(binaryIndicator true∘Z) := by
    funext ω
    exact binaryIndicator_complement (Z ω)
  rw [hr]
  have h := condExp_sub (integrable_const (1:ℝ)) hir m
  rw [condExp_const hm] at h
  filter_upwards [h,hbalance] with ω hω hb
  simpa only [Pi.sub_apply,Pi.one_apply,hb,show (1:ℝ)-1/2=1/2 by norm_num] using hω

namespace IVData
variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

 def selector (D : IVData d Ω) (j : Bool) : Ω→ℝ := binaryIndicator j∘D.Z
 theorem selector_measurable (D : IVData d Ω) (j : Bool) : Measurable (D.selector j) :=
   (binaryIndicator_measurable j).comp D.hZ
 theorem selector_integrable (D : IVData d Ω) (P : ProbabilityMeasure Ω) (j : Bool) : Integrable (D.selector j) (P:Measure Ω) :=
   Integrable.of_mem_Icc 0 1 (D.selector_measurable j).aemeasurable
     (Eventually.of_forall (fun ω=>binaryIndicator_range j (D.Z ω)))
 theorem boundedOutcome_integrable (P : ProbabilityMeasure Ω) (Y : Ω→Applications.MAR.Outcome) (hY : Measurable Y) :
     Integrable (fun ω=>(Y ω:ℝ)) (P:Measure Ω) := Integrable.of_mem_Icc 0 1
       (measurable_subtype_coe.comp hY).aemeasurable (Eventually.of_forall (fun ω=>(Y ω).property))

variable [StandardBorelSpace Ω]

 theorem selected_outcome_conditional (P : ProbabilityMeasure Ω) (D : IVData d Ω) (j : Bool)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω)) :
     (P:Measure Ω)[(fun ω=>D.selector j ω*(D.observedOutcome ω:ℝ))|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)]
       fun ω=>(P:Measure Ω)[D.selector j|MeasurableSpace.comap D.X inferInstance] ω*
         (P:Measure Ω)[(fun ω=>(D.potentialOutcome j ω:ℝ))|MeasurableSpace.comap D.X inferInstance] ω := by
   let p : Ω→ℝ := fun ω=>(D.potentialOutcome j ω:ℝ)
   have hp : Measurable p := measurable_subtype_coe.comp (D.potentialOutcome_measurable j)
   have hirp : Integrable (fun ω=>D.selector j ω*p ω) (P:Measure Ω) :=
     (D.selector_integrable P j).mul_bdd (c:=1) hp.aestronglyMeasurable
       (Eventually.of_forall (fun ω=>by
         simpa only [p,Real.norm_eq_abs,abs_of_nonneg (D.potentialOutcome j ω).property.1] using (D.potentialOutcome j ω).property.2))
   have hc : (fun ω=>D.selector j ω*(D.observedOutcome ω:ℝ))=ᵐ[(P:Measure Ω)] fun ω=>D.selector j ω*p ω := by
     apply Eventually.of_forall
     intro ω
     by_cases h : D.Z ω=j
     · simp only [selector,Function.comp_apply,binaryIndicator,h,ite_true,one_mul,p,D.outcome_consistency j ω h]
     · simp only [selector,Function.comp_apply,binaryIndicator,h,ite_false,zero_mul]
   have hi : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le (D.selector j) p (P:Measure Ω) :=
     hex.comp (binaryIndicator_measurable j) (measurable_subtype_coe.comp (latentOutcome_measurable j))
   exact selection_conditional_product (P:Measure Ω) (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le
     (D.selector j) (fun ω=>(D.observedOutcome ω:ℝ)) p (D.selector_measurable j) hp
     (D.selector_integrable P j) (boundedOutcome_integrable P _ (D.potentialOutcome_measurable j)) hirp hc hi

 theorem selected_treatment_conditional (P : ProbabilityMeasure Ω) (D : IVData d Ω) (j : Bool)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω)) :
     (P:Measure Ω)[(fun ω=>D.selector j ω*(Applications.MAR.bitOutcome (D.observedTreatment ω):ℝ))|
       MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)]
       fun ω=>(P:Measure Ω)[D.selector j|MeasurableSpace.comap D.X inferInstance] ω*
         (P:Measure Ω)[(fun ω=>(Applications.MAR.bitOutcome (D.potentialTreatment j ω):ℝ))|
           MeasurableSpace.comap D.X inferInstance] ω := by
   let p : Ω→ℝ := fun ω=>(Applications.MAR.bitOutcome (D.potentialTreatment j ω):ℝ)
   have hp : Measurable p := measurable_subtype_coe.comp
     ((measurable_of_countable Applications.MAR.bitOutcome).comp (D.potentialTreatment_measurable j))
   have hip : Integrable p (P:Measure Ω) := boundedOutcome_integrable P _
     ((measurable_of_countable Applications.MAR.bitOutcome).comp (D.potentialTreatment_measurable j))
   have hirp : Integrable (fun ω=>D.selector j ω*p ω) (P:Measure Ω) :=
     (D.selector_integrable P j).mul_bdd (c:=1) hp.aestronglyMeasurable
       (Eventually.of_forall (fun ω=>by
         simpa only [p,Real.norm_eq_abs,abs_of_nonneg (Applications.MAR.bitOutcome (D.potentialTreatment j ω)).property.1] using
           (Applications.MAR.bitOutcome (D.potentialTreatment j ω)).property.2))
   have hc : (fun ω=>D.selector j ω*(Applications.MAR.bitOutcome (D.observedTreatment ω):ℝ))=ᵐ[(P:Measure Ω)] fun ω=>D.selector j ω*p ω := by
     apply Eventually.of_forall
     intro ω
     by_cases h : D.Z ω=j
     · simp only [selector,Function.comp_apply,binaryIndicator,h,ite_true,one_mul,p,D.treatment_consistency j ω h]
     · simp only [selector,Function.comp_apply,binaryIndicator,h,ite_false,zero_mul]
   have hi : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le (D.selector j) p (P:Measure Ω) :=
     hex.comp (binaryIndicator_measurable j) (measurable_subtype_coe.comp
       ((measurable_of_countable Applications.MAR.bitOutcome).comp (latentTreatment_measurable j)))
   exact selection_conditional_product (P:Measure Ω) (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le
     (D.selector j) (fun ω=>(Applications.MAR.bitOutcome (D.observedTreatment ω):ℝ)) p (D.selector_measurable j) hp
     (D.selector_integrable P j) hip hirp hc hi

end IVData
end RoughRegime.Causal
