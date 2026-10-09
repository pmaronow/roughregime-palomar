module

public import RoughRegime.CausalMAR


@[expose] public section
/-! Actual observed arm means identify potential-outcome means under
consistency, conditional exchangeability and positivity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def treatmentObservation {Ω : Type*} (d : ℕ) (X : Ω→Model.Covariate d)
    (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (ω : Ω) :
    Model.Covariate d×Applications.MAR.TreatmentResponse := (X ω,(A ω,Y ω))

theorem treatmentObservation_measurable {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) :
    Measurable (treatmentObservation d X A Y) := hX.prodMk (hA.prodMk hY)

theorem armMean_potential_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d : ℕ) (P : ProbabilityMeasure Ω) (j : Bool)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y potential : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hp : Measurable potential)
    (hconsistency : ∀ᵐ ω ∂(P:Measure Ω),A ω=j→Y ω=potential ω)
    (hexchangeability : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A potential (P:Measure Ω))
    (hpositive : ∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[binaryIndicator j∘A|MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.armMean d j (P.map (treatmentObservation d X A Y))=
      ∫ ω,(potential ω:ℝ) ∂(P:Measure Ω) := by
  let μ := (P:Measure Ω)
  let T := treatmentObservation d X A Y
  let m : MeasurableSpace (Model.Covariate d×Applications.MAR.TreatmentResponse) :=
    MeasurableSpace.comap Prod.fst inferInstance
  let info := MeasurableSpace.comap X inferInstance
  let r := binaryIndicator j∘A
  let y : Ω→ℝ := fun ω=>(Y ω:ℝ)
  let p : Ω→ℝ := fun ω=>(potential ω:ℝ)
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace (Model.Covariate d×Applications.MAR.TreatmentResponse) :=
    (inferInstance : MeasurableSpace (Model.Covariate d)).prod (inferInstance : MeasurableSpace Applications.MAR.TreatmentResponse)
  have hT : Measurable T := treatmentObservation_measurable d X A Y hX hA hY
  have hr : Measurable r := (binaryIndicator_measurable j).comp hA
  have hy : Measurable y := measurable_subtype_coe.comp hY
  have hp' : Measurable p := measurable_subtype_coe.comp hp
  have hir : Integrable r μ := Integrable.of_mem_Icc 0 1 hr.aemeasurable
    (Eventually.of_forall (fun ω=>binaryIndicator_range j (A ω)))
  have hip : Integrable p μ := Integrable.of_mem_Icc 0 1 hp'.aemeasurable
    (Eventually.of_forall (fun ω=>(potential ω).property))
  have hiry : Integrable (fun ω=>r ω*y ω) μ :=
    hir.mul_bdd (c:=1) hy.aestronglyMeasurable (Eventually.of_forall (fun ω=>by
      simpa only [y,Real.norm_eq_abs,abs_of_nonneg (Y ω).property.1] using (Y ω).property.2))
  have hirp : Integrable (fun ω=>r ω*p ω) μ :=
    hir.mul_bdd (c:=1) hp'.aestronglyMeasurable (Eventually.of_forall (fun ω=>by
      simpa only [p,Real.norm_eq_abs,abs_of_nonneg (potential ω).property.1] using (potential ω).property.2))
  have hv : (Applications.MAR.armOutcome j∘Prod.snd)∘T=(fun ω=>r ω*y ω) := rfl
  have hd : (Applications.MAR.armIndicator j∘Prod.snd)∘T=r := rfl
  have hinfo : MeasurableSpace.comap T m=info := by rw [MeasurableSpace.comap_comp];rfl
  have hV : Integrable ((Applications.MAR.armOutcome j∘Prod.snd)∘T) μ := by rw [hv];exact hiry
  have hD : Integrable ((Applications.MAR.armIndicator j∘Prod.snd)∘T) μ := by rw [hd];exact hir
  have he := conditional_ratio_map_integral μ T hT m measurable_fst.comap_le
    (Applications.MAR.armOutcome j∘Prod.snd) (Applications.MAR.armIndicator j∘Prod.snd)
    ((Applications.MAR.armOutcome_measurable j).comp measurable_snd)
    ((Applications.MAR.armIndicator_measurable j).comp measurable_snd) hV hD
  change Applications.MAR.armMean d j (P.map T)=_ at he
  rw [hv,hd,hinfo] at he
  have hi : CondIndepFun info hX.comap_le r p μ :=
    hexchangeability.comp (binaryIndicator_measurable j) measurable_subtype_coe
  have hc : (fun ω=>r ω*y ω)=ᵐ[μ] fun ω=>r ω*p ω := by
    filter_upwards [hconsistency] with ω hω
    by_cases h : A ω=j
    · simp only [r,binaryIndicator,Function.comp_apply,h,ite_true,y,p,hω h]
    · simp only [r,binaryIndicator,Function.comp_apply,h,ite_false,zero_mul]
  exact he.trans (selection_mean_identification μ info hX.comap_le r y p hr hp' hir hip hirp hc hi hpositive)

theorem ate_potential_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y Y0 Y1 : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hconsistency : ∀ᵐ ω ∂(P:Measure Ω),Y ω=if A ω then Y1 ω else Y0 ω)
    (hexchangeability : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le
      A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hpositive : ∀ j : Bool,∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[binaryIndicator j∘A|MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.ate d (P.map (treatmentObservation d X A Y))=
      ∫ ω,((Y1 ω:ℝ)-(Y0 ω:ℝ)) ∂(P:Measure Ω) := by
  have hi0 : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A Y0 (P:Measure Ω) :=
    hexchangeability.comp measurable_id measurable_fst
  have hi1 : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A Y1 (P:Measure Ω) :=
    hexchangeability.comp measurable_id measurable_snd
  have hc0 : ∀ᵐ ω ∂(P:Measure Ω),A ω=false→Y ω=Y0 ω := by
    filter_upwards [hconsistency] with ω hω
    intro h
    simpa only [h,Bool.false_eq_true,ite_false] using hω
  have hc1 : ∀ᵐ ω ∂(P:Measure Ω),A ω=true→Y ω=Y1 ω := by
    filter_upwards [hconsistency] with ω hω
    intro h
    simpa only [h,ite_true] using hω
  unfold Applications.MAR.ate
  rw [armMean_potential_identification d P true X A Y Y1 hX hA hY hY1 hc1 hi1 (hpositive true),
    armMean_potential_identification d P false X A Y Y0 hX hA hY hY0 hc0 hi0 (hpositive false)]
  have h0 : Integrable (fun ω=>(Y0 ω:ℝ)) (P:Measure Ω) := Integrable.of_mem_Icc 0 1
    (measurable_subtype_coe.comp hY0).aemeasurable (Eventually.of_forall (fun ω=>(Y0 ω).property))
  have h1 : Integrable (fun ω=>(Y1 ω:ℝ)) (P:Measure Ω) := Integrable.of_mem_Icc 0 1
    (measurable_subtype_coe.comp hY1).aemeasurable (Eventually.of_forall (fun ω=>(Y1 ω).property))
  exact (integral_sub h1 h0).symm

end RoughRegime.Causal
