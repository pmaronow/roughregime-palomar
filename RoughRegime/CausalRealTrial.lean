module

public import RoughRegime.CausalTreatmentClass
public import RoughRegime.CausalIVConditional
public import RoughRegime.ApplicationTrial


@[expose] public section
/-! The randomized-trial transformed outcome has the genuine potential-outcome
CATE as conditional mean. Bounds for real potentials are inherited from the
observed outcome, consistency, randomization and positivity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

 theorem real_regression_potential_identification (d : ℕ) (P : ProbabilityMeasure Ω) (j : Bool)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (potential : Ω→ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hp : Measurable potential)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),A ω=j→(Y ω:ℝ)=potential ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A potential (P:Measure Ω))
    (hpositive : ∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘A|
      MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.regression d j (P.map (treatmentObservation d X A Y))∘treatmentObservation d X A Y=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[potential|MeasurableSpace.comap X inferInstance] := by
  have hr := selected_potential_range (P:Measure Ω) _ hX.comap_le A (fun ω=>(Y ω:ℝ)) potential j hA hp
    (Eventually.of_forall (fun ω=>(Y ω).property)) hc hex hpositive
  have hcclip : ∀ᵐ ω ∂(P:Measure Ω),A ω=j→Y ω=clipOutcome (potential ω) := by
    filter_upwards [hc] with ω hω
    intro hA
    rw [←clipOutcome_subtype (Y ω),hω hA]
  have h := regression_potential_identification d P j X A Y (clipOutcome∘potential) hX hA hY
    (clipOutcome_measurable.comp hp) hcclip (hex.comp measurable_id clipOutcome_measurable) hpositive
  exact h.trans (condExp_congr_ae (hr.mono (fun ω hω=>clipOutcome_coe_eq _ hω)))

 theorem trial_transformed_conditional_eq_real_cate (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if A ω then Y1 ω else Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hb : (P:Measure Ω)[binaryIndicator true∘A|MeasurableSpace.comap X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ)) :
    (P:Measure Ω)[(fun ω=>(Applications.Trial.transformedResponse (A ω,Y ω):ℝ))|
      MeasurableSpace.comap X inferInstance]=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[(fun ω=>Y1 ω-Y0 ω)|MeasurableSpace.comap X inferInstance] := by
  let μ := (P:Measure Ω)
  let T := treatmentObservation d X A Y
  let Q := P.map T
  let m := MeasurableSpace.comap (Prod.fst:Model.Covariate d×Applications.Trial.Response→_) inferInstance
  let info := MeasurableSpace.comap X inferInstance
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace (Model.Covariate d×Applications.Trial.Response) :=
    (inferInstance:MeasurableSpace (Model.Covariate d)).prod (inferInstance:MeasurableSpace Applications.Trial.Response)
  have hT : Measurable T := treatmentObservation_measurable d X A Y hX hA hY
  have hm : m ≤ (inferInstance:MeasurableSpace (Model.Covariate d×Applications.Trial.Response)) := measurable_fst.comap_le
  have hinfo : MeasurableSpace.comap T m=info := by rw [MeasurableSpace.comap_comp];rfl
  have hir : Integrable ((Applications.MAR.armIndicator true∘Prod.snd)∘T) μ :=
    Integrable.of_mem_Icc 0 1 (((Applications.MAR.armIndicator_measurable true).comp measurable_snd).comp hT).aemeasurable
      (Eventually.of_forall (fun ω=>binaryIndicator_range true (A ω)))
  have hCEr := condExp_map_pullback μ T hT m hm (Applications.MAR.armIndicator true∘Prod.snd)
    ((Applications.MAR.armIndicator_measurable true).comp measurable_snd) hir
  rw [hinfo] at hCEr
  have hr : (Applications.MAR.armIndicator true∘Prod.snd)∘T=binaryIndicator true∘A := rfl
  rw [hr] at hCEr
  have hbObs : (Q:Measure (Model.Covariate d×Applications.Trial.Response))[
      Applications.MAR.armIndicator true∘Prod.snd|m]=ᵐ[(Q:Measure (Model.Covariate d×Applications.Trial.Response))] fun _=>(1/2:ℝ) := by
    apply (ae_map_iff hT.aemeasurable (measurableSet_eq_fun
      ((stronglyMeasurable_condExp.mono hm).measurable) measurable_const)).mpr
    exact hCEr.trans hb
  have hTrial := Applications.Trial.transformed_conditional_eq_cate d (Q:Measure _) hbObs
  have hFull := ae_of_ae_map hT.aemeasurable hTrial
  have hpositive : ∀j:Bool,∀ᵐ ω ∂μ,μ[binaryIndicator j∘A|info] ω≠0 := by
    intro j
    cases j
    · exact (balanced_indicator_false μ info hX.comap_le A hA hb).mono (fun _ h=>by rw [h];norm_num)
    · exact hb.mono (fun _ h=>by rw [h];norm_num)
  have h0 := real_regression_potential_identification d P false X A Y Y0 hX hA hY hY0
    (hc.mono (fun ω h hA=>by simpa only [hA,Bool.false_eq_true,ite_false] using h))
    (hex.comp measurable_id measurable_fst) (hpositive false)
  have h1 := real_regression_potential_identification d P true X A Y Y1 hX hA hY hY1
    (hc.mono (fun ω h hA=>by simpa only [hA,ite_true] using h))
    (hex.comp measurable_id measurable_snd) (hpositive true)
  have hRange := real_potential_outcomes_range d P X A Y Y0 Y1 hX hA hY0 hY1 hc hex hpositive
  have hi0 : Integrable Y0 μ := Integrable.of_mem_Icc 0 1 hY0.aemeasurable hRange.1
  have hi1 : Integrable Y1 μ := Integrable.of_mem_Icc 0 1 hY1.aemeasurable hRange.2
  have hd := condExp_sub hi1 hi0 info
  have hiScore : Integrable (((fun z=>(Applications.Trial.transformedResponse z:ℝ))∘Prod.snd)∘T) μ := by
    apply Integrable.of_mem_Icc (-1) 1
      ((measurable_subtype_coe.comp Applications.Trial.transformedResponse_measurable).comp (hT.snd)).aemeasurable
    exact Eventually.of_forall (fun ω=>(Applications.Trial.transformedResponse (A ω,Y ω)).property)
  have hCEscore := condExp_map_pullback μ T hT m hm
    ((fun z=>(Applications.Trial.transformedResponse z:ℝ))∘Prod.snd)
    ((measurable_subtype_coe.comp Applications.Trial.transformedResponse_measurable).comp measurable_snd) hiScore
  rw [hinfo] at hCEscore
  filter_upwards [hCEscore,hFull,h0,h1,hd] with ω hscore hfull h0 h1 hd
  change μ[(fun ω=>(Applications.Trial.transformedResponse (A ω,Y ω):ℝ))|info] ω=μ[(fun ω=>Y1 ω-Y0 ω)|info] ω
  change ((μ.map T)[(fun z=>(Applications.Trial.transformedResponse z:ℝ))∘Prod.snd|m]) (T ω)=
    μ[(fun ω=>(Applications.Trial.transformedResponse (A ω,Y ω):ℝ))|info] ω at hscore
  change ((μ.map T)[(fun z=>(Applications.Trial.transformedResponse z:ℝ))∘Prod.snd|m]) (T ω)=
    Applications.MAR.regression d true Q (T ω)-Applications.MAR.regression d false Q (T ω) at hfull
  change Applications.MAR.regression d true Q (T ω)=μ[Y1|info] ω at h1
  change Applications.MAR.regression d false Q (T ω)=μ[Y0|info] ω at h0
  calc
    _ = ((μ.map T)[(fun z=>(Applications.Trial.transformedResponse z:ℝ))∘Prod.snd|m]) (T ω) := hscore.symm
    _ = Applications.MAR.regression d true Q (T ω)-Applications.MAR.regression d false Q (T ω) := hfull
    _ = μ[Y1|info] ω-μ[Y0|info] ω := congrArg₂ (fun a b:ℝ=>a-b) h1 h0
    _ = _ := hd.symm

 theorem trial_transformed_variance_eq_effect_heterogeneity (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if A ω then Y1 ω else Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hb : (P:Measure Ω)[binaryIndicator true∘A|MeasurableSpace.comap X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ)) :
    Var[(P:Measure Ω)[(fun ω=>(Applications.Trial.transformedResponse (A ω,Y ω):ℝ))|
      MeasurableSpace.comap X inferInstance];(P:Measure Ω)]=
      Var[(P:Measure Ω)[(fun ω=>Y1 ω-Y0 ω)|MeasurableSpace.comap X inferInstance];(P:Measure Ω)] :=
  variance_congr (trial_transformed_conditional_eq_real_cate d P X A Y Y0 Y1 hX hA hY hY0 hY1 hc hex hb)

end RoughRegime.Causal
