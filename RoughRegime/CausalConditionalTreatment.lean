module

public import RoughRegime.CausalOverlap


@[expose] public section
/-! The actual ATT and ATU targets identify potential effects under the
corresponding conditional treatment measures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

 theorem selected_conditional_mean_integral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (r p : Ω→ℝ)
    (hr : Measurable[mΩ] r) (hp : Measurable[mΩ] p)
    (hir : Integrable r μ) (hip : Integrable p μ)
    (hrb : ∀ᵐ ω ∂μ,‖r ω‖≤1)
    (hi : CondIndepFun m hm r p μ) :
    (∫ ω,r ω*μ[p|m] ω ∂μ)=∫ ω,r ω*p ω ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have hprod : Integrable (fun ω=>r ω*p ω) μ := hip.bdd_mul hr.aestronglyMeasurable hrb
  have hceprod : Integrable (fun ω=>r ω*μ[p|m] ω) μ := integrable_condExp.bdd_mul hr.aestronglyMeasurable hrb
  rw [RoughRegime.Conditional.integral_mul_condExp hm r (μ[p|m]) hir stronglyMeasurable_condExp hceprod]
  rw [← integral_congr_ae (condExp_product_of_condIndep μ m hm r p hr hp hir hip hprod hi),integral_condExp hm]

 theorem conditionalEffect_potential_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d : ℕ) (P : ProbabilityMeasure Ω) (j : Bool)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y Y0 Y1 : Ω→Applications.MAR.Outcome)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hconsistency : ∀ᵐ ω ∂(P:Measure Ω),Y ω=if A ω then Y1 ω else Y0 ω)
    (hexchangeability : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le
      A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hpositive : ∀ k : Bool,∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[binaryIndicator k∘A|MeasurableSpace.comap X inferInstance] ω≠0)
    (_hselected : (P:Measure Ω) {ω|A ω=j}≠0) :
    Applications.MAR.conditionalEffect d j (P.map (treatmentObservation d X A Y))=
      ∫ ω,((Y1 ω:ℝ)-(Y0 ω:ℝ)) ∂(ProbabilityTheory.cond (P:Measure Ω) {ω|A ω=j}) := by
  let μ := (P:Measure Ω)
  let T := treatmentObservation d X A Y
  let r := binaryIndicator j∘A
  let p0 : Ω→ℝ := fun ω=>(Y0 ω:ℝ)
  let p1 : Ω→ℝ := fun ω=>(Y1 ω:ℝ)
  let info := MeasurableSpace.comap X inferInstance
  let : MeasurableSpace Ω := mΩ
  have hT : Measurable T := treatmentObservation_measurable d X A Y hX hA hY
  have hr : Measurable r := (binaryIndicator_measurable j).comp hA
  have hp0 : Measurable p0 := measurable_subtype_coe.comp hY0
  have hp1 : Measurable p1 := measurable_subtype_coe.comp hY1
  have hir : Integrable r μ := Integrable.of_mem_Icc 0 1 hr.aemeasurable
    (Eventually.of_forall (fun ω=>binaryIndicator_range j (A ω)))
  have hip0 : Integrable p0 μ := Integrable.of_mem_Icc 0 1 hp0.aemeasurable (Eventually.of_forall (fun ω=>(Y0 ω).property))
  have hip1 : Integrable p1 μ := Integrable.of_mem_Icc 0 1 hp1.aemeasurable (Eventually.of_forall (fun ω=>(Y1 ω).property))
  have hrb : ∀ᵐ ω ∂μ,‖r ω‖≤1 := Eventually.of_forall (fun ω=>by
    cases h : A ω <;> cases j <;> norm_num [r,binaryIndicator,h])
  have hi0 : CondIndepFun info hX.comap_le A Y0 μ := hexchangeability.comp measurable_id measurable_fst
  have hi1 : CondIndepFun info hX.comap_le A Y1 μ := hexchangeability.comp measurable_id measurable_snd
  have hc0 : ∀ᵐ ω ∂μ,A ω=false→Y ω=Y0 ω := by
    filter_upwards [hconsistency] with ω hω
    intro h
    simpa only [h,Bool.false_eq_true,ite_false] using hω
  have hc1 : ∀ᵐ ω ∂μ,A ω=true→Y ω=Y1 ω := by
    filter_upwards [hconsistency] with ω hω
    intro h
    simpa only [h,ite_true] using hω
  have hreg0 := regression_potential_identification d P false X A Y Y0 hX hA hY hY0 hc0 hi0 (hpositive false)
  have hreg1 := regression_potential_identification d P true X A Y Y1 hX hA hY hY1 hc1 hi1 (hpositive true)
  have hmeas (k : Bool) : Measurable (Applications.MAR.regression d k (P.map T)) :=
    ((stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable).div
      ((stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable)
  unfold Applications.MAR.conditionalEffect Applications.MAR.armProbability
  change (∫ o,Applications.MAR.armIndicator j o.2 *
    (Applications.MAR.regression d true (P.map T) o-Applications.MAR.regression d false (P.map T) o)
    ∂(μ.map T))/(∫ o,Applications.MAR.armIndicator j o.2 ∂(μ.map T))=_
  rw [integral_map (μ:=μ) (f:=fun o=>Applications.MAR.armIndicator j o.2 *
      (Applications.MAR.regression d true (P.map T) o-Applications.MAR.regression d false (P.map T) o)) hT.aemeasurable
    ((((Applications.MAR.armIndicator_measurable j).comp measurable_snd).mul
      ((hmeas true).sub (hmeas false))).aestronglyMeasurable),
    integral_map (μ:=μ) (f:=fun o=>Applications.MAR.armIndicator j o.2) hT.aemeasurable ((Applications.MAR.armIndicator_measurable j).comp measurable_snd).aestronglyMeasurable]
  change (∫ ω,r ω*(Applications.MAR.regression d true (P.map T) (T ω)-
    Applications.MAR.regression d false (P.map T) (T ω)) ∂μ)/(∫ ω,r ω ∂μ)=_
  rw [integral_congr_ae (show (fun ω=>r ω*(Applications.MAR.regression d true (P.map T) (T ω)-
    Applications.MAR.regression d false (P.map T) (T ω)))=ᵐ[μ] fun ω=>r ω*(μ[p1|info] ω-μ[p0|info] ω) from by
      filter_upwards [hreg1,hreg0] with ω h1 h0
      exact congrArg (fun v:ℝ=>r ω*v) (congrArg₂ (fun a b:ℝ=>a-b) h1 h0))]
  have hcp0 : Integrable (fun ω=>r ω*μ[p0|info] ω) μ := integrable_condExp.bdd_mul hr.aestronglyMeasurable hrb
  have hcp1 : Integrable (fun ω=>r ω*μ[p1|info] ω) μ := integrable_condExp.bdd_mul hr.aestronglyMeasurable hrb
  have hrp0 : Integrable (fun ω=>r ω*p0 ω) μ := hip0.bdd_mul hr.aestronglyMeasurable hrb
  have hrp1 : Integrable (fun ω=>r ω*p1 ω) μ := hip1.bdd_mul hr.aestronglyMeasurable hrb
  have hs : (∫ ω,r ω*(μ[p1|info] ω-μ[p0|info] ω) ∂μ)=∫ ω,r ω*(p1 ω-p0 ω) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub hcp1 hcp0,
      selected_conditional_mean_integral μ info hX.comap_le r p1 hr hp1 hir hip1 hrb
        (hi1.comp (binaryIndicator_measurable j) measurable_subtype_coe),
      selected_conditional_mean_integral μ info hX.comap_le r p0 hr hp0 hir hip0 hrb
        (hi0.comp (binaryIndicator_measurable j) measurable_subtype_coe),integral_sub hrp1 hrp0]
  rw [hs]
  have hset : MeasurableSet {ω|A ω=j} := measurableSet_eq_fun hA measurable_const
  have hrind : r={ω|A ω=j}.indicator (fun _=>(1:ℝ)) := by
    funext ω
    simp [r,binaryIndicator,Set.indicator_apply]
  have heind : (fun ω=>r ω*(p1 ω-p0 ω))={ω|A ω=j}.indicator (fun ω=>p1 ω-p0 ω) := by
    funext ω
    by_cases h:A ω=j <;> simp [r,binaryIndicator,h]
  have hden : (∫ ω,{ω|A ω=j}.indicator (fun _=>(1:ℝ)) ω ∂μ)=μ.real {ω|A ω=j} := by
    simpa only [Pi.one_def] using integral_indicator_one (μ:=μ) hset
  rw [heind,integral_indicator hset,hrind,hden]
  rw [ProbabilityTheory.cond,integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul,Measure.real,div_eq_mul_inv,mul_comm,p0,p1]
  rfl

end RoughRegime.Causal
