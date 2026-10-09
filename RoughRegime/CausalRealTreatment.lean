module

public import RoughRegime.CausalPotentialRange


@[expose] public section
/-! Treatment identification with measurable real potential outcomes.
Only the observed outcome is bounded; both potential ranges are derived
from actual consistency, conditional exchangeability and positivity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

 theorem real_potential_outcomes_range (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if A ω then Y1 ω else Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘A|
      MeasurableSpace.comap X inferInstance] ω≠0) :
    (∀ᵐ ω ∂(P:Measure Ω),Y0 ω∈Icc (0:ℝ) 1) ∧ (∀ᵐ ω ∂(P:Measure Ω),Y1 ω∈Icc (0:ℝ) 1) := by
  have hyr : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)∈Icc (0:ℝ) 1 := Eventually.of_forall (fun ω=>(Y ω).property)
  constructor
  · apply selected_potential_range (P:Measure Ω) _ hX.comap_le A (fun ω=>(Y ω:ℝ)) Y0 false hA hY0 hyr
    · filter_upwards [hc] with ω hω
      intro h
      simpa only [h,Bool.false_eq_true,ite_false] using hω
    · exact hex.comp measurable_id measurable_fst
    · exact hpositive false
  · apply selected_potential_range (P:Measure Ω) _ hX.comap_le A (fun ω=>(Y ω:ℝ)) Y1 true hA hY1 hyr
    · filter_upwards [hc] with ω hω
      intro h
      simpa only [h,ite_true] using hω
    · exact hex.comp measurable_id measurable_snd
    · exact hpositive true

 omit [StandardBorelSpace Ω] in
 theorem real_potential_clipping_consistency (P : ProbabilityMeasure Ω) (A : Ω→Bool)
    (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if A ω then Y1 ω else Y0 ω) :
    ∀ᵐ ω ∂(P:Measure Ω),Y ω=if A ω then clipOutcome (Y1 ω) else clipOutcome (Y0 ω) := by
  filter_upwards [hc] with ω hω
  rw [←clipOutcome_subtype (Y ω),hω]
  cases A ω <;> rfl

 theorem real_ate_potential_identification (d : ℕ) (P : ProbabilityMeasure Ω)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if A ω then Y1 ω else Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘A|
      MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.ate d (P.map (treatmentObservation d X A Y))=
      ∫ ω,Y1 ω-Y0 ω ∂(P:Measure Ω) := by
  have hr := real_potential_outcomes_range d P X A Y Y0 Y1 hX hA hY0 hY1 hc hex hpositive
  have hexclip := hex.comp measurable_id
    ((clipOutcome_measurable.comp measurable_fst).prodMk (clipOutcome_measurable.comp measurable_snd))
  have h := ate_potential_identification d P X A Y (clipOutcome∘Y0) (clipOutcome∘Y1) hX hA hY
    (clipOutcome_measurable.comp hY0) (clipOutcome_measurable.comp hY1)
    (real_potential_clipping_consistency P A Y Y0 Y1 hc) hexclip hpositive
  exact h.trans (integral_congr_ae (by
    filter_upwards [hr.1,hr.2] with ω h0 h1
    rw [Function.comp_apply,Function.comp_apply,clipOutcome_coe_eq _ h1,clipOutcome_coe_eq _ h0]))

 omit [StandardBorelSpace Ω] in
 theorem selection_mass_ne_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω→Bool) (j : Bool)
    (m : MeasurableSpace Ω)
    (hpositive : ∀ᵐ ω ∂μ,μ[binaryIndicator j∘A|m] ω≠0) :
    μ {ω|A ω=j}≠0 := by
  let : MeasurableSpace Ω := mΩ
  intro hz
  have hnot : ∀ᵐ ω ∂μ,ω∉{ω|A ω=j} := measure_eq_zero_iff_ae_notMem.mp hz
  have hi : binaryIndicator j∘A=ᵐ[μ] 0 := hnot.mono (fun ω hω=>by
    have hA : A ω≠j := hω
    simp [binaryIndicator,Function.comp_apply,hA])
  have he := condExp_congr_ae hi (m:=m)
  rw [condExp_zero] at he
  have hf : ∀ᵐ ω ∂μ,False := by
    filter_upwards [hpositive,he] with ω hp he
    exact hp he
  exact hf.exists.choose_spec

 theorem real_conditionalEffect_potential_identification (d : ℕ) (P : ProbabilityMeasure Ω) (j : Bool)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (Y0 Y1 : Ω→ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hY0 : Measurable Y0) (hY1 : Measurable Y1)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if A ω then Y1 ω else Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hpositive : ∀k:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator k∘A|
      MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.conditionalEffect d j (P.map (treatmentObservation d X A Y))=
      ∫ ω,Y1 ω-Y0 ω ∂(cond (P:Measure Ω) {ω|A ω=j}) := by
  have hr := real_potential_outcomes_range d P X A Y Y0 Y1 hX hA hY0 hY1 hc hex hpositive
  have hexclip := hex.comp measurable_id
    ((clipOutcome_measurable.comp measurable_fst).prodMk (clipOutcome_measurable.comp measurable_snd))
  have hselected := selection_mass_ne_zero (P:Measure Ω) A j (MeasurableSpace.comap X inferInstance) (hpositive j)
  have h := conditionalEffect_potential_identification d P j X A Y (clipOutcome∘Y0) (clipOutcome∘Y1) hX hA hY
    (clipOutcome_measurable.comp hY0) (clipOutcome_measurable.comp hY1)
    (real_potential_clipping_consistency P A Y Y0 Y1 hc) hexclip hpositive hselected
  exact h.trans (integral_congr_ae (by
    filter_upwards [hr.1.filter_mono cond_absolutelyContinuous.ae_le,
      hr.2.filter_mono cond_absolutelyContinuous.ae_le] with ω h0 h1
    rw [Function.comp_apply,Function.comp_apply,clipOutcome_coe_eq _ h1,clipOutcome_coe_eq _ h0]))

end RoughRegime.Causal
