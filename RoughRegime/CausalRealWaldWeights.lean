module

public import RoughRegime.CausalRealConditionalWald
public import RoughRegime.CausalWaldClass


@[expose] public section
/-! General first-stage weighting of the actual Wald target. Conditional
complier probability may vanish; the weighted identity still holds exactly. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

 theorem conditional_indicator_ratio_cancel {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω)
    (C : Set Ω) (hC : MeasurableSet[mΩ] C) (effect : Ω→ℝ) (he : Measurable[mΩ] effect)
    (heb : ∀ᵐ ω ∂μ,ω∈C→|effect ω|≤1) :
    (fun ω=>μ[C.indicator (fun _=>(1:ℝ))|m] ω *
      (μ[C.indicator effect|m] ω/μ[C.indicator (fun _=>(1:ℝ))|m] ω))=ᵐ[μ]
      μ[C.indicator effect|m] := by
  let : MeasurableSpace Ω := mΩ
  let i := C.indicator (fun _=>(1:ℝ))
  let e := C.indicator effect
  have hbound : ∀ᵐ ω ∂μ,-i ω ≤ e ω ∧ e ω ≤ i ω := by
    filter_upwards [heb] with ω hω
    by_cases h:ω∈C
    · simpa only [i,e,Set.indicator_of_mem h] using abs_le.mp (hω h)
    · simp [i,e,h]
  have hi : Integrable i μ := Integrable.of_mem_Icc 0 1 (measurable_const.indicator hC).aemeasurable
    (Eventually.of_forall (fun ω=>by by_cases h:ω∈C <;> simp [i,h]))
  have heint : Integrable e μ := Integrable.of_mem_Icc (-1) 1 (he.indicator hC).aemeasurable (by
    filter_upwards [heb] with ω hω
    by_cases h:ω∈C
    · simpa only [e,Set.indicator_of_mem h,Set.mem_Icc] using abs_le.mp (hω h)
    · simp [e,h])
  have hu := condExp_mono (m:=m) heint hi (hbound.mono (fun _ h=>h.2))
  have hl := condExp_mono (m:=m) hi.neg heint (hbound.mono (fun _ h=>h.1))
  have hn := condExp_neg i m (μ:=μ)
  filter_upwards [hu,hl,hn] with ω hu hl hn
  change μ[i|m] ω*(μ[e|m] ω/μ[i|m] ω)=μ[e|m] ω
  by_cases hq:μ[i|m] ω=0
  · rw [hn] at hl
    change -μ[i|m] ω ≤ μ[e|m] ω at hl
    rw [hq] at hl hu
    have hezero : μ[e|m] ω=0 := by linarith
    simp [hq,hezero]
  · exact mul_div_cancel₀ _ hq

namespace RealIVData
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

 theorem wald_weighted_conditional_complier (A : Model.Parameters) (P : ProbabilityMeasure Ω)
    (D : RealIVData A.d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘D.Z|
      MeasurableSpace.comap D.X inferInstance] ω≠0)
    (hmono : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω) :
    Applications.Wald.target A (P.map D.observation)=
      (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
        MeasurableSpace.comap D.X inferInstance] ω*D.conditionalComplierEffect P ω ∂(P:Measure Ω))/
        (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
          MeasurableSpace.comap D.X inferInstance] ω ∂(P:Measure Ω)) := by
  have he := D.complier_effect_eq_bounded P hc hex hpositive
  have hnum := D.bounded.numerator_complier A P (D.bounded_exchangeable P hex) hpositive hmono
  have hden := D.bounded.denominator_complier A P (D.bounded_exchangeable P hex) hpositive hmono
  rw [D.bounded_law_eq P hc] at hnum hden
  have hnumReal : Applications.Wald.numerator A (P.map D.observation)=
      ∫ ω in D.complierSet,D.effect ω ∂(P:Measure Ω) := by
    apply hnum.trans
    have hI := integral_congr_ae he.symm
    rw [integral_indicator D.complierSet_measurable,
      integral_indicator D.bounded.complierSet_measurable] at hI
    exact hI
  have hn : (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω*D.conditionalComplierEffect P ω ∂(P:Measure Ω))=
      ∫ ω in D.complierSet,D.effect ω ∂(P:Measure Ω) := by
    have hcancel := conditional_indicator_ratio_cancel (P:Measure Ω)
      (MeasurableSpace.comap D.X inferInstance) D.complierSet D.complierSet_measurable D.effect D.effect_measurable
      (D.complier_effect_bound P hc hex hpositive)
    dsimp only [conditionalComplierEffect]
    rw [integral_congr_ae hcancel,integral_condExp D.hX.comap_le,integral_indicator D.complierSet_measurable]
  have hd : (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω ∂(P:Measure Ω))=(P:Measure Ω).real D.complierSet := by
    rw [integral_condExp D.hX.comap_le]
    simpa only [Pi.one_def] using integral_indicator_one (μ:=(P:Measure Ω)) D.complierSet_measurable
  unfold Applications.Wald.target
  rw [hnumReal,hden,hn,hd]
  rfl

 theorem class_wald_weighted_conditional_complier (A : Model.Parameters) (P : ProbabilityMeasure Ω)
    (D : RealIVData A.d Ω) (cW : ℝ)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hmono : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω)
    (hclass : P.map D.observation∈Applications.Wald.modelClass A cW) :
    Applications.Wald.target A (P.map D.observation)=
      (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
        MeasurableSpace.comap D.X inferInstance] ω*D.conditionalComplierEffect P ω ∂(P:Measure Ω))/
        (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
          MeasurableSpace.comap D.X inferInstance] ω ∂(P:Measure Ω)) :=
  D.wald_weighted_conditional_complier A P hc hex (D.class_instrument_positive A P cW hclass) hmono

end RealIVData
end RoughRegime.Causal
