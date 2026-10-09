module

public import RoughRegime.CausalConditionalWald


@[expose] public section
/-! The ordinary Wald target is the first-stage-weighted conditional complier
mean; the conditional Wald target uses the original covariate distribution. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.IVData
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem wald_weighted_conditional_complier (A : Model.Parameters) (P : ProbabilityMeasure Ω)
    (D : IVData A.d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (honesided : ∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω)
    (hcomplier : ∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|MeasurableSpace.comap D.X inferInstance] ω≠0) :
    Applications.Wald.target A (P.map D.observation)=
      (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
        MeasurableSpace.comap D.X inferInstance] ω*D.conditionalComplierEffect P ω ∂(P:Measure Ω))/
        (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
          MeasurableSpace.comap D.X inferInstance] ω ∂(P:Measure Ω)) := by
  have h0 := D.no_always_takers P hex hbalance honesided
  have hmono : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω := h0.mono (fun ω hω=>by simp [hω])
  have hpositive : ∀ j:Bool,∀ᵐ ω ∂(P:Measure Ω),
      (P:Measure Ω)[binaryIndicator j∘D.Z|MeasurableSpace.comap D.X inferInstance] ω≠0 := by
    intro j
    exact (D.balanced_selectors P hbalance j).mono (fun ω h=>by
      change (P:Measure Ω)[D.selector j|MeasurableSpace.comap D.X inferInstance] ω≠0
      rw [h]
      norm_num)
  have hn : (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω*D.conditionalComplierEffect P ω ∂(P:Measure Ω))=
      ∫ ω in D.complierSet,D.effect ω ∂(P:Measure Ω) := by
    rw [integral_congr_ae (show (fun ω=>(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω*D.conditionalComplierEffect P ω)=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[D.complierSet.indicator D.effect|MeasurableSpace.comap D.X inferInstance] from by
        filter_upwards [hcomplier] with ω hω
        exact mul_div_cancel₀ _ hω),integral_condExp D.hX.comap_le,integral_indicator D.complierSet_measurable]
  have hd : (∫ ω,(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω ∂(P:Measure Ω))=(P:Measure Ω).real D.complierSet := by
    rw [integral_condExp D.hX.comap_le]
    simpa only [Pi.one_def] using integral_indicator_one (μ:=(P:Measure Ω)) D.complierSet_measurable
  unfold Applications.Wald.target
  rw [D.numerator_complier A P hex hpositive hmono,D.denominator_complier A P hex hpositive hmono,hn,hd]

end RoughRegime.Causal.IVData
