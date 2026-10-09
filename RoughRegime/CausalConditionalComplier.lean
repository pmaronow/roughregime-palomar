module

public import RoughRegime.CausalConditionalWald
public import RoughRegime.CausalConditionalBayes


@[expose] public section
/-! The conditional complier mean is taken under the genuine complier
conditional probability measure; positivity identifies its covariate version
also under the original covariate distribution. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.IVData
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem complier_mass_ne_zero (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hq : ∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω) : (P:Measure Ω) D.complierSet≠0 := by
  intro hzero
  have hnot : ∀ᵐ ω ∂(P:Measure Ω),ω∉D.complierSet := measure_eq_zero_iff_ae_notMem.mp hzero
  have hi : D.complierSet.indicator (fun _=>(1:ℝ))=ᵐ[(P:Measure Ω)] 0 :=
    hnot.mono (fun ω hω=>by simp [hω])
  have he := condExp_congr_ae hi (m:=MeasurableSpace.comap D.X inferInstance)
  rw [condExp_zero] at he
  have hf : ∀ᵐ ω ∂(P:Measure Ω),False := by
    filter_upwards [hq,he] with ω hp hz
    change _=0 at hz
    rw [hz] at hp
    exact (lt_irrefl (0:ℝ)) hp
  exact hf.exists.choose_spec

theorem conditionalComplierEffect_eq_conditional_mean (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hq : ∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω) :
    D.conditionalComplierEffect P=ᵐ[(P:Measure Ω)]
      (cond (P:Measure Ω) D.complierSet)[D.effect|MeasurableSpace.comap D.X inferInstance] := by
  have heb : ∀ᵐ ω ∂(P:Measure Ω),|D.effect ω|≤1 := Eventually.of_forall (fun ω=>by
    apply abs_le.mpr
    dsimp only [effect]
    constructor <;> linarith [(D.Y0 ω).property.1,(D.Y0 ω).property.2,(D.Y1 ω).property.1,(D.Y1 ω).property.2])
  exact (conditional_event_mean_ae_original (P:Measure Ω) (MeasurableSpace.comap D.X inferInstance)
    D.hX.comap_le D.complierSet D.complierSet_measurable (D.complier_mass_ne_zero P hq)
    D.effect D.effect_measurable heb hq).symm

variable [StandardBorelSpace Ω]

theorem conditionalWald_actual_conditional_complier (P : ProbabilityMeasure Ω) (D : IVData d Ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hbalance : (P:Measure Ω)[D.selector true|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (honesided : ∀ᵐ ω ∂(P:Measure Ω),D.observedTreatment ω≤D.Z ω)
    (hq : ∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω) :
    Applications.ConditionalWald.target d (P.map D.observation)=
      ∫ ω,(cond (P:Measure Ω) D.complierSet)[D.effect|
        MeasurableSpace.comap D.X inferInstance] ω ∂(P:Measure Ω) :=
  (D.conditionalWald_complier_identification P hex hbalance honesided).trans
    (integral_congr_ae (D.conditionalComplierEffect_eq_conditional_mean P hq))

end RoughRegime.Causal.IVData
