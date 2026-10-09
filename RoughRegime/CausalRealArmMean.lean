module

public import RoughRegime.CausalPotentialRange


@[expose] public section
/-! The actual observed mean in any selected treatment arm identifies a
measurable real potential-outcome mean. Its bounded range is derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

 theorem real_armMean_potential_identification (d : ℕ) (P : ProbabilityMeasure Ω) (j : Bool)
    (X : Ω→Model.Covariate d) (A : Ω→Bool) (Y : Ω→Applications.MAR.Outcome) (potential : Ω→ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y) (hp : Measurable potential)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),A ω=j→(Y ω:ℝ)=potential ω)
    (hex : CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A potential (P:Measure Ω))
    (hpositive : ∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘A|
      MeasurableSpace.comap X inferInstance] ω≠0) :
    Applications.MAR.armMean d j (P.map (treatmentObservation d X A Y))=
      ∫ ω,potential ω ∂(P:Measure Ω) := by
  have hr := selected_potential_range (P:Measure Ω) _ hX.comap_le A (fun ω=>(Y ω:ℝ)) potential j hA hp
    (Eventually.of_forall (fun ω=>(Y ω).property)) hc hex hpositive
  have hcclip : ∀ᵐ ω ∂(P:Measure Ω),A ω=j→Y ω=clipOutcome (potential ω) := by
    filter_upwards [hc] with ω hω
    intro hA
    rw [←clipOutcome_subtype (Y ω),hω hA]
  have h := armMean_potential_identification d P j X A Y (clipOutcome∘potential) hX hA hY
    (clipOutcome_measurable.comp hp) hcclip (hex.comp measurable_id clipOutcome_measurable) hpositive
  exact h.trans (integral_congr_ae (hr.mono (fun ω hω=>clipOutcome_coe_eq _ hω)))

end RoughRegime.Causal
