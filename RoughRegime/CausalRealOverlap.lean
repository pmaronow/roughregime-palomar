module

public import RoughRegime.CausalRealTreatment
public import RoughRegime.CausalOverlap


@[expose] public section
/-! The literal causal overlap identity for arbitrary measurable real
potential outcomes. Their bounded ranges follow from the source assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

theorem real_overlap_effect_potential_identification {Ω:Type*} [mΩ:MeasurableSpace Ω]
    [StandardBorelSpace Ω] (d:ℕ) (P:ProbabilityMeasure Ω)
    (X:Ω→Model.Covariate d) (A:Ω→Bool) (Y:Ω→Applications.MAR.Outcome) (Y0 Y1:Ω→ℝ)
    (hX:Measurable X) (hA:Measurable A) (hY:Measurable Y) (hY0:Measurable Y0) (hY1:Measurable Y1)
    (hc:∀ᵐ ω ∂(P:Measure Ω),(Y ω:ℝ)=if A ω then Y1 ω else Y0 ω)
    (hex:CondIndepFun (MeasurableSpace.comap X inferInstance) hX.comap_le A
      (fun ω=>(Y0 ω,Y1 ω)) (P:Measure Ω))
    (hpositive:∀ j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘A|
      MeasurableSpace.comap X inferInstance] ω≠0) :
    let w:=(P:Measure Ω)[binaryIndicator true∘A|MeasurableSpace.comap X inferInstance]
    let t0:=(P:Measure Ω)[Y0|MeasurableSpace.comap X inferInstance]
    let t1:=(P:Measure Ω)[Y1|MeasurableSpace.comap X inferInstance]
    Applications.Overlap.effect d (P.map (treatmentObservation d X A Y))=
      (∫ ω,w ω*(1-w ω)*(t1 ω-t0 ω) ∂(P:Measure Ω)) /
      (∫ ω,w ω*(1-w ω) ∂(P:Measure Ω)) := by
  have hr:=real_potential_outcomes_range d P X A Y Y0 Y1 hX hA hY0 hY1 hc hex hpositive
  have hexclip:=hex.comp measurable_id
    ((clipOutcome_measurable.comp measurable_fst).prodMk (clipOutcome_measurable.comp measurable_snd))
  have h:=overlap_effect_potential_identification d P X A Y (clipOutcome∘Y0) (clipOutcome∘Y1)
    hX hA hY (clipOutcome_measurable.comp hY0) (clipOutcome_measurable.comp hY1)
    (real_potential_clipping_consistency P A Y Y0 Y1 hc) hexclip
  have h0:(fun ω=>(clipOutcome (Y0 ω):ℝ))=ᵐ[(P:Measure Ω)] Y0:=hr.1.mono
    (fun ω hω=>clipOutcome_coe_eq _ hω)
  have h1:(fun ω=>(clipOutcome (Y1 ω):ℝ))=ᵐ[(P:Measure Ω)] Y1:=hr.2.mono
    (fun ω hω=>clipOutcome_coe_eq _ hω)
  have he0:=condExp_congr_ae h0 (m:=MeasurableSpace.comap X inferInstance)
  have he1:=condExp_congr_ae h1 (m:=MeasurableSpace.comap X inferInstance)
  apply h.trans
  congr 1
  apply integral_congr_ae
  filter_upwards [he0,he1] with ω h0 h1
  simp only [Function.comp_apply]
  rw [h0,h1]

end RoughRegime.Causal
