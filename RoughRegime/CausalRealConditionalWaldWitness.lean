module

public import RoughRegime.CausalRealConditionalWald


@[expose] public section
/-! Native source-class conditional Wald identification for real potentials.
Balance, one-sided uptake and first-stage positivity come from the actual
observed-law witness; no extra observed-law assumption is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.RealIVData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

 theorem witness_complier_identification (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : RealIVData A.d Ω)
    (W : Applications.ConditionalWald.Witness A (P.map D.observation))
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω)) :
    (∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω) ∧
    (W.b∘D.X=ᵐ[(P:Measure Ω)] (cond (P:Measure Ω) D.complierSet)[D.effect|
      MeasurableSpace.comap D.X inferInstance]) := by
  let Wb : Applications.ConditionalWald.Witness A (P.map D.bounded.observation) := {
    p := W.p
    q := W.q
    b := W.b
    measurableP := W.measurableP
    measurableQ := W.measurableQ
    measurableB := W.measurableB
    nonnegativeP := W.nonnegativeP
    marginal := by simpa only [D.bounded_law_eq P hc] using W.marginal
    instrumentHalf := by simpa only [D.bounded_law_eq P hc] using W.instrumentHalf
    oneSided := by simpa only [D.bounded_law_eq P hc] using W.oneSided
    momentD := by simpa only [D.bounded_law_eq P hc] using W.momentD
    momentV := by simpa only [D.bounded_law_eq P hc] using W.momentV
    overlap := W.overlap
    smoothInverse := W.smoothInverse
    smoothB := W.smoothB
    densityBounds := W.densityBounds }
  have hbounded := D.bounded.witness_complier_identification A P Wb (D.bounded_exchangeable P hex)
  have hq : ∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω := hbounded.1
  have hb := (D.bounded.witness_pullback A P Wb).1
  have hpositive := D.balanced_instrument_positive P hb
  have he := D.complier_effect_eq_bounded P hc hex hpositive
  have hmem : ∀ᵐ ω ∂cond (P:Measure Ω) D.complierSet,ω∈D.complierSet := ae_cond_mem D.complierSet_measurable
  have hec : D.bounded.effect=ᵐ[cond (P:Measure Ω) D.complierSet] D.effect := by
    filter_upwards [he.filter_mono cond_absolutelyContinuous.ae_le,hmem] with ω hω hC
    simpa only [show D.bounded.complierSet=D.complierSet from rfl,Set.indicator_of_mem hC] using hω.symm
  have hce := ae_eq_of_cond_eq_of_conditional_mass_pos (P:Measure Ω)
    (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.complierSet D.complierSet_measurable hq
    ((cond (P:Measure Ω) D.complierSet)[D.bounded.effect|MeasurableSpace.comap D.X inferInstance])
    ((cond (P:Measure Ω) D.complierSet)[D.effect|MeasurableSpace.comap D.X inferInstance])
    stronglyMeasurable_condExp stronglyMeasurable_condExp (condExp_congr_ae hec)
  refine ⟨hq,?_⟩
  have hbEq : W.b∘D.X=Wb.b∘D.bounded.X := rfl
  rw [hbEq]
  exact hbounded.2.trans hce

 theorem witness_ate_of_homogeneity (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : RealIVData A.d Ω)
    (W : Applications.ConditionalWald.Witness A (P.map D.observation))
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hei : Integrable D.effect (P:Measure Ω))
    (hhom : (P:Measure Ω)[D.effect|MeasurableSpace.comap (fun ω=>(D.X ω,D.A1 ω)) inferInstance]=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[D.effect|MeasurableSpace.comap D.X inferInstance]) :
    Applications.ConditionalWald.target A.d (P.map D.observation)=∫ ω,D.effect ω ∂(P:Measure Ω) := by
  let Wb : Applications.ConditionalWald.Witness A (P.map D.bounded.observation) := {
    p := W.p
    q := W.q
    b := W.b
    measurableP := W.measurableP
    measurableQ := W.measurableQ
    measurableB := W.measurableB
    nonnegativeP := W.nonnegativeP
    marginal := by simpa only [D.bounded_law_eq P hc] using W.marginal
    instrumentHalf := by simpa only [D.bounded_law_eq P hc] using W.instrumentHalf
    oneSided := by simpa only [D.bounded_law_eq P hc] using W.oneSided
    momentD := by simpa only [D.bounded_law_eq P hc] using W.momentD
    momentV := by simpa only [D.bounded_law_eq P hc] using W.momentV
    overlap := W.overlap
    smoothInverse := W.smoothInverse
    smoothB := W.smoothB
    densityBounds := W.densityBounds }
  obtain ⟨hb,hs,_⟩ := D.bounded.witness_pullback A P Wb
  have hq := (D.witness_complier_identification A P W hc hex).1
  exact D.conditionalWald_ate_of_homogeneity P hc hex hb hs (hq.mono (fun _ h=>ne_of_gt h)) hei hhom

end RoughRegime.Causal.RealIVData
