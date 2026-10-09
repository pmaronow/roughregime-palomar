module

public import RoughRegime.CausalRealIV


@[expose] public section
/-! Conditional Wald identification with unrestricted measurable real
potentials. Bounds are inherited only on compliers; the homogeneity clause
uses the original integrable effect, including never-taker effects. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.RealIVData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

def conditionalComplierEffect (P : ProbabilityMeasure Ω) (D : RealIVData d Ω) (ω : Ω) : ℝ :=
  (P:Measure Ω)[D.complierSet.indicator D.effect|MeasurableSpace.comap D.X inferInstance] ω/
    (P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|MeasurableSpace.comap D.X inferInstance] ω

 omit [StandardBorelSpace Ω] in
 theorem balanced_instrument_positive (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hb : (P:Measure Ω)[binaryIndicator true∘D.Z|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ)) :
    ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘D.Z|
      MeasurableSpace.comap D.X inferInstance] ω≠0 := by
  intro j
  have h := D.bounded.balanced_selectors P hb j
  filter_upwards [h] with ω hω
  change (P:Measure Ω)[D.bounded.selector j|MeasurableSpace.comap D.bounded.X inferInstance] ω≠0
  rw [hω]
  norm_num

 theorem conditionalWald_complier_identification (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hb : (P:Measure Ω)[binaryIndicator true∘D.Z|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (hs : ∀ᵐ ω ∂(P:Measure Ω),D.treatment ω≤D.Z ω) :
    Applications.ConditionalWald.target d (P.map D.observation)=
      ∫ ω,D.conditionalComplierEffect P ω ∂(P:Measure Ω) := by
  have h := D.bounded.conditionalWald_complier_identification P (D.bounded_exchangeable P hex) hb hs
  rw [D.bounded_law_eq P hc] at h
  have he := condExp_congr_ae (D.complier_effect_eq_bounded P hc hex (D.balanced_instrument_positive P hb))
    (m:=MeasurableSpace.comap D.X inferInstance)
  apply h.trans (integral_congr_ae ?_)
  filter_upwards [he] with ω hω
  change _/((P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
    MeasurableSpace.comap D.X inferInstance]) ω=_
  exact congrArg (fun a:ℝ=>a/((P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
    MeasurableSpace.comap D.X inferInstance]) ω) hω.symm

 theorem complier_effect_bound (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hpositive : ∀j:Bool,∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[binaryIndicator j∘D.Z|
      MeasurableSpace.comap D.X inferInstance] ω≠0) :
    ∀ᵐ ω ∂(P:Measure Ω),ω∈D.complierSet→|D.effect ω|≤1 := by
  filter_upwards [D.complier_potential_ranges P hc hex hpositive] with ω hω
  intro hC
  have hp := hω hC
  apply abs_le.mpr
  dsimp only [effect]
  constructor <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2]

 theorem conditionalWald_actual_conditional_complier (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hb : (P:Measure Ω)[binaryIndicator true∘D.Z|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (hs : ∀ᵐ ω ∂(P:Measure Ω),D.treatment ω≤D.Z ω)
    (hq : ∀ᵐ ω ∂(P:Measure Ω),0<(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω) :
    Applications.ConditionalWald.target d (P.map D.observation)=
      ∫ ω,(cond (P:Measure Ω) D.complierSet)[D.effect|MeasurableSpace.comap D.X inferInstance] ω ∂(P:Measure Ω) := by
  have hbayes := conditional_event_mean_ae_original_of_bound_on_event (P:Measure Ω)
    (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.complierSet D.complierSet_measurable
    (D.bounded.complier_mass_ne_zero P hq) D.effect D.effect_measurable
    (D.complier_effect_bound P hc hex (D.balanced_instrument_positive P hb)) hq
  exact (D.conditionalWald_complier_identification P hc hex hb hs).trans (integral_congr_ae hbayes.symm)

 theorem conditionalWald_ate_of_homogeneity (P : ProbabilityMeasure Ω) (D : RealIVData d Ω)
    (hc : ∀ᵐ ω ∂(P:Measure Ω),(D.Y ω:ℝ)=if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
    (hb : (P:Measure Ω)[binaryIndicator true∘D.Z|MeasurableSpace.comap D.X inferInstance]=ᵐ[(P:Measure Ω)] fun _=>(1/2:ℝ))
    (hs : ∀ᵐ ω ∂(P:Measure Ω),D.treatment ω≤D.Z ω)
    (hq : ∀ᵐ ω ∂(P:Measure Ω),(P:Measure Ω)[D.complierSet.indicator (fun _=>(1:ℝ))|
      MeasurableSpace.comap D.X inferInstance] ω≠0)
    (hei : Integrable D.effect (P:Measure Ω))
    (hhom : (P:Measure Ω)[D.effect|MeasurableSpace.comap (fun ω=>(D.X ω,D.A1 ω)) inferInstance]=ᵐ[(P:Measure Ω)]
      (P:Measure Ω)[D.effect|MeasurableSpace.comap D.X inferInstance]) :
    Applications.ConditionalWald.target d (P.map D.observation)=∫ ω,D.effect ω ∂(P:Measure Ω) := by
  let μ := (P:Measure Ω)
  let m1 := MeasurableSpace.comap D.X inferInstance
  let : MeasurableSpace Ω := mΩ
  let m2 := MeasurableSpace.comap (fun ω=>(D.X ω,D.A1 ω)) inferInstance
  let : MeasurableSpace Ω := mΩ
  let g : Ω→ℝ := binaryIndicator true∘D.A1
  have hm12 : m1 ≤ m2 := MeasurableSpace.comap_le_comap_of_eq_comp Prod.fst measurable_fst rfl
  have hm2 : m2 ≤ mΩ := (D.hX.prodMk D.hA1).comap_le
  have hg : StronglyMeasurable[m2] g := ((binaryIndicator_measurable true).comp
    (measurable_snd.comp (comap_measurable (fun ω=>(D.X ω,D.A1 ω))))).stronglyMeasurable
  have hgb : ∀ᵐ ω ∂μ,‖g ω‖≤(1:ℝ) := Eventually.of_forall (fun ω=>by
    cases hA : D.A1 ω <;> norm_num [g,binaryIndicator,hA])
  have hfac := selected_effect_of_mean_homogeneity μ m1 m2 hm12 hm2 g D.effect hg 1 hgb hei hhom
  have h0 := D.bounded.no_always_takers P (D.bounded_exchangeable P hex) hb hs
  have hcg : D.complierSet.indicator (fun _=>(1:ℝ))=ᵐ[μ] g := by
    filter_upwards [h0] with ω hω
    change D.A0 ω=false at hω
    cases hA : D.A1 ω <;> simp [complierSet,g,binaryIndicator,hω,hA]
  have hce : D.complierSet.indicator D.effect=ᵐ[μ] fun ω=>g ω*D.effect ω := by
    filter_upwards [h0] with ω hω
    change D.A0 ω=false at hω
    cases hA : D.A1 ω <;> simp [complierSet,g,binaryIndicator,hω,hA]
  rw [D.conditionalWald_complier_identification P hc hex hb hs,←integral_condExp D.hX.comap_le (f:=D.effect)]
  apply integral_congr_ae
  filter_upwards [condExp_congr_ae hcg (m:=m1),condExp_congr_ae hce (m:=m1),hfac,hq] with ω hq hy hf hpos
  change μ[D.complierSet.indicator D.effect|m1] ω/μ[D.complierSet.indicator (fun _=>(1:ℝ))|m1] ω=μ[D.effect|m1] ω
  rw [hy,hf,←hq]
  exact mul_div_cancel_left₀ _ hpos

end RoughRegime.Causal.RealIVData
