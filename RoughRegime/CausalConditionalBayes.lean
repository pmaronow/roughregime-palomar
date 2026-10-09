module

public import RoughRegime.CausalHomogeneity
public import RoughRegime.Conditional


@[expose] public section
/-! Conditional means under an actual event-conditioned probability measure
are the conditional selected mean divided by its conditional event mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace RoughRegime.Causal
set_option maxHeartbeats 900000

theorem conditional_event_mean {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (C : Set Ω) (hC : MeasurableSet[mΩ] C) (hμC : μ C≠0)
    (effect : Ω→ℝ) (he : Measurable[mΩ] effect) (heb : ∀ᵐ ω ∂μ,|effect ω|≤1)
    (hq : ∀ᵐ ω ∂μ,0<μ[C.indicator (fun _=> (1:ℝ))|m] ω) :
    (cond μ C)[effect|m]=ᵐ[cond μ C] fun ω=>
      μ[C.indicator effect|m] ω/μ[C.indicator (fun _=>(1:ℝ))|m] ω := by
  let : MeasurableSpace Ω := mΩ
  let i : Ω→ℝ := C.indicator (fun _=>1)
  let q := μ[i|m]
  let N := μ[C.indicator effect|m]
  let H : Ω→ℝ := fun ω=>N ω/q ω
  have hi : Measurable i := measurable_const.indicator hC
  have hib : ∀ω,‖i ω‖≤1 := by intro ω;by_cases h:ω∈C <;> simp [i,h]
  have hii : Integrable i μ := Integrable.of_bound hi.aestronglyMeasurable 1 (Eventually.of_forall hib)
  have hei : Integrable effect μ := Integrable.of_bound he.aestronglyMeasurable 1 (by
    simpa only [Real.norm_eq_abs] using heb)
  have hie : Integrable (C.indicator effect) μ := hei.indicator hC
  have hb : ∀ᵐ ω ∂μ,-i ω ≤ C.indicator effect ω ∧ C.indicator effect ω ≤ i ω := by
    filter_upwards [heb] with ω hw
    by_cases h:ω∈C
    · simpa only [i,Set.indicator_of_mem h] using abs_le.mp hw
    · simp [i,h]
  have hu := condExp_mono (m:=m) hie hii (hb.mono (fun _ h=>h.2))
  have hl := condExp_mono (m:=m) hii.neg hie (hb.mono (fun _ h=>h.1))
  have hn := condExp_neg i m (μ:=μ)
  have hHbound : ∀ᵐ ω ∂μ,|H ω|≤1 := by
    filter_upwards [hq,hu,hl,hn] with ω hq hu hl hn
    change 0<q ω at hq
    change N ω ≤ q ω at hu
    change μ[-i|m] ω ≤ N ω at hl
    change μ[-i|m] ω = -q ω at hn
    rw [hn] at hl
    apply abs_le.mpr
    exact ⟨(le_div_iff₀ hq).mpr (by simpa only [neg_one_mul] using hl),
      (div_le_iff₀ hq).mpr (by simpa only [one_mul] using hu)⟩
  have hHm : StronglyMeasurable[m] H := stronglyMeasurable_condExp.div stronglyMeasurable_condExp
  have hHambient := hHm.mono hm
  have hHi : Integrable H μ := Integrable.of_bound hHambient.aestronglyMeasurable 1 (by
    simpa only [Real.norm_eq_abs] using hHbound)
  have hiH : Integrable (i*H) μ := hHi.bdd_mul hi.aestronglyMeasurable (Eventually.of_forall hib)
  have hHc : ∀ᵐ ω ∂cond μ C,|H ω|≤1 := hHbound.filter_mono cond_absolutelyContinuous.ae_le
  have : IsProbabilityMeasure (cond μ C) := cond_isProbabilityMeasure hμC
  have hHci : Integrable H (cond μ C) := Integrable.of_bound hHambient.aestronglyMeasurable 1 (by
    simpa only [Real.norm_eq_abs] using hHc)
  have hec : ∀ᵐ ω ∂cond μ C,|effect ω|≤1 := heb.filter_mono cond_absolutelyContinuous.ae_le
  have heci : Integrable effect (cond μ C) := Integrable.of_bound he.aestronglyMeasurable 1 (by
    simpa only [Real.norm_eq_abs] using hec)
  have hsIntegral : ∀ s,MeasurableSet[m] s→∫ω in s,H ω ∂cond μ C=∫ω in s,effect ω ∂cond μ C := by
    intro s hs
    have hp := condExp_mul_of_stronglyMeasurable_right hHm hiH hii
    have hpe : ∀ᵐ ω ∂μ, μ[i*H|m] ω = q ω * H ω := by
      filter_upwards [hp] with ω hw
      exact hw
    have hcancel : (fun ω=>q ω*H ω)=ᵐ[μ] N := by
      filter_upwards [hq] with ω hq
      change 0<q ω at hq
      dsimp only [H]
      exact mul_div_cancel₀ _ (ne_of_gt hq)
    have heq : (∫ω in s,i ω*H ω ∂μ)=(∫ω in s,C.indicator effect ω ∂μ) := by
      calc
        _ = ∫ω in s,μ[i*H|m] ω ∂μ := (setIntegral_condExp hm hiH hs).symm
        _ = ∫ω in s,q ω*H ω ∂μ := integral_congr_ae
          (ae_restrict_of_ae hpe)
        _ = ∫ω in s,N ω ∂μ := integral_congr_ae (ae_restrict_of_ae hcancel)
        _ = _ := setIntegral_condExp hm hie hs
    have heq' : (∫ω in s∩C,H ω ∂μ)=(∫ω in s∩C,effect ω ∂μ) := by
      have hiHeq : (fun ω => i ω * H ω) = C.indicator H := by
        funext ω
        by_cases hw : ω ∈ C <;> simp [i, hw]
      rw [hiHeq, setIntegral_indicator hC, setIntegral_indicator hC] at heq
      exact heq
    unfold ProbabilityTheory.cond
    simp only [Measure.restrict_smul, integral_smul_measure,
      Measure.restrict_restrict (hm s hs)]
    rw [heq']
  have ha := ae_eq_condExp_of_forall_setIntegral_eq hm heci
    (fun _ _ _=>hHci.integrableOn) (fun s hs _=>hsIntegral s hs) hHm.aestronglyMeasurable
  exact ha.symm

theorem ae_eq_of_cond_eq_of_conditional_mass_pos {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (C : Set Ω) (hC : MeasurableSet[mΩ] C)
    (hq : ∀ᵐ ω ∂μ, 0 < μ[C.indicator (fun _ => (1 : ℝ))|m] ω)
    (f g : Ω → ℝ) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
    (heq : f =ᵐ[cond μ C] g) : f =ᵐ[μ] g := by
  let : MeasurableSpace Ω := mΩ
  let B := {ω | f ω ≠ g ω}
  have hBm : MeasurableSet[m] B := (hf.measurableSet_eq_fun hg).compl
  have hB : MeasurableSet B := hm B hBm
  have hcond : (cond μ C) B = 0 := by
    simpa only [Filter.EventuallyEq, ae_iff, B] using heq
  have hCB : μ (C ∩ B) = 0 := by
    rw [cond_apply hC] at hcond
    rcases mul_eq_zero.mp hcond with hi | hi
    · have htop : μ C = ⊤ := by simp at hi
      exact False.elim ((measure_ne_top μ C) htop)
    · exact hi
  let i : Ω → ℝ := C.indicator (fun _ => 1)
  let q := μ[i|m]
  have hi : Integrable i μ := Integrable.of_bound
    (measurable_const.indicator hC).aestronglyMeasurable 1 (by
      apply Eventually.of_forall
      intro ω
      by_cases hw : ω ∈ C <;> simp [i, hw])
  have hzero : ∫ ω in B, q ω ∂μ = 0 := by
    rw [setIntegral_condExp hm hi hBm, setIntegral_indicator hC, setIntegral_const]
    simp [Measure.real, inter_comm B C, hCB]
  have hnonneg : 0 ≤ᵐ[μ.restrict B] q :=
    (ae_restrict_of_ae hq).mono (fun _ hw => hw.le)
  have hz : q =ᵐ[μ.restrict B] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg (integrable_condExp.integrableOn)).mp hzero
  have hempty : ∀ᵐ ω ∂μ, ω ∉ B := by
    have hz' := (ae_restrict_iff' hB).mp hz
    filter_upwards [hq, hz'] with ω hp hz
    intro hw
    exact (ne_of_gt hp) (hz hw)
  filter_upwards [hempty] with ω hw
  exact not_ne_iff.mp hw

theorem conditional_event_mean_ae_original {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (C : Set Ω) (hC : MeasurableSet[mΩ] C) (hμC : μ C ≠ 0)
    (effect : Ω → ℝ) (he : Measurable[mΩ] effect) (heb : ∀ᵐ ω ∂μ, |effect ω| ≤ 1)
    (hq : ∀ᵐ ω ∂μ, 0 < μ[C.indicator (fun _ => (1 : ℝ))|m] ω) :
    (cond μ C)[effect|m] =ᵐ[μ] fun ω =>
      μ[C.indicator effect|m] ω / μ[C.indicator (fun _ => (1 : ℝ))|m] ω := by
  let : MeasurableSpace Ω := mΩ
  exact ae_eq_of_cond_eq_of_conditional_mass_pos μ m hm C hC hq _ _
    stronglyMeasurable_condExp (stronglyMeasurable_condExp.div stronglyMeasurable_condExp)
    (conditional_event_mean μ m hm C hC hμC effect he heb hq)

theorem conditional_event_mean_ae_original_of_bound_on_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (C : Set Ω) (hC : MeasurableSet[mΩ] C) (hμC : μ C ≠ 0)
    (effect : Ω → ℝ) (he : Measurable[mΩ] effect)
    (heb : ∀ᵐ ω ∂μ, ω ∈ C → |effect ω| ≤ 1)
    (hq : ∀ᵐ ω ∂μ, 0 < μ[C.indicator (fun _ => (1 : ℝ))|m] ω) :
    (cond μ C)[effect|m] =ᵐ[μ] fun ω =>
      μ[C.indicator effect|m] ω / μ[C.indicator (fun _ => (1 : ℝ))|m] ω := by
  let : MeasurableSpace Ω := mΩ
  have hib : ∀ᵐ ω ∂μ, |C.indicator effect ω| ≤ 1 := by
    filter_upwards [heb] with ω hw
    by_cases h : ω ∈ C
    · simpa only [Set.indicator_of_mem h] using hw h
    · simp [h]
  have hmem : ∀ᵐ ω ∂cond μ C, ω ∈ C := ae_cond_mem hC
  have hie : effect =ᵐ[cond μ C] C.indicator effect :=
    hmem.mono (fun _ h => (Set.indicator_of_mem h effect).symm)
  have hce : (cond μ C)[effect|m] =ᵐ[μ] (cond μ C)[C.indicator effect|m] :=
    ae_eq_of_cond_eq_of_conditional_mass_pos μ m hm C hC hq _ _
      stronglyMeasurable_condExp stronglyMeasurable_condExp (condExp_congr_ae hie)
  have hbayes := conditional_event_mean_ae_original μ m hm C hC hμC
    (C.indicator effect) (he.indicator hC) hib hq
  simpa only [Set.indicator_indicator, Set.inter_self] using hce.trans hbayes

end RoughRegime.Causal
