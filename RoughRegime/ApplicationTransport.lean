module

public import RoughRegime.Model


@[expose] public section
/-! Conditional moments under actual measurable transformations of observations. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications

/-- Conditional moments descend along a measurable pushforward. The hypothesis
is the input conditional expectation on the pulled-back information sigma algebra. -/
theorem conditional_map {Ω Y : Type*} [mΩ : MeasurableSpace Ω] [mY : MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Y) (hT : Measurable T)
    (m : MeasurableSpace Y) (hm : m ≤ mY) (f g : Y → ℝ)
    (hf : @Measurable Y ℝ mY inferInstance f) (hg : @Measurable Y ℝ m inferInstance g)
    (hfi : Integrable (f ∘ T) μ)
    (hc : μ[f ∘ T | MeasurableSpace.comap T m] =ᵐ[μ] g ∘ T) :
    (@Measure.map Ω Y mΩ mY T μ)[f | m] =ᵐ[@Measure.map Ω Y mΩ mY T μ] g := by
  let : MeasurableSpace Y := mY
  have hgm : @Measurable Y ℝ mY inferInstance g :=
    measurable_iff_comap_le.mpr ((measurable_iff_comap_le.mp hg).trans hm)
  have hfout : Integrable f (μ.map T) :=
    (integrable_map_measure hf.aestronglyMeasurable hT.aemeasurable).mpr hfi
  have hgout : Integrable g (μ.map T) :=
    (integrable_map_measure hgm.aestronglyMeasurable hT.aemeasurable).mpr
      (integrable_condExp.congr hc)
  have hpull : MeasurableSpace.comap T m ≤ mΩ :=
    (MeasurableSpace.comap_mono hm).trans (measurable_iff_comap_le.mp hT)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hfout
    (fun s _ _ => hgout.integrableOn) ?_ hg.stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  rw [setIntegral_map (hm s hs) hgm.aestronglyMeasurable hT.aemeasurable,
    setIntegral_map (hm s hs) hf.aestronglyMeasurable hT.aemeasurable]
  have hsPull : @MeasurableSet Ω (MeasurableSpace.comap T m) (T ⁻¹' s) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨s, hs, rfl⟩
  calc
    _ = ∫ o in T ⁻¹' s, μ[f ∘ T | MeasurableSpace.comap T m] o ∂μ :=
      integral_congr_ae (hc.symm.filter_mono ae_restrict_le)
    _ = _ := setIntegral_condExp hpull hfi hsPull

/-- Adding independent auxiliary randomness preserves every input conditional moment. -/
theorem conditional_fst_product {Ω S : Type*} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hfi : Integrable f μ) (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    (@Measure.prod Ω S mΩ mS μ ν)[f ∘ Prod.fst | MeasurableSpace.comap Prod.fst m] =ᵐ[
      @Measure.prod Ω S mΩ mS μ ν]
      (μ[f | m]) ∘ Prod.fst := by
  let : MeasurableSpace Ω := mΩ
  have hmap : (μ.prod ν).map Prod.fst = μ := by simp
  have hfp : Integrable (f ∘ Prod.fst) (μ.prod ν) := by
    apply Integrable.comp_measurable (f := Prod.fst) _ measurable_fst
    simpa only [hmap] using hfi
  have hgp : Integrable ((μ[f | m]) ∘ Prod.fst) (μ.prod ν) := by
    apply Integrable.comp_measurable (f := Prod.fst) _ measurable_fst
    simpa only [hmap] using (integrable_condExp : Integrable (μ[f | m]) μ)
  have hmp : MeasurableSpace.comap (@Prod.fst Ω S) m ≤ (mΩ.prod mS) :=
    (MeasurableSpace.comap_mono hm).trans (measurable_iff_comap_le.mp measurable_fst)
  have hfst : @Measurable (Ω × S) Ω (MeasurableSpace.comap Prod.fst m) m Prod.fst :=
    measurable_iff_comap_le.mpr le_rfl
  apply (ae_eq_condExp_of_forall_setIntegral_eq hmp hfp
    (fun s _ _ => hgp.integrableOn) ?_
    (stronglyMeasurable_condExp.comp_measurable hfst).aestronglyMeasurable).symm
  intro Q hQ _
  obtain ⟨s, hs, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hQ
  have hgmeas : AEStronglyMeasurable (μ[f | m]) ((μ.prod ν).map Prod.fst) := by
    rw [hmap]
    exact (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hfmeas : AEStronglyMeasurable f ((μ.prod ν).map Prod.fst) := by
    rw [hmap]
    exact hfi.aestronglyMeasurable
  simp only [Function.comp_apply]
  rw [← setIntegral_map (hm s hs) hgmeas measurable_fst.aemeasurable,
    ← setIntegral_map (hm s hs) hfmeas measurable_fst.aemeasurable, hmap]
  exact setIntegral_condExp hm hfi hs

/-- A randomized response product averages the independent seed exactly. -/
theorem conditional_product_mul {Ω S : Type*} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hfi : Integrable f μ) (h : S → ℝ) (hhi : Integrable h ν)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    (@Measure.prod Ω S mΩ mS μ ν)[(fun o => f o.1 * h o.2) |
      MeasurableSpace.comap Prod.fst m] =ᵐ[@Measure.prod Ω S mΩ mS μ ν]
      fun o => (μ[f | m]) o.1 * ∫ s, h s ∂ν := by
  let : MeasurableSpace Ω := mΩ
  have hmap : (μ.prod ν).map Prod.fst = μ := by simp
  have hgpi : Integrable ((μ[f | m]) ∘ Prod.fst) (μ.prod ν) := by
    apply Integrable.comp_measurable (f := Prod.fst) _ measurable_fst
    simpa only [hmap] using (integrable_condExp : Integrable (μ[f | m]) μ)
  have hmp : MeasurableSpace.comap (@Prod.fst Ω S) m ≤ (mΩ.prod mS) :=
    (MeasurableSpace.comap_mono hm).trans (measurable_iff_comap_le.mp measurable_fst)
  have hfst : @Measurable (Ω × S) Ω (MeasurableSpace.comap Prod.fst m) m Prod.fst :=
    measurable_iff_comap_le.mpr le_rfl
  apply (ae_eq_condExp_of_forall_setIntegral_eq hmp (hfi.mul_prod hhi)
    (fun s _ _ => (hgpi.mul_const _).integrableOn) ?_
    ((stronglyMeasurable_condExp.comp_measurable hfst).mul_const _).aestronglyMeasurable).symm
  intro Q hQ _
  obtain ⟨s, hs, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hQ
  have hset : Prod.fst ⁻¹' s = s ×ˢ (univ : Set S) := by ext x; simp
  rw [hset]
  simp only [Function.comp_apply]
  rw [setIntegral_prod_mul (μ[f | m]) (fun _ : S => ∫ t, h t ∂ν) s univ,
    setIntegral_prod_mul f h s univ]
  simp only [integral_const, Measure.restrict_univ, probReal_univ,
    smul_eq_mul, one_mul]
  rw [setIntegral_condExp hm hfi hs]

end RoughRegime.Applications
