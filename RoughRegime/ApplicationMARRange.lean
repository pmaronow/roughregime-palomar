module

public import RoughRegime.ApplicationMARUpper


@[expose] public section
/-! The observed MAR mean is in the unit interval for every response law,
 including laws with zero observation probability on parts of the design. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR

 theorem observedOutcome_le_observed (z : Response) : observedOutcome z≤observed z := by
   cases z with
   | inl _=>simp [observedOutcome,observed]
   | inr z=>exact z.property.2

 theorem observedMean_mem_Icc (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d×Response)) :
     observedMean d P∈Icc (0:ℝ) 1 := by
   let μ := (P:Measure (Model.Covariate d×Response))
   let m : MeasurableSpace (Model.Covariate d×Response) := MeasurableSpace.comap Prod.fst inferInstance
   let f := μ[observedOutcome∘Prod.snd|m]
   let g := μ[observed∘Prod.snd|m]
   have hf : Integrable (observedOutcome∘Prod.snd) μ := Integrable.of_mem_Icc 0 1
     (observedOutcome_measurable.comp measurable_snd).aemeasurable
     (Filter.Eventually.of_forall (fun o=>observedOutcome_range o.2))
   have hg : Integrable (observed∘Prod.snd) μ := Integrable.of_mem_Icc 0 1
     (observed_measurable.comp measurable_snd).aemeasurable
     (Filter.Eventually.of_forall (fun o=>observed_range o.2))
   have hfp : 0≤ᵐ[μ] f := condExp_nonneg (Filter.Eventually.of_forall (fun o=>(observedOutcome_range o.2).1))
   have hgp : 0≤ᵐ[μ] g := condExp_nonneg (Filter.Eventually.of_forall (fun o=>(observed_range o.2).1))
   have hfg : f≤ᵐ[μ] g := condExp_mono hf hg (Filter.Eventually.of_forall (fun o=>observedOutcome_le_observed o.2))
   have hr : ∀ᵐ o ∂μ,f o/g o∈Icc (0:ℝ) 1 := by
     filter_upwards [hfp,hgp,hfg] with o hp hq hle
     refine ⟨div_nonneg hp hq,?_⟩
     by_cases hz : g o=0
     · simp [hz]
     · exact (div_le_one (lt_of_le_of_ne hq (Ne.symm hz))).mpr hle
   have hm : AEMeasurable (fun o=>f o/g o) μ :=
     ((stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable.div
       (stronglyMeasurable_condExp.mono measurable_fst.comap_le).measurable).aemeasurable
   have hi : Integrable (fun o=>f o/g o) μ := Integrable.of_mem_Icc 0 1 hm hr
   change 0≤(∫ o,f o/g o ∂μ) ∧ (∫ o,f o/g o ∂μ)≤1
   refine ⟨integral_nonneg_of_ae (hr.mono (fun _ h=>h.1)),?_⟩
   have hu := integral_mono_ae hi (integrable_const (1:ℝ)) (hr.mono (fun _ h=>h.2))
   simpa only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using hu

end RoughRegime.Applications.MAR
