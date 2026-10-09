module

public import RoughRegime.PoissonKernels


@[expose] public section
/-! The observation marginal of a genuine density kernel is its density mixture. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace RoughRegime.GeneralTesting
set_option backward.isDefEq.respectTransparency false

variable {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]

 theorem densityKernel_marginal_integrable (prior : Measure W) [IsProbabilityMeasure prior]
    (μ : Measure Ω) [SFinite μ] (f : W → Ω → ℝ) (hf : Measurable (Function.uncurry f))
    (hf0 : ∀ w x, 0 ≤ f w x) (hfi : ∀ x, Integrable (fun w => f w x) prior) :
    (prior ⊗ₘ (Kernel.const W μ).withDensity (fun w x => ENNReal.ofReal (f w x))).snd =
      μ.withDensity (fun x => ENNReal.ofReal (∫ w, f w x ∂prior)) := by
  have : IsSFiniteKernel ((Kernel.const W μ).withDensity (fun w x => ENNReal.ofReal (f w x))) :=
    Kernel.IsSFiniteKernel.withDensity _ fun _ _ => ENNReal.ofReal_ne_top
  have hff : Measurable (Function.uncurry (fun w x => ENNReal.ofReal (f w x))) := hf.ennreal_ofReal
  ext s hs
  rw [Measure.snd_apply hs, Measure.compProd_apply (measurable_snd hs), withDensity_apply _ hs]
  simp_rw [Kernel.withDensity_apply (Kernel.const W μ) hff, Kernel.const_apply]
  change (∫⁻ w, μ.withDensity (fun x => ENNReal.ofReal (f w x)) s ∂prior) = _
  simp_rw [withDensity_apply _ hs]
  simp_rw [ofReal_integral_eq_lintegral_ofReal (hfi _) (Filter.Eventually.of_forall (fun w => hf0 w _))]
  exact lintegral_lintegral_swap hff.aemeasurable

end RoughRegime.GeneralTesting
