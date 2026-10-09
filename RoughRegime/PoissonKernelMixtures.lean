module

public import RoughRegime.KernelMixtures


@[expose] public section
/-! The phase-prior mixtures are marginals of the genuine common Poisson
observation kernel, as required by fuzzy testing. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {W Y : Type*} [MeasurableSpace W] [MeasurableSpace Y]
variable (μ : Measure Y) (prior : Measure W)
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure prior]

theorem observationKernel_marginal (A : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C) (hbA : ∀ w, |A.density w| ≤ V)
    (hbψ : ∀ w y, |ψ w y| ≤ C) (hψ0 : ∀ w y, 0 ≤ ψ w y)
    (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) (rate : ℝ≥0) :
    (A.measure ⊗ₘ observationKernel μ ψ hψ rate).snd =
      (markedMixtureLaw μ prior A ψ hψ V C hV hC hbA hbψ hψ0 hmean rate).measure := by
  rw [observationKernel_eq_withDensity μ ψ hψ C hbψ hψ0 hmean]
  have hm : Measurable (Function.uncurry (fun (w : W) (x : PointConfiguration Y) => tensor ψ x.1 w x.2)) :=
    measurable_point_product_function _ (fun n => tensor_measurable ψ hψ n)
  rw [GeneralTesting.densityKernel_marginal_integrable A.measure (referenceProcess μ rate)
    (fun w x => tensor ψ x.1 w x.2) hm
    (fun w x => tensor_nonneg ψ hψ0 x.1 w x.2)
    (fun x => bounded_integrable A.measure _
      (hm.comp (measurable_id.prodMk measurable_const)) (C ^ x.1)
      (fun w => tensor_bound ψ C hC hbψ x.1 w x.2))]
  congr 1
  funext x
  rw [densityLaw_integral prior A (fun w => tensor ψ x.1 w x.2)]
  rfl

end RoughRegime.PoissonMeasure
