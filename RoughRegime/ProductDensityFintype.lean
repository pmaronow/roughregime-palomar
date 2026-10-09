module

public import RoughRegime.ProductTesting


@[expose] public section
/-! True density products and Hellinger subadditivity for arbitrary finite
indices, including the original named spatial block pairs. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal
namespace RoughRegime.LowerMeasure
set_option backward.isDefEq.respectTransparency false

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

 def fintypeProductDensityLaw (L : ι → GeneralTesting.DensityLaw μ) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : ι => μ)) where
  density xs := ∏ i, (L i).density (xs i)
  measurable := Finset.measurable_prod _ (fun i _ => (L i).measurable.comp (measurable_pi_apply i))
  integrable := Integrable.fintype_prod fun i => (L i).integrable
  nonneg := by
    have h : ∀ᵐ xs : ι → Ω ∂Measure.pi (fun _ : ι => μ),
        ∀ i, 0 ≤ (L i).density (xs i) := ae_le_pi (fun i => (L i).nonneg)
    filter_upwards [h] with xs hx
    exact Finset.prod_nonneg fun i _ => hx i
  integral_one := by
    rw [integral_fintype_prod_eq_prod]
    simp only [GeneralTesting.DensityLaw.integral_one, Finset.prod_const_one]

 theorem fintypeProductDensityLaw_measure (L : ι → GeneralTesting.DensityLaw μ) :
    (fintypeProductDensityLaw L).measure = Measure.pi (fun i => (L i).measure) := by
  apply (Measure.pi_eq (μ := fun i : ι => (L i).measure) ?_).symm
  intro s hs
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hrhs : (∏ i : ι, (L i).measure (s i)) ≠ ∞ := by
    rw [← Measure.pi_pi (fun i : ι => (L i).measure)]
    exact measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hrhs).mp
  rw [ENNReal.toReal_prod]
  change (fintypeProductDensityLaw L).measure.real (Set.univ.pi s) = ∏ i, (L i).measure.real (s i)
  rw [(fintypeProductDensityLaw L).measureReal_eq_setIntegral _ hS]
  simp_rw [(L _).measureReal_eq_setIntegral _ (hs _)]
  rw [Measure.restrict_pi_pi]
  change (∫ xs : ι → Ω, ∏ i, (L i).density (xs i) ∂Measure.pi (fun i => μ.restrict (s i))) = _
  rw [integral_fintype_prod_eq_prod (fun i : ι => (L i).density)]

 theorem densityAffinity_fintypeProduct (L R : ι → GeneralTesting.DensityLaw μ) :
    densityAffinity (fintypeProductDensityLaw L) (fintypeProductDensityLaw R) = ∏ i, densityAffinity (L i) (R i) := by
  have hp : ∀ᵐ xs : ι → Ω ∂Measure.pi (fun _ : ι => μ),
      ∀ i, 0 ≤ (L i).density (xs i) := ae_le_pi (fun i => (L i).nonneg)
  have hq : ∀ᵐ xs : ι → Ω ∂Measure.pi (fun _ : ι => μ),
      ∀ i, 0 ≤ (R i).density (xs i) := ae_le_pi (fun i => (R i).nonneg)
  have he : (fun xs : ι → Ω => Real.sqrt ((fintypeProductDensityLaw L).density xs) *
      Real.sqrt ((fintypeProductDensityLaw R).density xs)) =ᵐ[Measure.pi (fun _ : ι => μ)]
      fun xs => ∏ i, Real.sqrt ((L i).density (xs i)) * Real.sqrt ((R i).density (xs i)) := by
    filter_upwards [hp, hq] with xs hpx hqx
    change Real.sqrt (∏ i, (L i).density (xs i)) * Real.sqrt (∏ i, (R i).density (xs i)) = _
    rw [Lower.sqrt_finite_product _ hpx, Lower.sqrt_finite_product _ hqx, Finset.prod_mul_distrib]
  unfold densityAffinity
  rw [integral_congr_ae he, integral_fintype_prod_eq_prod (fun i : ι => fun x : Ω =>
    Real.sqrt ((L i).density x) * Real.sqrt ((R i).density x))]

 theorem hellinger_fintypeProduct_le (L R : ι → GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared (fintypeProductDensityLaw L) (fintypeProductDensityLaw R) ≤
      ∑ i, GeneralTesting.hellingerSquared (L i) (R i) := by
  classical
  rw [hellinger_integral_eq, densityAffinity_fintypeProduct]
  have h := one_sub_prod_le_sum Finset.univ (fun i => densityAffinity (L i) (R i))
    (fun i _ => ⟨densityAffinity_nonneg _ _, densityAffinity_le_one _ _⟩)
  simp_rw [hellinger_integral_eq]
  have he : (∑ i, (2 - 2 * densityAffinity (L i) (R i))) =
      2 * ∑ i, (1 - densityAffinity (L i) (R i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linarith

end RoughRegime.LowerMeasure
