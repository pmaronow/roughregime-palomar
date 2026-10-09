module

public import RoughRegime.LowerMeasure


@[expose] public section
/-! Genuine heterogeneous finite product experiments and Hellinger
subadditivity, used for independent Poisson block pairs. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal
namespace RoughRegime.LowerMeasure
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

 def productDensityLaw {n : ℕ} (L : Fin n → GeneralTesting.DensityLaw μ) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)) where
  density xs := ∏ i, (L i).density (xs i)
  measurable := Finset.measurable_prod _ (fun i _ => (L i).measurable.comp (measurable_pi_apply i))
  integrable := Integrable.fintype_prod fun i => (L i).integrable
  nonneg := by
    have h : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
        ∀ i, 0 ≤ (L i).density (xs i) := ae_le_pi (fun i => (L i).nonneg)
    filter_upwards [h] with xs hx
    exact Finset.prod_nonneg fun i _ => hx i
  integral_one := by
    rw [integral_fin_nat_prod_eq_prod]
    simp only [GeneralTesting.DensityLaw.integral_one, Finset.prod_const_one]

 theorem productDensityLaw_measure {n : ℕ} (L : Fin n → GeneralTesting.DensityLaw μ) :
    (productDensityLaw L).measure = Measure.pi (fun i => (L i).measure) := by
  apply (Measure.pi_eq (μ := fun i : Fin n => (L i).measure) ?_).symm
  intro s hs
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hrhs : (∏ i : Fin n, (L i).measure (s i)) ≠ ∞ := by
    rw [← Measure.pi_pi (fun i : Fin n => (L i).measure)]
    exact measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hrhs).mp
  rw [ENNReal.toReal_prod]
  change (productDensityLaw L).measure.real (Set.univ.pi s) = ∏ i, (L i).measure.real (s i)
  rw [(productDensityLaw L).measureReal_eq_setIntegral _ hS]
  simp_rw [(L _).measureReal_eq_setIntegral _ (hs _)]
  rw [Measure.restrict_pi_pi]
  change (∫ xs : Fin n → Ω, ∏ i, (L i).density (xs i) ∂Measure.pi (fun i => μ.restrict (s i))) = _
  rw [integral_fin_nat_prod_eq_prod (fun i : Fin n => (L i).density)]

 theorem densityAffinity_product {n : ℕ} (L R : Fin n → GeneralTesting.DensityLaw μ) :
    densityAffinity (productDensityLaw L) (productDensityLaw R) = ∏ i, densityAffinity (L i) (R i) := by
  have hp : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i, 0 ≤ (L i).density (xs i) := ae_le_pi (fun i => (L i).nonneg)
  have hq : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i, 0 ≤ (R i).density (xs i) := ae_le_pi (fun i => (R i).nonneg)
  have he : (fun xs : Fin n → Ω => Real.sqrt ((productDensityLaw L).density xs) *
      Real.sqrt ((productDensityLaw R).density xs)) =ᵐ[Measure.pi (fun _ : Fin n => μ)]
      fun xs => ∏ i, Real.sqrt ((L i).density (xs i)) * Real.sqrt ((R i).density (xs i)) := by
    filter_upwards [hp, hq] with xs hpx hqx
    change Real.sqrt (∏ i, (L i).density (xs i)) * Real.sqrt (∏ i, (R i).density (xs i)) = _
    rw [Lower.sqrt_finite_product _ hpx, Lower.sqrt_finite_product _ hqx, Finset.prod_mul_distrib]
  unfold densityAffinity
  rw [integral_congr_ae he, integral_fin_nat_prod_eq_prod (fun i : Fin n => fun x : Ω =>
    Real.sqrt ((L i).density x) * Real.sqrt ((R i).density x))]

 theorem one_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have ha' : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hai := ha i (Finset.mem_insert_self _ _)
    have hP : (∏ j ∈ s, a j) ≤ 1 := Finset.prod_le_one₀ (fun j hj => (ha' j hj).1) (fun j hj => (ha' j hj).2)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hh := ih ha'
    nlinarith [mul_nonneg (sub_nonneg.mpr hai.2) (sub_nonneg.mpr hP)]

 theorem hellinger_product_le {n : ℕ} (L R : Fin n → GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared (productDensityLaw L) (productDensityLaw R) ≤
      ∑ i, GeneralTesting.hellingerSquared (L i) (R i) := by
  rw [hellinger_integral_eq, densityAffinity_product]
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
