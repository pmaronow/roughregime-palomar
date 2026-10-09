module

public import RoughRegime.Model
public import RoughRegime.Conditional
public import RoughRegime.UniformCube


@[expose] public section
/-! Known bounded design statistics have precisely the source moments, derived
from the actual model conditional expectation identities. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory

 theorem observable_weighted_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (R : Z → ℝ) (hR : Measurable R) (C : ℝ) (hC : 0 ≤ C) (hRC : ∀ z, |R z| ≤ C)
    (cf : Covariate A.d → ℝ) (hcf : Measurable cf)
    (hcond : (P : Measure (Observation A Z))[R ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))] cf ∘ Prod.fst)
    (φ : Covariate A.d → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ x, |φ x| ≤ B) :
    (∫ o, R o.2 * φ o.1 ∂(P : Measure (Observation A Z))) =
      ∫ x, h.p x * (cf x * φ x) ∂cubeVolume A.d := by
  have hm : covariateInformation A Z ≤ (inferInstance : MeasurableSpace (Observation A Z)) :=
    measurable_fst.comap_le
  have hRi : Integrable (R ∘ Prod.snd) (P : Measure (Observation A Z)) := by
    apply Integrable.of_bound (hR.comp measurable_snd).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun o => by simpa [Real.norm_eq_abs] using hRC o.2
  have hφs : @StronglyMeasurable (Observation A Z) ℝ inferInstance
      (covariateInformation A Z) (φ ∘ Prod.fst) :=
    (hφ.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hprod : Integrable ((R ∘ Prod.snd) * (φ ∘ Prod.fst)) (P : Measure (Observation A Z)) := by
    apply Integrable.of_bound ((hR.comp measurable_snd).mul (hφ.comp measurable_fst)).aestronglyMeasurable (C * B)
    apply Filter.Eventually.of_forall
    intro o
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hRC o.2) (hφB o.1) (abs_nonneg _) hC
  calc
    _ = ∫ o, ((P : Measure (Observation A Z))[R ∘ Prod.snd | covariateInformation A Z]) o * φ o.1
        ∂(P : Measure (Observation A Z)) :=
      RoughRegime.Conditional.integral_mul_condExp hm (R ∘ Prod.snd) (φ ∘ Prod.fst) hRi hφs hprod
    _ = ∫ o, cf o.1 * φ o.1 ∂(P : Measure (Observation A Z)) := by
      apply integral_congr_ae
      filter_upwards [hcond] with o ho
      simp only [Function.comp_apply] at ho
      rw [ho]
    _ = _ := marginal_integral A F P h (fun x => cf x * φ x) (hcf.mul hφ)

 theorem design_D_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (φ : Covariate A.d → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ x, |φ x| ≤ B) :
    (∫ o, F.D o.2 * φ o.1 ∂(P : Measure (Observation A Z))) =
      ∫ x, (h.w x * h.p x) * φ x ∂cubeVolume A.d := by
  rw [observable_weighted_integral A F P h F.D F.measurableD A.M0 A.hM0.le
    (fun z => by rw [abs_of_nonneg (F.boundD z).1]; exact (F.boundD z).2)
    h.w h.measurableW h.momentD φ hφ B hB hφB]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

 theorem design_U_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (φ : Covariate A.d → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ x, |φ x| ≤ B) :
    (∫ o, F.U o.2 * φ o.1 ∂(P : Measure (Observation A Z))) =
      ∫ x, h.a x * (h.w x * h.p x) * φ x ∂cubeVolume A.d := by
  rw [observable_weighted_integral A F P h F.U F.measurableU A.M0 A.hM0.le F.boundU
    (fun x => h.w x * h.a x) (h.measurableW.mul h.measurableA) h.momentU φ hφ B hB hφB]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

 theorem design_V_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (φ : Covariate A.d → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : 0 ≤ B) (hφB : ∀ x, |φ x| ≤ B) :
    (∫ o, F.V o.2 * φ o.1 ∂(P : Measure (Observation A Z))) =
      ∫ x, h.b x * (h.w x * h.p x) * φ x ∂cubeVolume A.d := by
  rw [observable_weighted_integral A F P h F.V F.measurableV A.M0 A.hM0.le F.boundV
    (fun x => h.w x * h.b x) (h.measurableW.mul h.measurableB) h.momentV φ hφ B hB hφB]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

 theorem design_cell_probability (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (C : Set (Covariate A.d)) (hC : MeasurableSet C) :
    (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' C) ≤
      (A.gplus / A.δ) * (cubeVolume A.d).real C := by
  let φ := C.indicator (fun _ : Covariate A.d => (1 : ℝ))
  have hφ : Measurable φ := measurable_const.indicator hC
  have he : (∫ o, φ o.1 ∂(P : Measure (Observation A Z))) =
      (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' C) := by
    change (∫ o, (Prod.fst ⁻¹' C).indicator (fun _ => (1 : ℝ)) o ∂(P : Measure (Observation A Z))) = _
    rw [integral_indicator (hC.preimage measurable_fst), setIntegral_const, smul_eq_mul, mul_one]
  rw [← he, marginal_integral A F P h φ hφ]
  have hp := covariate_density_bounds A F P h
  have hpi : Integrable (fun x => h.p x * φ x) (cubeVolume A.d) := by
    apply Integrable.of_bound (h.measurableP.mul hφ).aestronglyMeasurable (A.gplus / A.δ)
    filter_upwards [hp, h.nonnegativeP] with x hx hpx
    dsimp only [Pi.mul_apply]
    by_cases hxC : x ∈ C
    · simp only [φ, Set.indicator_of_mem hxC, mul_one, Real.norm_eq_abs, abs_of_nonneg hpx]
      exact hx.2
    · simp only [φ, Set.indicator_of_notMem hxC, mul_zero, norm_zero]
      exact div_nonneg (A.hgminus.trans A.hgplus).le A.hδ.le
  have hφi : Integrable φ (cubeVolume A.d) := (integrable_const (1 : ℝ)).indicator hC
  have hm := integral_mono_ae hpi (hφi.const_mul (A.gplus / A.δ))
    (hp.mono (fun x hx => by
      change h.p x * φ x ≤ (A.gplus / A.δ) * φ x
      apply mul_le_mul_of_nonneg_right hx.2
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x))
  rw [integral_const_mul] at hm
  have hi : (∫ x, φ x ∂cubeVolume A.d) = (cubeVolume A.d).real C := by
    dsimp only [φ]
    rw [integral_indicator hC, setIntegral_const, smul_eq_mul, mul_one]
  rwa [hi] at hm

end RoughRegime.Model
