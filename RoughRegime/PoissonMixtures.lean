module

public import RoughRegime.PoissonMeasure
public import RoughRegime.GeneralTesting


@[expose] public section
/-! Actual arbitrary-measure mixtures of marked Poisson likelihoods. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace RoughRegime.PoissonMeasure

set_option backward.isDefEq.respectTransparency false

variable {W Y : Type*} [MeasurableSpace W] [MeasurableSpace Y]
variable (prior : Measure W) (μ : Measure Y) [IsProbabilityMeasure prior] [IsProbabilityMeasure μ]

omit [MeasurableSpace W] [MeasurableSpace Y] in
theorem tensor_nonneg (ψ : W → Y → ℝ) (hψ : ∀ w y, 0 ≤ ψ w y)
    (n : ℕ) (w : W) (xs : Fin n → Y) : 0 ≤ tensor ψ n w xs :=
  Finset.prod_nonneg fun i _ => hψ w (xs i)

theorem weighted_tensor_integrable (A : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C)
    (n : ℕ) (xs : Fin n → Y) : Integrable (fun w => A.density w * tensor ψ n w xs) prior := by
  apply bounded_integrable prior _
    (A.measurable.mul ((tensor_measurable ψ hψ n).comp (measurable_id.prodMk measurable_const)))
    (V * C ^ n)
  intro w
  change |A.density w * tensor ψ n w xs| ≤ V * C ^ n
  rw [abs_mul]
  exact mul_le_mul (hbA w) (tensor_bound ψ C hC hbψ n w xs) (abs_nonneg _) hV

def conditionalMixtureLaw (A : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C)
    (hψ0 : ∀ w y, 0 ≤ ψ w y) (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) (n : ℕ) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)) where
  density xs := ∫ w, A.density w * tensor ψ n w xs ∂prior
  measurable := by
    have hm := (A.measurable.comp measurable_fst).mul (tensor_measurable ψ hψ n)
    exact hm.stronglyMeasurable.integral_prod_left'.measurable
  integrable := by
    have hm := (A.measurable.comp measurable_fst).mul (tensor_measurable ψ hψ n)
    apply bounded_integrable (Measure.pi (fun _ : Fin n => μ)) _
      hm.stronglyMeasurable.integral_prod_left'.measurable (V * C ^ n)
    intro xs
    have hb : ∀ᵐ w ∂prior, ‖A.density w * tensor ψ n w xs‖ ≤ V * C ^ n :=
      Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbA w) (tensor_bound ψ C hC hbψ n w xs) (abs_nonneg _) hV
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hb
  nonneg := Filter.Eventually.of_forall fun xs => by
    apply integral_nonneg_of_ae
    filter_upwards [A.nonneg] with w hw
    exact mul_nonneg hw (tensor_nonneg ψ hψ0 n w xs)
  integral_one := by
    have hm : Measurable (fun q : (Fin n → Y) × W => A.density q.2 * tensor ψ n q.2 q.1) :=
      (A.measurable.comp measurable_snd).mul ((tensor_measurable ψ hψ n).comp measurable_swap)
    have hi : Integrable (fun q : (Fin n → Y) × W => A.density q.2 * tensor ψ n q.2 q.1)
        ((Measure.pi (fun _ : Fin n => μ)).prod prior) := by
      apply bounded_integrable _ _ hm (V * C ^ n)
      rintro ⟨xs, w⟩
      rw [abs_mul]
      exact mul_le_mul (hbA w) (tensor_bound ψ C hC hbψ n w xs) (abs_nonneg _) hV
    rw [integral_integral_swap hi]
    simp_rw [integral_const_mul, tensor,
      integral_fin_nat_prod_eq_prod (μ := fun _ : Fin n => μ), hmean]
    simpa using A.integral_one

theorem conditionalMixtureLaw_lower (A : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C)
    (hψ0 : ∀ w y, 0 ≤ ψ w y) (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1)
    (c : ℝ) (hc : 0 ≤ c) (hlow : ∀ w y, c ≤ ψ w y) (n : ℕ) (xs : Fin n → Y) :
    c ^ n ≤ (conditionalMixtureLaw prior μ A ψ hψ V C hV hC hbA hbψ hψ0 hmean n).density xs := by
  have ht (w : W) : c ^ n ≤ tensor ψ n w xs := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin n => c)
      (g := fun i => ψ w (xs i)) (fun _ _ => hc) (fun i _ => hlow w (xs i))
    simpa [tensor] using h
  have hm : (fun w => c ^ n * A.density w) ≤ᵐ[prior]
      fun w => A.density w * tensor ψ n w xs := by
    filter_upwards [A.nonneg] with w hw
    nlinarith [mul_le_mul_of_nonneg_left (ht w) hw]
  have hi := integral_mono_ae (A.integrable.const_mul (c ^ n))
    (weighted_tensor_integrable prior A ψ hψ V C hV hC hbA hbψ n xs) hm
  simpa [conditionalMixtureLaw, integral_const_mul, A.integral_one] using hi

theorem tensorMixture_measurable (v : W → ℝ) (ψ : W → Y → ℝ)
    (hv : Measurable v) (hψ : Measurable (Function.uncurry ψ)) (n : ℕ) :
    Measurable (tensorMixture prior v ψ n) := by
  have hm := (hv.comp measurable_fst).mul (tensor_measurable ψ hψ n)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

omit [MeasurableSpace Y] in
theorem tensorMixture_bound (v : W → ℝ) (ψ : W → Y → ℝ)
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C)
    (n : ℕ) (xs : Fin n → Y) : |tensorMixture prior v ψ n xs| ≤ V * C ^ n := by
  have hb : ∀ᵐ w ∂prior, ‖v w * tensor ψ n w xs‖ ≤ V * C ^ n :=
    Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbv w) (tensor_bound ψ C hC hbψ n w xs) (abs_nonneg _) hV
  simpa [Real.norm_eq_abs, tensorMixture] using norm_integral_le_of_norm_le_const hb

theorem tensorMixture_square_integrable (v : W → ℝ) (ψ : W → Y → ℝ)
    (hv : Measurable v) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C) (n : ℕ) :
    Integrable (fun xs : Fin n → Y => tensorMixture prior v ψ n xs ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) := by
  apply bounded_integrable _ _ ((tensorMixture_measurable prior v ψ hv hψ n).pow_const 2)
    ((V * C ^ n) ^ 2)
  intro xs
  rw [abs_pow]
  nlinarith [tensorMixture_bound prior v ψ V C hV hC hbv hbψ n xs, abs_nonneg
    (tensorMixture prior v ψ n xs), sq_abs (tensorMixture prior v ψ n xs)]

/-- Hellinger bound for genuine mixtures conditional on a Poisson count. -/
theorem conditionalMixture_hellinger_le (A B : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbB : ∀ w, |B.density w| ≤ V)
    (hbψ : ∀ w y, |ψ w y| ≤ C)
    (hψ0 : ∀ w y, 0 ≤ ψ w y) (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ w y, c ≤ ψ w y) (n : ℕ) :
    GeneralTesting.hellingerSquared
      (conditionalMixtureLaw prior μ A ψ hψ V C hV hC hbA hbψ hψ0 hmean n)
      (conditionalMixtureLaw prior μ B ψ hψ V C hV hC hbB hbψ hψ0 hmean n) ≤
      (1 / 4) * (c⁻¹) ^ n * tensorNormSquared prior μ
        (fun w => A.density w - B.density w) ψ n := by
  let LA := conditionalMixtureLaw prior μ A ψ hψ V C hV hC hbA hbψ hψ0 hmean n
  let LB := conditionalMixtureLaw prior μ B ψ hψ V C hV hC hbB hbψ hψ0 hmean n
  let v := fun w => A.density w - B.density w
  have hdiff (xs : Fin n → Y) : LA.density xs - LB.density xs = tensorMixture prior v ψ n xs := by
    change (∫ w, A.density w * tensor ψ n w xs ∂prior) -
      (∫ w, B.density w * tensor ψ n w xs ∂prior) = _
    rw [← integral_sub (weighted_tensor_integrable prior A ψ hψ V C hV hC hbA hbψ n xs)
      (weighted_tensor_integrable prior B ψ hψ V C hV hC hbB hbψ n xs)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => by dsimp [v, tensorMixture]; ring
  have hvb (w : W) : |v w| ≤ 2 * V := by
    have h : |A.density w - B.density w| ≤ |A.density w| + |B.density w| := by
      simpa using abs_sub_le (A.density w) 0 (B.density w)
    dsimp [v]
    linarith [hbA w, hbB w]
  have hpoint : ∀ᵐ xs ∂Measure.pi (fun _ : Fin n => μ),
      (Real.sqrt (LA.density xs) - Real.sqrt (LB.density xs)) ^ 2 ≤
        ((1 / 4) * (c⁻¹) ^ n) * tensorMixture prior v ψ n xs ^ 2 :=
    Filter.Eventually.of_forall fun xs => by
      have hla := conditionalMixtureLaw_lower prior μ A ψ hψ V C hV hC hbA hbψ hψ0 hmean
        c (le_of_lt hc) hlow n xs
      have hlb := conditionalMixtureLaw_lower prior μ B ψ hψ V C hV hC hbB hbψ hψ0 hmean
        c (le_of_lt hc) hlow n xs
      have h := Lower.square_root_difference_bound (pow_pos hc n) hla hlb
      rw [hdiff xs] at h
      have he : tensorMixture prior v ψ n xs ^ 2 / (4 * c ^ n) =
          ((1 / 4) * (c⁻¹) ^ n) * tensorMixture prior v ψ n xs ^ 2 := by
        rw [inv_pow]
        field_simp
      exact h.trans_eq he
  have hi := integral_mono_ae (GeneralTesting.hellinger_integrable LA LB)
    ((tensorMixture_square_integrable prior μ v ψ (A.measurable.sub B.measurable) hψ
      (2 * V) C (by positivity) hC hvb hbψ n).const_mul ((1 / 4) * (c⁻¹) ^ n)) hpoint
  simpa [GeneralTesting.hellingerSquared, tensorNormSquared, integral_const_mul,
    LA, LB, v] using hi

end RoughRegime.PoissonMeasure
