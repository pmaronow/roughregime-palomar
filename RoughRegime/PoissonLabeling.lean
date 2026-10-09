module

public import RoughRegime.PoissonProcess


@[expose] public section
/-! Labeling expansion and its L² estimate for arbitrary prior/mark spaces. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RoughRegime.PoissonMeasure

set_option backward.isDefEq.respectTransparency false

variable {W Y : Type*} [MeasurableSpace W] [MeasurableSpace Y]
variable (prior : Measure W) (μ : Measure Y) [IsProbabilityMeasure prior] [IsProbabilityMeasure μ]

def labeledTensor (e : Fin 3 → W → Y → ℝ) (k : ℕ) (labels : Fin k → Fin 3)
    (w : W) (xs : Fin k → Y) : ℝ := ∏ i, e (labels i) w (xs i)

def labeledMixture (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (k : ℕ) (labels : Fin k → Fin 3) (xs : Fin k → Y) : ℝ :=
  ∫ w, v w * labeledTensor e k labels w xs ∂prior

def labeledNormSquared (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (k : ℕ) (labels : Fin k → Fin 3) : ℝ :=
  ∫ xs : Fin k → Y, labeledMixture prior v e k labels xs ^ 2 ∂Measure.pi (fun _ => μ)

theorem labeledTensor_measurable (e : Fin 3 → W → Y → ℝ)
    (he : ∀ l, Measurable (Function.uncurry (e l))) (k : ℕ) (labels : Fin k → Fin 3) :
    Measurable (Function.uncurry (labeledTensor e k labels)) := by
  unfold labeledTensor Function.uncurry
  apply Finset.measurable_prod
  intro i _
  exact (he (labels i)).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

omit [MeasurableSpace W] [MeasurableSpace Y] in
theorem labeledTensor_bound (e : Fin 3 → W → Y → ℝ) (C : ℝ)
    (he : ∀ l w y, |e l w y| ≤ C) (k : ℕ) (labels : Fin k → Fin 3) (w : W) (xs : Fin k → Y) :
    |labeledTensor e k labels w xs| ≤ C ^ k := by
  unfold labeledTensor
  rw [Finset.abs_prod]
  have h := Finset.prod_le_prod₀ (s := Finset.univ)
    (f := fun i : Fin k => |e (labels i) w (xs i)|) (g := fun _ => C)
    (fun _ _ => abs_nonneg _) (fun i _ => he (labels i) w (xs i))
  simpa using h

theorem labeled_integrable (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (hv : Measurable v) (he : ∀ l, Measurable (Function.uncurry (e l)))
    (V C : ℝ) (hV : 0 ≤ V) (hbv : ∀ w, |v w| ≤ V) (hbe : ∀ l w y, |e l w y| ≤ C)
    (k : ℕ) (labels : Fin k → Fin 3) (xs : Fin k → Y) :
    Integrable (fun w => v w * labeledTensor e k labels w xs) prior := by
  apply bounded_integrable prior _ (hv.mul ((labeledTensor_measurable e he k labels).comp
    (measurable_id.prodMk measurable_const))) (V * C ^ k)
  intro w
  change |v w * labeledTensor e k labels w xs| ≤ V * C ^ k
  rw [abs_mul]
  exact mul_le_mul (hbv w) (labeledTensor_bound e C hbe k labels w xs) (abs_nonneg _) hV

/-- Exact expansion of the mixture tensor over the `3^k` source labelings. -/
theorem tensorMixture_labelings (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (hv : Measurable v) (he : ∀ l, Measurable (Function.uncurry (e l)))
    (V C : ℝ) (hV : 0 ≤ V) (hbv : ∀ w, |v w| ≤ V) (hbe : ∀ l w y, |e l w y| ≤ C)
    (k : ℕ) (xs : Fin k → Y) :
    tensorMixture prior v (fun w y => ∑ l : Fin 3, e l w y) k xs =
      ∑ labels : Fin k → Fin 3, labeledMixture prior v e k labels xs := by
  have hex (w : W) : v w * tensor (fun w y => ∑ l : Fin 3, e l w y) k w xs =
      ∑ labels : Fin k → Fin 3, v w * labeledTensor e k labels w xs := by
    unfold tensor labeledTensor
    rw [Fintype.prod_sum]
    rw [Finset.mul_sum]
  unfold tensorMixture labeledMixture
  simp_rw [hex]
  rw [integral_finsetSum]
  intro labels _
  exact labeled_integrable prior v e hv he V C hV hbv hbe k labels xs

theorem labeledMixture_square_integrable (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (hv : Measurable v) (he : ∀ l, Measurable (Function.uncurry (e l)))
    (V C : ℝ) (hV : 0 ≤ V) (hbv : ∀ w, |v w| ≤ V) (hbe : ∀ l w y, |e l w y| ≤ C)
    (k : ℕ) (labels : Fin k → Fin 3) :
    Integrable (fun xs : Fin k → Y => labeledMixture prior v e k labels xs ^ 2)
      (Measure.pi (fun _ : Fin k => μ)) := by
  have hm : Measurable (labeledMixture prior v e k labels) :=
    ((hv.comp measurable_fst).mul (labeledTensor_measurable e he k labels)).stronglyMeasurable.integral_prod_left'.measurable
  apply bounded_integrable _ _ (hm.pow_const 2) ((V * C ^ k) ^ 2)
  intro xs
  have hb : |labeledMixture prior v e k labels xs| ≤ V * C ^ k := by
    have h := norm_integral_le_of_norm_le_const (μ := prior)
      (f := fun w => v w * labeledTensor e k labels w xs)
      (C := V * C ^ k) (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbv w) (labeledTensor_bound e C hbe k labels w xs) (abs_nonneg _) hV)
    simpa [Real.norm_eq_abs, labeledMixture] using h
  rw [abs_pow]
  nlinarith [abs_nonneg (labeledMixture prior v e k labels xs), sq_abs
    (labeledMixture prior v e k labels xs)]

/-- The exact general-measure `3^k` Cauchy--Schwarz estimate used in (5.9). -/
theorem tensorNormSquared_labelings_le (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (hv : Measurable v) (he : ∀ l, Measurable (Function.uncurry (e l)))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbe : ∀ l w y, |e l w y| ≤ C) (k : ℕ) :
    tensorNormSquared prior μ v (fun w y => ∑ l : Fin 3, e l w y) k ≤
      (3 : ℝ) ^ k * ∑ labels : Fin k → Fin 3, labeledNormSquared prior μ v e k labels := by
  have hm : Measurable (Function.uncurry (fun w y => ∑ l : Fin 3, e l w y)) :=
    Finset.measurable_sum _ fun l _ => he l
  have hsum (w : W) (y : Y) : |∑ l : Fin 3, e l w y| ≤ 3 * C := by
    calc
      _ ≤ ∑ l : Fin 3, |e l w y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, C := Finset.sum_le_sum fun l _ => hbe l w y
      _ = 3 * C := by simp
  have hpoint : ∀ᵐ xs ∂Measure.pi (fun _ : Fin k => μ),
      tensorMixture prior v (fun w y => ∑ l : Fin 3, e l w y) k xs ^ 2 ≤
        (3 : ℝ) ^ k * ∑ labels : Fin k → Fin 3, labeledMixture prior v e k labels xs ^ 2 :=
    Filter.Eventually.of_forall fun xs => by
      rw [tensorMixture_labelings prior v e hv he V C hV hbv hbe k xs]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun labels : Fin k → Fin 3 => labeledMixture prior v e k labels xs)
      simpa using h
  have hir : Integrable (fun xs : Fin k → Y =>
      ∑ labels : Fin k → Fin 3, labeledMixture prior v e k labels xs ^ 2)
      (Measure.pi (fun _ : Fin k => μ)) := by
    apply integrable_finsetSum
    intro labels _
    exact labeledMixture_square_integrable prior μ v e hv he V C hV hbv hbe k labels
  have h := integral_mono_ae (tensorMixture_square_integrable prior μ v _ hv hm V (3 * C)
    hV (by positivity) hbv hsum k) (hir.const_mul ((3 : ℝ) ^ k)) hpoint
  rw [integral_const_mul, integral_finsetSum] at h
  · exact h
  · intro labels _
    exact labeledMixture_square_integrable prior μ v e hv he V C hV hbv hbe k labels

end RoughRegime.PoissonMeasure
