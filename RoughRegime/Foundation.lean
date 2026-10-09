module

public import Mathlib


@[expose] public section
/-!
# Identities underlying the paper's generic functional

These results concern real functions and their actual Bochner integrals. They
do not assert the nonparametric minimax theorem. `mixed_bias` is the weighted
integral identity in Section 2; `projection_product_residual` is the abstract
Hilbert-space identity used by the projection construction in Section 4.
-/

noncomputable section

namespace RoughRegime.Foundation

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

def weightedTarget (μ : Measure X) (a b g : X → ℝ) : ℝ :=
  ∫ x, a x * b x * g x ∂μ

def augmentedTarget (μ : Measure X) (a b g ac bc : X → ℝ) : ℝ :=
  ∫ x, (a x * bc x + b x * ac x - ac x * bc x) * g x ∂μ

theorem mixed_bias_pointwise (a b g ac bc : ℝ) :
    (a * bc + b * ac - ac * bc) * g - a * b * g =
      -((ac - a) * (bc - b) * g) := by
  ring

/-- The mixed-bias identity, with the integrability conditions stated explicitly. -/
theorem mixed_bias (μ : Measure X) (a b g ac bc : X → ℝ)
    (ht : Integrable (fun x ↦ a x * b x * g x) μ)
    (hc : Integrable (fun x ↦ (a x * bc x + b x * ac x - ac x * bc x) * g x) μ) :
    augmentedTarget μ a b g ac bc - weightedTarget μ a b g =
      -(∫ x, (ac x - a x) * (bc x - b x) * g x ∂μ) := by
  unfold augmentedTarget weightedTarget
  rw [← integral_sub hc ht, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  exact mixed_bias_pointwise _ _ _ _ _

theorem double_robustness_left (μ : Measure X) (a b g ac bc : X → ℝ)
    (ht : Integrable (fun x ↦ a x * b x * g x) μ)
    (hc : Integrable (fun x ↦ (a x * bc x + b x * ac x - ac x * bc x) * g x) μ)
    (ha : ac =ᵐ[μ] a) :
    augmentedTarget μ a b g ac bc = weightedTarget μ a b g := by
  have hz : (∫ x, (ac x - a x) * (bc x - b x) * g x ∂μ) = 0 := by
    calc
      _ = ∫ x, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ha] with x hx
        simp [hx]
      _ = 0 := by simp
  have h := mixed_bias μ a b g ac bc ht hc
  rw [hz, neg_zero, sub_eq_zero] at h
  exact h

theorem double_robustness_right (μ : Measure X) (a b g ac bc : X → ℝ)
    (ht : Integrable (fun x ↦ a x * b x * g x) μ)
    (hc : Integrable (fun x ↦ (a x * bc x + b x * ac x - ac x * bc x) * g x) μ)
    (hb : bc =ᵐ[μ] b) :
    augmentedTarget μ a b g ac bc = weightedTarget μ a b g := by
  have hz : (∫ x, (ac x - a x) * (bc x - b x) * g x ∂μ) = 0 := by
    calc
      _ = ∫ x, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hb] with x hx
        simp [hx]
      _ = 0 := by simp
  have h := mixed_bias μ a b g ac bc ht hc
  rw [hz, neg_zero, sub_eq_zero] at h
  exact h

theorem generic_ratio_to_weighted_product (p w mU mV : ℝ) (hw : w ≠ 0) :
    p * (mU * mV / w) = (mU / w) * (mV / w) * (w * p) := by
  field_simp

/-- The model degenerates to an observable mean when `U = D`. -/
theorem degenerate_ratio (w mV : ℝ) (hw : w ≠ 0) : w * mV / w = mV := by
  field_simp

theorem ratio_baseline_decomposition (mU mV w a0 b0 : ℝ) (hw : w ≠ 0) :
    mU * mV / w = a0 * mV + b0 * mU - a0 * b0 * w +
      (mU - a0 * w) * (mV - b0 * w) / w := by
  field_simp
  ring

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Product projection bias retains both residuals. -/
theorem projection_product_residual (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (a b : E) :
    inner ℝ a b - inner ℝ (K.starProjection a) (K.starProjection b) =
      inner ℝ (a - K.starProjection a) (b - K.starProjection b) := by
  have ha := K.starProjection_inner_eq_zero a (K.starProjection b)
    (K.starProjection_apply_mem b)
  have hb := K.starProjection_inner_eq_zero b (K.starProjection a)
    (K.starProjection_apply_mem a)
  rw [inner_sub_left] at ha hb
  rw [← real_inner_comm b (K.starProjection a)] at hb
  rw [← real_inner_comm (K.starProjection b) (K.starProjection a)] at hb
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem projection_product_bias_bound (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (a b : E) :
    |inner ℝ a b - inner ℝ (K.starProjection a) (K.starProjection b)| ≤
      ‖a - K.starProjection a‖ * ‖b - K.starProjection b‖ := by
  rw [projection_product_residual]
  exact abs_real_inner_le_norm _ _

/-- Nested increments are the inner product of the two projection differences. -/
theorem nested_projection_increment (K L : Submodule ℝ E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K ≤ L) (a b : E) :
    inner ℝ (L.starProjection a) (L.starProjection b) -
      inner ℝ (K.starProjection a) (K.starProjection b) =
      inner ℝ (L.starProjection a - K.starProjection a)
        (L.starProjection b - K.starProjection b) := by
  have h1 := L.starProjection_inner_eq_zero a (K.starProjection b)
    (hKL (K.starProjection_apply_mem b))
  have h2 := K.starProjection_inner_eq_zero a (K.starProjection b)
    (K.starProjection_apply_mem b)
  have h3 := L.starProjection_inner_eq_zero b (K.starProjection a)
    (hKL (K.starProjection_apply_mem a))
  have h4 := K.starProjection_inner_eq_zero b (K.starProjection a)
    (K.starProjection_apply_mem a)
  simp only [inner_sub_left] at h1 h2 h3 h4
  rw [← real_inner_comm b (K.starProjection a)] at h3 h4
  rw [← real_inner_comm (L.starProjection b) (K.starProjection a)] at h3
  rw [← real_inner_comm (K.starProjection b) (K.starProjection a)] at h4
  simp only [inner_sub_left, inner_sub_right]
  linarith

end Projection

end RoughRegime.Foundation
