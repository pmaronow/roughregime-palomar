module

public import Mathlib


@[expose] public section
/-! A genuine first-order Taylor remainder from a bounded second Fréchet derivative. -/
noncomputable section
open Set Metric
namespace RoughRegime.SecondOrderRemainder

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- On a ball, a bound for the actual second derivative gives a quadratic first
Taylor remainder. The result applies to vector-valued derivatives as well. -/
theorem first_order_remainder (f : E → G) (r C : ℝ) (hr : 0 < r)
    (hf : ∀ y ∈ ball (0 : E) r, DifferentiableAt ℝ f y)
    (hdf : ∀ y ∈ ball (0 : E) r, DifferentiableAt ℝ (fderiv ℝ f) y)
    (hD : ∀ y ∈ ball (0 : E) r, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C)
    (x : E) (hx : ‖x‖ < r) :
    ‖f x - f 0 - (fderiv ℝ f 0) x‖ ≤ C * ‖x‖ ^ 2 := by
  have hzero : (0 : E) ∈ ball 0 r := by simpa using hr
  have hC : 0 ≤ C := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hD 0 hzero)
  have hgrad (y : E) (hy : y ∈ ball 0 r) :
      ‖fderiv ℝ f y - fderiv ℝ f 0‖ ≤ C * ‖y‖ := by
    simpa using (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le hdf hD hzero hy
  let B : Set E := closedBall 0 ‖x‖
  have hsub : B ⊆ ball 0 r := by
    intro y hy
    have hn : ‖y‖ ≤ ‖x‖ := by simpa [B] using hy
    simpa using hn.trans_lt hx
  let H : E → G := fun y => f y - f 0 - (fderiv ℝ f 0) y
  have hH (y : E) (hy : y ∈ B) :
      HasFDerivAt H (fderiv ℝ f y - fderiv ℝ f 0) y := by
    exact ((hf y (hsub hy)).hasFDerivAt.sub_const (f 0)).sub
      (fderiv ℝ f 0).hasFDerivAt
  have hb (y : E) (hy : y ∈ B) : ‖fderiv ℝ f y - fderiv ℝ f 0‖ ≤ C * ‖x‖ := by
    apply (hgrad y (hsub hy)).trans
    exact mul_le_mul_of_nonneg_left (by simpa [B] using hy) hC
  have he := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy => (hH y hy).hasFDerivWithinAt) hb
    (show (0 : E) ∈ B by simp [B]) (show x ∈ B by simp [B])
  simpa [H, sub_zero, pow_two, mul_assoc] using he

end RoughRegime.SecondOrderRemainder
