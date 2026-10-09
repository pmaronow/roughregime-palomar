module

public import Mathlib


@[expose] public section
/-! Cauchy coefficient and truncation bounds for genuine one-variable analytic series. -/
noncomputable section
open scoped BigOperators
open Set Metric
namespace RoughRegime.AnalyticCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Encode an ordinary Banach-valued coefficient sequence as a multilinear series. -/
def coefficientSeries (a : ℕ → E) : FormalMultilinearSeries ℂ ℂ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)

@[simp] theorem coefficientSeries_coeff (a : ℕ → E) (n : ℕ) :
    (coefficientSeries a).coeff n = a n := by
  simp [coefficientSeries, FormalMultilinearSeries.coeff, ContinuousMultilinearMap.mkPiRing_apply]

@[simp] theorem coefficientSeries_norm (a : ℕ → E) (n : ℕ) :
    ‖coefficientSeries a n‖ = ‖a n‖ := ContinuousMultilinearMap.norm_mkPiRing ..

/-- Geometric coefficient growth gives a positive radius, even when the ratio is larger than one. -/
theorem coefficientSeries_radius_pos (a : ℕ → E) (A Λ : ℝ) (hA : 0 ≤ A) (hΛ : 0 ≤ Λ)
    (hcoeff : ∀ n, ‖a n‖ ≤ A * Λ ^ n) : 0 < (coefficientSeries a).radius := by
  let r : NNReal := ⟨(Λ + 1)⁻¹, by positivity⟩
  have hr : 0 < r := by
    apply NNReal.coe_pos.mp
    change 0 < (Λ + 1)⁻¹
    exact inv_pos.mpr (by linarith)
  apply (ENNReal.coe_pos.mpr hr).trans_le
  apply (coefficientSeries a).le_radius_of_bound A
  intro n
  rw [coefficientSeries_norm]
  have hq : Λ * (r : ℝ) ≤ 1 := by
    dsimp [r]
    exact (mul_inv_le_iff₀ (by positivity : 0 < Λ + 1)).mpr (by linarith)
  calc
    ‖a n‖ * (r : ℝ) ^ n ≤ (A * Λ ^ n) * (r : ℝ) ^ n := by gcongr; exact hcoeff n
    _ = A * (Λ * (r : ℝ)) ^ n := by rw [mul_pow]; ring
    _ ≤ A := by
      simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left
        (pow_le_one₀ (by positivity : 0 ≤ Λ * (r : ℝ)) hq) hA

/-- Cauchy bound for the actual coefficients of a locally represented analytic function. -/
theorem coefficient_norm_le [CompleteSpace E] (f : ℂ → E) (a : ℕ → E)
    (ha : HasFPowerSeriesAt f (coefficientSeries a) 0)
    (r B : ℝ) (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall 0 r))
    (hbound : ∀ z ∈ sphere 0 r, ‖f z‖ ≤ B) (n : ℕ) :
    ‖a n‖ ≤ B * r⁻¹ ^ n := by
  let rN : NNReal := ⟨r, hr.le⟩
  have hp := hf.hasFPowerSeriesOnBall (R := rN) (by exact hr)
  have he : coefficientSeries a = cauchyPowerSeries f 0 r :=
    ha.eq_formalMultilinearSeries hp.hasFPowerSeriesAt
  have hc : Continuous (fun θ : ℝ => f (circleMap 0 r θ)) := by
    exact hf.continuousOn.comp_continuous (continuous_circleMap 0 r) (fun θ =>
      sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ))
  have hi : (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖) ≤ 2 * Real.pi * B := by
    have h := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hc.norm.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      ((continuous_const : Continuous (fun _ : ℝ => B)).intervalIntegrable (μ := MeasureTheory.volume) _ _)
      (fun θ _ => hbound _ (circleMap_mem_sphere 0 hr.le θ))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h
  rw [← coefficientSeries_norm, he]
  apply (norm_cauchyPowerSeries_le f 0 r n).trans
  rw [abs_of_pos hr]
  have havg : (2 * Real.pi)⁻¹ * (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖) ≤ B := by
    have h := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul] using h
  exact mul_le_mul_of_nonneg_right havg (by positivity)

omit [NormedSpace ℂ E] in
/-- Every combined-index truncation is bounded by the same geometric-series constant. -/
theorem partial_sum_norm_le (a : ℕ → E) (B q : ℝ) (_hB : 0 ≤ B) (hq : 0 ≤ q)
    (hq1 : q < 1) (hcoeff : ∀ n, ‖a n‖ ≤ B * q ^ n) (m : ℕ) :
    ‖∑ n ∈ Finset.range (m + 1), a n‖ ≤ B * (1 - q)⁻¹ := by
  have hs := (summable_geometric_of_lt_one hq hq1).mul_left B
  have hn : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hcoeff hs
  calc
    _ ≤ ∑ n ∈ Finset.range (m + 1), ‖a n‖ := norm_sum_le _ _
    _ ≤ ∑' n, ‖a n‖ := hn.sum_le_tsum _ (fun n _ => norm_nonneg _)
    _ ≤ ∑' n, B * q ^ n := hn.tsum_le_tsum hcoeff hs
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]

end RoughRegime.AnalyticCoefficients
