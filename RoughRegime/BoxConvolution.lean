module

public import RoughRegime.BoxKernel
public import Mathlib.Analysis.Convolution
public import Mathlib


@[expose] public section
namespace RoughRegime.LatticeFourier

open MeasureTheory Set
open scoped Convolution

/-- The normalized triangular density obtained from two centered uniform boxes. -/
noncomputable def triangleKernel (a : ℝ) (x : ℝ) : ℂ :=
  ((max (2 * a - |x|) 0 * ((2 * a)⁻¹) ^ 2 : ℝ) : ℂ)

private theorem interval_overlap_length (a x : ℝ) :
    min a (x + a) - max (-a) (x - a) = 2 * a - |x| := by
  by_cases hx : 0 ≤ x
  · rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos hx']
    ring

/-- The convolution of two normalized interval indicators is the triangular density. -/
theorem boxKernel_convolution_eq_triangleKernel (a : ℝ) :
    MeasureTheory.convolution (boxKernel a) (boxKernel a)
      (ContinuousLinearMap.mul ℂ ℂ) volume = triangleKernel a := by
  funext x
  have hi : (fun t : ℝ => boxKernel a t * boxKernel a (x - t)) =
      (Icc (max (-a) (x - a)) (min a (x + a))).indicator
        (fun _ : ℝ => (((2 * a)⁻¹ : ℝ) : ℂ) * (((2 * a)⁻¹ : ℝ) : ℂ)) := by
    funext t
    have he : x - t ∈ Icc (-a) a ↔ t ∈ Icc (x - a) (x + a) := by
      simp only [mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have hb : boxKernel a (x - t) =
        (Icc (x - a) (x + a)).indicator
          (fun _ : ℝ => (((2 * a)⁻¹ : ℝ) : ℂ)) t := by
      simp only [boxKernel, indicator, he]
    rw [hb]
    simp only [boxKernel]
    rw [← inter_indicator_mul, Icc_inter_Icc]
  change (∫ t : ℝ, boxKernel a t * boxKernel a (x - t)) = triangleKernel a x
  rw [hi, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc, interval_overlap_length]
  simp only [triangleKernel, Complex.real_smul, ← Complex.ofReal_mul, pow_two]

/-- The triangular convolution kernel is continuous. -/
theorem triangleKernel_continuous (a : ℝ) : Continuous (triangleKernel a) := by
  unfold triangleKernel
  fun_prop

/-- The triangular kernel vanishes beyond twice the box radius. -/
theorem triangleKernel_eq_zero_of_two_mul_lt_abs (a x : ℝ) (hx : 2 * a < |x|) :
    triangleKernel a x = 0 := by
  simp [triangleKernel, max_eq_right (by linarith : 2 * a - |x| ≤ 0)]

theorem triangleKernel_support_subset (a : ℝ) :
    Function.support (triangleKernel a) ⊆ Icc (-2 * a) (2 * a) := by
  intro x hx
  by_contra hn
  apply hx
  apply triangleKernel_eq_zero_of_two_mul_lt_abs
  simp only [mem_Icc, not_and_or, not_le] at hn
  rcases hn with hn | hn
  · have habs := neg_le_abs x
    linarith
  · exact hn.trans_le (le_abs_self x)

theorem triangleKernel_hasCompactSupport (a : ℝ) : HasCompactSupport (triangleKernel a) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (triangleKernel_support_subset a)

theorem triangleKernel_integrable (a : ℝ) : Integrable (triangleKernel a) :=
  (triangleKernel_continuous a).integrable_of_hasCompactSupport (triangleKernel_hasCompactSupport a)

theorem boxKernel_convolution_continuous (a : ℝ) :
    Continuous (MeasureTheory.convolution (boxKernel a) (boxKernel a)
      (ContinuousLinearMap.mul ℂ ℂ) volume) := by
  rw [boxKernel_convolution_eq_triangleKernel]
  exact triangleKernel_continuous a

theorem boxKernel_convolution_hasCompactSupport (a : ℝ) :
    HasCompactSupport (MeasureTheory.convolution (boxKernel a) (boxKernel a)
      (ContinuousLinearMap.mul ℂ ℂ) volume) := by
  rw [boxKernel_convolution_eq_triangleKernel]
  exact triangleKernel_hasCompactSupport a

theorem boxKernel_convolution_integrable (a : ℝ) :
    Integrable (MeasureTheory.convolution (boxKernel a) (boxKernel a)
      (ContinuousLinearMap.mul ℂ ℂ) volume) := by
  rw [boxKernel_convolution_eq_triangleKernel]
  exact triangleKernel_integrable a

end RoughRegime.LatticeFourier
