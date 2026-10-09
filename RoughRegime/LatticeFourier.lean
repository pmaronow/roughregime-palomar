module

public import RoughRegime.Lattice
public import RoughRegime.BoxKernel
public import RoughRegime.BoxConvolution
public import RoughRegime.TrianglePowers
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


@[expose] public section
namespace RoughRegime.LatticeFourier

open MeasureTheory Set Real Complex Filter Asymptotics
open scoped FourierTransform Convolution

theorem integral_scaled_exp (a t : ℝ) :
    (∫ x in -a..a, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) =
      ((2 * a * Real.sinc (t * a) : ℝ) : ℂ) := by
  by_cases ht : t = 0
  · simp [ht]
    ring
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) (a := -a) (b := a) ht
  rw [mul_neg, integral_exp_mul_I_eq_sinc] at h
  convert h using 1
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr ht]

theorem boxKernel_fourier (a : ℝ) (ha : 0 < a) (w : ℝ) :
    𝓕 (boxKernel a) w = ((Real.sinc (2 * Real.pi * a * w) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold boxKernel
  simp only [smul_eq_mul]
  have hi : (fun v : ℝ => Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I) *
      (Icc (-a) a).indicator (fun _ : ℝ => (((2 * a)⁻¹ : ℝ) : ℂ)) v) =
      (Icc (-a) a).indicator (fun v : ℝ =>
        Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I) * (((2 * a)⁻¹ : ℝ) : ℂ)) := by
    ext v
    by_cases hv : v ∈ Icc (-a) a <;> simp [hv]
  rw [hi]
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    intervalIntegral.integral_mul_const]
  have h : (fun v : ℝ => Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I)) =
      (fun v : ℝ => Complex.exp ((((-2 * Real.pi * w) * v : ℝ) : ℂ) * Complex.I)) := by
    ext v
    congr 1
    push_cast
    ring
  rw [h, integral_scaled_exp]
  have harg : -2 * Real.pi * w * a = -(2 * Real.pi * a * w) := by ring
  rw [harg, Real.sinc_neg]
  push_cast
  field_simp [ha.ne']

theorem triangleKernel_fourier (a : ℝ) (ha : 0 < a) (w : ℝ) :
    𝓕 (triangleKernel a) w = ((Real.sinc (2 * Real.pi * a * w) ^ 2 : ℝ) : ℂ) := by
  rw [← boxKernel_convolution_eq_triangleKernel]
  rw [Real.fourier_mul_convolution_eq (boxKernel_integrable a) (boxKernel_integrable a),
    boxKernel_fourier a ha, ← pow_two, ← Complex.ofReal_pow]

theorem trianglePower_fourier (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℝ) :
    𝓕 (trianglePower a n) w =
      ((Real.sinc (2 * Real.pi * a * w) ^ (2 * (n + 1)) : ℝ) : ℂ) := by
  induction n with
  | zero => simpa using triangleKernel_fourier a ha w
  | succ n ih =>
    rw [trianglePower_succ, Real.fourier_mul_convolution_eq
      (triangleKernel_integrable a) (trianglePower_integrable a n),
      triangleKernel_fourier a ha w, ih]
    push_cast
    rw [← pow_add]
    congr 1
    omega

end RoughRegime.LatticeFourier
