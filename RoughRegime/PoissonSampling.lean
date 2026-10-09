module

public import RoughRegime.SamplingDecay


@[expose] public section
/-! Exact scaled and modulated Poisson sampling for a continuous, quadratically
    decaying function whose Fourier transform has compact support. -/

noncomputable section

open MeasureTheory Filter Asymptotics
open scoped FourierTransform

namespace RoughRegime.LatticeFourier

/-- The Fourier transform convention is `exp (-2 * pi * i * x * t)`. -/
theorem fourier_scaled_modulated (f : ℝ → ℂ) (h w t : ℝ) (hh : 0 < h) :
    𝓕 (fun x : ℝ => f (h * x) * Complex.exp ((w * h * x : ℝ) * Complex.I)) t =
      (h : ℂ)⁻¹ * 𝓕 f (t / h - w / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have hphase (x : ℝ) :
      (-2 * Real.pi * x * t : ℝ) + w * h * x =
        -2 * Real.pi * (h * x) * (t / h - w / (2 * Real.pi)) := by
    field_simp
    ring
  have hint : (fun x : ℝ =>
      Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) •
        (f (h * x) * Complex.exp ((w * h * x : ℝ) * Complex.I))) =
      (fun x : ℝ => Complex.exp
        ((-2 * Real.pi * (h * x) * (t / h - w / (2 * Real.pi)) : ℝ) * Complex.I) *
          f (h * x)) := by
    funext x
    simp only [smul_eq_mul]
    calc
      Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) *
          (f (h * x) * Complex.exp ((w * h * x : ℝ) * Complex.I)) =
        (Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) *
          Complex.exp ((w * h * x : ℝ) * Complex.I)) * f (h * x) := by ring
      _ = _ := by
        rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, hphase]
  rw [hint, Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp
      ((-2 * Real.pi * y * (t / h - w / (2 * Real.pi)) : ℝ) * Complex.I) * f y) h]
  simp only [abs_of_pos (inv_pos.mpr hh), Complex.real_smul, Complex.ofReal_inv,
    smul_eq_mul]

/-- Compact Fourier support is preserved by scaling and frequency modulation. -/
theorem fourier_scaled_modulated_hasCompactSupport (f : ℝ → ℂ) (h w : ℝ)
    (hh : 0 < h) (hF : HasCompactSupport (𝓕 f)) :
    HasCompactSupport (𝓕 (fun x : ℝ =>
      f (h * x) * Complex.exp ((w * h * x : ℝ) * Complex.I))) := by
  let φ : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ h⁻¹ (inv_ne_zero hh.ne')).trans
    (Homeomorph.addRight (-w / (2 * Real.pi)))
  have heq (t : ℝ) : φ t = t / h - w / (2 * Real.pi) := by
    change h⁻¹ * t + (-w / (2 * Real.pi)) = t / h - w / (2 * Real.pi)
    simp only [div_eq_mul_inv]
    ring
  have hc : HasCompactSupport (fun t : ℝ =>
      (h : ℂ)⁻¹ * 𝓕 f (t / h - w / (2 * Real.pi))) := by
    have hs := (hF.comp_homeomorph φ).mul_left
      (f := fun _ : ℝ => (h : ℂ)⁻¹)
    change HasCompactSupport (fun t : ℝ => (h : ℂ)⁻¹ * 𝓕 f (φ t)) at hs
    simpa only [heq] using hs
  convert hc using 1
  funext t
  exact fourier_scaled_modulated f h w t hh

/-- The sample identity with an explicit decay bound for the modulated rescaling. -/
theorem poisson_sampling_of_modulated_decay (f : ℝ → ℂ) (h w : ℝ)
    (hh : 0 < h) (hc : Continuous f)
    (hg : IsBigO (cocompact ℝ)
      (fun x : ℝ => f (h * x) * Complex.exp ((w * h * x : ℝ) * Complex.I))
      (fun x : ℝ => |x| ^ (-(2 : ℝ))))
    (hF : IsBigO (cocompact ℝ)
      (𝓕 (fun x : ℝ => f (h * x) * Complex.exp ((w * h * x : ℝ) * Complex.I)))
      (fun x : ℝ => |x| ^ (-(2 : ℝ)))) :
    (h : ℂ) * (∑' z : ℤ,
      f (h * z) * Complex.exp ((w * h * z : ℝ) * Complex.I)) =
      ∑' l : ℤ, 𝓕 f ((l : ℝ) / h - w / (2 * Real.pi)) := by
  have hcont : Continuous (fun x : ℝ =>
      f (h * x) * Complex.exp ((w * h * x : ℝ) * Complex.I)) := by
    apply (hc.comp (continuous_const.mul continuous_id)).mul
    fun_prop
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay hcont one_lt_two hg hF 0
  simp only [zero_add, AddCircle.coe_zero, fourier_apply, zsmul_zero,
    AddCircle.toCircle_zero, Circle.coe_one, mul_one] at hp
  simp_rw [fourier_scaled_modulated f h w _ hh] at hp
  rw [tsum_mul_left] at hp
  rw [hp]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hh.ne'), one_mul]

/-- Exact Poisson sampling for any positive spacing and real modulation,
    from continuous quadratic decay and compact Fourier support. -/
theorem poisson_sampling (f : ℝ → ℂ) (h w : ℝ)
    (hh : 0 < h) (hc : Continuous f)
    (hf : IsBigO (cocompact ℝ) f (fun x : ℝ => |x| ^ (-(2 : ℝ))))
    (hF : HasCompactSupport (𝓕 f)) :
    (h : ℂ) * (∑' z : ℤ,
      f (h * z) * Complex.exp ((w * h * z : ℝ) * Complex.I)) =
      ∑' l : ℤ, 𝓕 f ((l : ℝ) / h - w / (2 * Real.pi)) := by
  apply poisson_sampling_of_modulated_decay f h w hh hc
  · exact isBigO_mul_bounded (cocompact ℝ)
      (fun x : ℝ => f (h * x))
      (fun x : ℝ => Complex.exp ((w * h * x : ℝ) * Complex.I))
      (fun x : ℝ => |x| ^ (-(2 : ℝ)))
      (isBigO_quadratic_rescale hf hh.ne')
      (fun x => (Complex.norm_exp_ofReal_mul_I (w * h * x)).le)
  · exact hasCompactSupport_isBigO
      (fourier_scaled_modulated_hasCompactSupport f h w hh hF) _

/-- Both sides of the sample identity are genuine convergent series. -/
theorem poisson_sampling_summable (f : ℝ → ℂ) (h w : ℝ)
    (hh : 0 < h)
    (hf : IsBigO (cocompact ℝ) f (fun x : ℝ => |x| ^ (-(2 : ℝ))))
    (hF : HasCompactSupport (𝓕 f)) :
    Summable (fun z : ℤ => f (h * z) *
      Complex.exp ((w * h * z : ℝ) * Complex.I)) ∧
    Summable (fun l : ℤ => 𝓕 f ((l : ℝ) / h - w / (2 * Real.pi))) := by
  constructor
  · have hg := isBigO_mul_bounded (cocompact ℝ)
      (fun x : ℝ => f (h * x))
      (fun x : ℝ => Complex.exp ((w * h * x : ℝ) * Complex.I))
      (fun x : ℝ => |x| ^ (-(2 : ℝ)))
      (isBigO_quadratic_rescale hf hh.ne')
      (fun x => (Complex.norm_exp_ofReal_mul_I (w * h * x)).le)
    exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hg.comp_tendsto Int.tendsto_coe_cofinite)
  · let φ : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ h⁻¹ (inv_ne_zero hh.ne')).trans
      (Homeomorph.addRight (-w / (2 * Real.pi)))
    have heq (t : ℝ) : φ t = t / h - w / (2 * Real.pi) := by
      change h⁻¹ * t + (-w / (2 * Real.pi)) = t / h - w / (2 * Real.pi)
      simp only [div_eq_mul_inv]
      ring
    have hdec := hasCompactSupport_isBigO (hF.comp_homeomorph φ)
      (fun x : ℝ => |x| ^ (-(2 : ℝ)))
    have hs := summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hdec.comp_tendsto Int.tendsto_coe_cofinite)
    change Summable (fun l : ℤ => 𝓕 f (φ (l : ℝ))) at hs
    simpa only [heq] using hs

end RoughRegime.LatticeFourier
