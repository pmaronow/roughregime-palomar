module

public import RoughRegime.ReductionAmplitudes


@[expose] public section
/-! Numerical separation-error and prior concentration scales in Proposition 12. -/
noncomputable section
open Filter

namespace RoughRegime.ReductionScales

lemma frequency_div_log_tendsto_zero (θ τ : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => frequency n θ τ / Real.log n) atTop (nhds 0) := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hlim := (frequency_sq_log_tendsto θ τ hθ hθhalf hτ).mul (tendsto_inv_atTop_zero.comp hM)
  simp only [mul_zero] at hlim
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [hM.eventually_ge_atTop 1] with n hn
  have hM0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
  simp only [Function.comp_apply]
  field_simp

lemma frequency_exponential_linear_loss_tendsto_zero (θ τ a C : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (ha : 0 < a) :
    Tendsto (fun n : ℝ => n ^ (-a) * Real.exp (C * frequency n θ τ)) atTop (nhds 0) := by
  have hratio := ((frequency_div_log_tendsto_zero θ τ hθ hθhalf hτ).const_mul C).sub_const a
  simp only [mul_zero, zero_sub] at hratio
  have hprod := hratio.neg_mul_atTop (neg_neg_of_pos ha) Real.tendsto_log_atTop
  have hbot : Tendsto (fun n : ℝ => -a * Real.log n + C * frequency n θ τ) atTop atBot := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    have hL0 : Real.log n ≠ 0 := (Real.log_pos hn).ne'
    field_simp
    ring
  have he := Real.tendsto_exp_atBot.comp hbot
  apply Filter.Tendsto.congr' _ he
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [Function.comp_apply, Real.exp_add, Real.rpow_def_of_pos hn]
  congr 1
  congr 1
  ring

lemma sqrt_log_div_log_tendsto_zero :
    Tendsto (fun n : ℝ => Real.sqrt (Real.log n) / Real.log n) atTop (nhds 0) := by
  have hlim := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  have hLp : 0 < Real.log n := Real.log_pos hn
  have hsp : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hLp
  have hs := Real.sq_sqrt hLp.le
  simp only [Function.comp_apply]
  field_simp
  nlinarith

/-- The squared target scale multiplied by `n` diverges. Hence prior variance
`O(1/B)` is negligible because the constructed blocks have `B≥n`. -/
theorem subcritical_testing_scale_tendsto (θ τ : ℝ) (hθhalf : θ < 1 / 2) :
    Tendsto (fun n : ℝ => n * RoughRegime.Rates.subcriticalScale n θ τ ^ 2) atTop atTop := by
  have hlogLog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hsqrt := sqrt_log_div_log_tendsto_zero
  have hratio := ((hlogLog.const_mul θ).sub (hsqrt.const_mul (2 * RoughRegime.Rates.kappa θ τ))).add_const (1 - 2 * θ)
  norm_num only [mul_zero, sub_self, zero_add] at hratio
  have hprod := hratio.pos_mul_atTop (by linarith : 0 < 1 - 2 * θ) Real.tendsto_log_atTop
  have he := Real.tendsto_exp_atTop.comp hprod
  apply Filter.Tendsto.congr' _ he
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  have hnp : 0 < n := zero_lt_one.trans hn
  have hLp : 0 < Real.log n := Real.log_pos hn
  have hL0 := hLp.ne'
  have hscale := RoughRegime.Rates.log_scale n θ τ hn
  have hprodEq : (θ * (Real.log (Real.log n) / Real.log n) -
      2 * RoughRegime.Rates.kappa θ τ * (Real.sqrt (Real.log n) / Real.log n) + (1 - 2 * θ)) * Real.log n =
      Real.log (n * RoughRegime.Rates.subcriticalScale n θ τ ^ 2) := by
    rw [Real.log_mul hnp.ne' (pow_pos (RoughRegime.Rates.scale_pos n θ τ hn) 2).ne', Real.log_pow, hscale]
    field_simp
    ring
  simp only [Function.comp_apply, id_eq]
  rw [hprodEq, Real.exp_log (mul_pos hnp (pow_pos (RoughRegime.Rates.scale_pos n θ τ hn) 2))]

/-- The actual source spectral margin `δ_n=(log n)^{-2}` vanishes. -/
lemma logarithmicMargin_tendsto_zero :
    Tendsto (fun n : ℝ => (Real.log n) ^ (-2 : ℝ)) atTop (nhds 0) := by
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).pow 2
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  simp only [Function.comp_apply, Real.rpow_neg (Real.log_pos hn).le, Real.rpow_two, inv_pow]

/-- The nearest-even frequency times the source spectral margin vanishes. -/
lemma frequencyTimesMargin_tendsto_zero (θ τ : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => frequency n θ τ * (Real.log n) ^ (-2 : ℝ)) atTop (nhds 0) := by
  have h := (frequency_div_log_tendsto_zero θ τ hθ hθhalf hτ).mul
    (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop)
  simp only [mul_zero] at h
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  simp only [Function.comp_apply, Real.rpow_neg (Real.log_pos hn).le, Real.rpow_two, div_eq_mul_inv]
  ring

end RoughRegime.ReductionScales
