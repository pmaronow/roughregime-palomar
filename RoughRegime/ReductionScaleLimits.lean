module

public import RoughRegime.ReductionScales


@[expose] public section
/-! Genuine limits for the actual rounded lower-bound block scale. -/
noncomputable section
open Filter

namespace RoughRegime.ReductionScales

def blockInflation (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) : ℝ :=
  (selectedBlockCount θ τ c0 R d n : ℝ) / n

lemma resolutionRatio_eq_inflation (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) :
    resolutionRatio θ τ c0 R d n = blockInflation θ τ c0 R d n * R n := by
  unfold resolutionRatio blockInflation
  ring

lemma blockCount_positive (n R t : ℝ) (d : ℕ) (hn : 0 < n) (hR : 0 < R) :
    0 < blockCount n R t d := by
  have hz := idealSideLength_positive n R t d hn hR
  have hk : 0 < evenCeiling (idealSideLength n R t d) := by
    have h := hz.trans_le (evenCeiling_bounds _ hz.le).1
    exact_mod_cast h
  exact Nat.pow_pos hk

lemma blockInflation_positive (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ)
    (hn : 0 < n) (hR : 0 < R n) : 0 < blockInflation θ τ c0 R d n := by
  unfold blockInflation selectedBlockCount
  exact div_pos (by exact_mod_cast blockCount_positive n (R n) _ d hn hR) hn

lemma log_resolutionRatio_div_frequency_tendsto (θ τ c0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => Real.log (resolutionRatio θ τ c0 R d n) / frequency n θ τ) atTop (nhds (τ / θ)) := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have he := (log_resolutionRatio_sub_tendsto_zero θ τ c0 hθ hθhalf hτ R hRpos hR d hd).mul
    (tendsto_inv_atTop_zero.comp hM)
  norm_num only [mul_zero] at he
  have hlim := he.add (logResolution_div_frequency_tendsto θ τ c0 hθ hθhalf hτ)
  norm_num only [zero_add] at hlim
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [] with n
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/-- The actual rounded block inflation has the source exponential scale. -/
theorem log_blockInflation_div_frequency_tendsto (θ τ c0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => Real.log (blockInflation θ τ c0 R d n) / frequency n θ τ) atTop (nhds (τ / θ)) := by
  have hx := log_resolutionRatio_div_frequency_tendsto θ τ c0 hθ hθhalf hτ R hRpos hR d hd
  have hr := logR_div_frequency_tendsto_zero θ τ hθ hθhalf hτ R hR
  have hlim := hx.sub hr
  norm_num only [sub_zero] at hlim
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [hRpos, eventually_gt_atTop (0 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  rw [resolutionRatio_eq_inflation, Real.log_mul (blockInflation_positive θ τ c0 R d n hn hRp).ne' hRp.ne']
  ring

lemma log_blockInflation_tendsto (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => Real.log (blockInflation θ τ c0 R d n)) atTop atTop := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hprod := (log_blockInflation_div_frequency_tendsto θ τ c0 hθ hθhalf hτ R hRpos hR d hd).pos_mul_atTop
    (div_pos hτ hθ) hM
  apply Filter.Tendsto.congr' _ hprod
  filter_upwards [hM.eventually_ge_atTop 1] with n hn
  have hM0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
  exact div_mul_cancel₀ _ hM0

lemma logLog_div_frequency_tendsto_zero (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => Real.log (Real.log n) / frequency n θ τ) atTop (nhds 0) := by
  have hΔ : 0 < 1 - 2 * θ := by linarith
  have hc : 0 < θ * (1 - 2 * θ) / τ := by positivity
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hlogRatio := (Real.continuousAt_log hc.ne').tendsto.comp (frequency_sq_log_tendsto θ τ hθ hθhalf hτ)
  have hrem := hlogRatio.mul (tendsto_inv_atTop_zero.comp hM)
  norm_num only [mul_zero] at hrem
  have hlim := ((logFrequency_div_frequency_tendsto_zero θ τ hθ hθhalf hτ).const_mul 2).sub hrem
  norm_num only [mul_zero, sub_self] at hlim
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [hM.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)] with n hn hn1
  have hmpos : 0 < (frequency n θ τ : ℝ) := zero_lt_one.trans_le hn
  have hln : 0 < Real.log n := Real.log_pos hn1
  simp only [Function.comp_apply]
  rw [Real.log_div (pow_pos hmpos 2).ne' hln.ne', Real.log_pow]
  simp only [div_eq_mul_inv]
  ring

/-- `B/(n(log n)^q)` diverges for every fixed real `q`; in particular the
block count is eventually at least `n`. -/
theorem blockInflation_div_logPower_tendsto (θ τ c0 q : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => blockInflation θ τ c0 R d n / (Real.log n) ^ q) atTop atTop := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hratio := (log_blockInflation_div_frequency_tendsto θ τ c0 hθ hθhalf hτ R hRpos hR d hd).sub
    ((logLog_div_frequency_tendsto_zero θ τ hθ hθhalf hτ).const_mul q)
  norm_num only [mul_zero, sub_zero] at hratio
  have hprod := hratio.pos_mul_atTop (div_pos hτ hθ) hM
  have hprodEq : Tendsto (fun n : ℝ => Real.log (blockInflation θ τ c0 R d n) - q * Real.log (Real.log n)) atTop atTop := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards [hM.eventually_ge_atTop 1] with n hn
    have hm0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
    field_simp
  have he := Real.tendsto_exp_atTop.comp hprodEq
  apply Filter.Tendsto.congr' _ he
  filter_upwards [hRpos, eventually_gt_atTop (1 : ℝ)] with n hRn hn
  have hnp : 0 < n := zero_lt_one.trans hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  have hln : 0 < Real.log n := Real.log_pos hn
  rw [Function.comp_apply, Real.exp_sub, Real.exp_log (blockInflation_positive θ τ c0 R d n hnp hRp)]
  congr 1
  rw [Real.rpow_def_of_pos hln]
  congr 1
  ring

lemma lambda_log_scale (θ τ c0 v0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hv : 0 < v0)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => Real.log (2 * v0 / blockInflation θ τ c0 R d n) / frequency n θ τ) atTop (nhds (-τ / θ)) := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hconst := (tendsto_inv_atTop_zero.comp hM).const_mul (Real.log (2 * v0))
  have hlim := hconst.sub (log_blockInflation_div_frequency_tendsto θ τ c0 hθ hθhalf hτ R hRpos hR d hd)
  simp only [mul_zero, zero_sub] at hlim
  rw [neg_div]
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [hRpos, eventually_gt_atTop (0 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  rw [Real.log_div (by positivity) (blockInflation_positive θ τ c0 R d n hn hRp).ne']
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/-- The actual Poisson tail ratio `y R^(sqrt M)` vanishes. -/
theorem tilted_tail_ratio_tendsto_zero (θ τ c0 C1 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (hτ : 0 < τ) (hC1 : 0 < C1)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => (C1 / blockInflation θ τ c0 R d n) * R n ^ Real.sqrt (frequency n θ τ)) atTop (nhds 0) := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hbase := lambda_log_scale θ τ c0 (C1 / 2) hθ hθhalf hτ (by positivity) R hRpos hR d hd
  have hC : 2 * (C1 / 2) = C1 := by ring
  rw [hC] at hbase
  have hRsmall := logR_div_sqrtFrequency_tendsto_zero θ τ hθ hθhalf hτ R hR
  have hratio := hbase.add hRsmall
  simp only [add_zero] at hratio
  have hprod := hratio.neg_mul_atTop (div_neg_of_neg_of_pos (neg_neg_of_pos hτ) hθ) hM
  have hprodEq : Tendsto (fun n : ℝ => Real.log (C1 / blockInflation θ τ c0 R d n) +
      Real.sqrt (frequency n θ τ) * Real.log (R n)) atTop atBot := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards [hM.eventually_ge_atTop 1] with n hn
    have hm : 0 < (frequency n θ τ : ℝ) := zero_lt_one.trans_le hn
    have hs : Real.sqrt (frequency n θ τ) ^ 2 = frequency n θ τ := Real.sq_sqrt hm.le
    have hs0 : Real.sqrt (frequency n θ τ) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
    field_simp
    linear_combination -Real.log (R n) * hs
  have he := Real.tendsto_exp_atBot.comp hprodEq
  apply Filter.Tendsto.congr' _ he
  filter_upwards [hRpos, eventually_gt_atTop (0 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  rw [Function.comp_apply, Real.exp_add, Real.exp_log (div_pos hC1 (blockInflation_positive θ τ c0 R d n hn hRp))]
  rw [Real.rpow_def_of_pos hRp]
  congr 2
  ring

end RoughRegime.ReductionScales
