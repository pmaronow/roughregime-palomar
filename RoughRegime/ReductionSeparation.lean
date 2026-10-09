module

public import RoughRegime.ReductionScaleLimits


@[expose] public section
/-! Exact asymptotic separation for the actual nearest-even frequency and
smallest even-side block count of Proposition 12. -/
noncomputable section
open Filter

namespace RoughRegime.ReductionScales

def separationScale (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) : ℝ :=
  (n * resolutionRatio θ τ c0 R d n) ^ (-θ) * Real.exp (-τ * frequency n θ τ)

def separationConstant (θ τ c0 : ℝ) : ℝ :=
  Real.exp (-θ * c0) * (θ * (1 - 2 * θ) / τ) ^ (θ / 2)

lemma separationConstant_positive (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    0 < separationConstant θ τ c0 := by
  unfold separationConstant
  have hΔ : 0 < 1 - 2 * θ := by linarith
  positivity

lemma frequency_phase_penalty_tendsto_zero (θ τ : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => θ * (1 - 2 * θ) * Real.log n / frequency n θ τ + τ * frequency n θ τ -
      RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) atTop (nhds 0) := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hi := idealFrequency_tendsto θ τ hθ hθhalf hτ
  have ht := (tendsto_inv_atTop_zero.comp hM).const_mul τ
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hi.eventually_ge_atTop 2] with n hn hn2
    exact (frequency_phase_penalty n θ τ hn hθ hθhalf hτ hn2).1
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hi.eventually_ge_atTop 2] with n hn hn2
    simpa only [Function.comp_apply, div_eq_mul_inv] using
      (frequency_phase_penalty n θ τ hn hθ hθhalf hτ hn2).2

lemma logFrequency_minus_half_logLog_tendsto (θ τ : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => Real.log (frequency n θ τ) - (1 / 2 : ℝ) * Real.log (Real.log n))
      atTop (nhds ((1 / 2 : ℝ) * Real.log (θ * (1 - 2 * θ) / τ))) := by
  have hΔ : 0 < 1 - 2 * θ := by linarith
  have hc : 0 < θ * (1 - 2 * θ) / τ := by positivity
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hlog := ((Real.continuousAt_log hc.ne').tendsto.comp
    (frequency_sq_log_tendsto θ τ hθ hθhalf hτ)).const_mul (1 / 2 : ℝ)
  apply Filter.Tendsto.congr' _ hlog
  filter_upwards [hM.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)] with n hnM hn
  have hMp : 0 < (frequency n θ τ : ℝ) := zero_lt_one.trans_le hnM
  simp only [Function.comp_apply]
  rw [Real.log_div (pow_pos hMp 2).ne' (Real.log_pos hn).ne', Real.log_pow]
  ring

lemma log_separationScale_ratio (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ)
    (hn : 1 < n) (hx : 0 < resolutionRatio θ τ c0 R d n) :
    Real.log (separationScale θ τ c0 R d n / RoughRegime.Rates.subcriticalScale n θ τ) =
      -θ * (Real.log (resolutionRatio θ τ c0 R d n) - logResolution n θ τ c0) -
        (θ * (1 - 2 * θ) * Real.log n / frequency n θ τ + τ * frequency n θ τ -
          RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) +
          θ * (Real.log (frequency n θ τ) - (1 / 2 : ℝ) * Real.log (Real.log n)) - θ * c0 := by
  have hnp : 0 < n := zero_lt_one.trans hn
  have hsp : 0 < separationScale θ τ c0 R d n := by unfold separationScale; positivity
  rw [Real.log_div hsp.ne' (RoughRegime.Rates.scale_pos n θ τ hn).ne', RoughRegime.Rates.log_scale n θ τ hn]
  unfold separationScale logResolution
  rw [Real.log_mul (Real.rpow_pos_of_pos (mul_pos hnp hx) (-θ)).ne' (Real.exp_pos _).ne',
    Real.log_rpow (mul_pos hnp hx), Real.log_mul hnp.ne' hx.ne', Real.log_exp]
  ring

/-- The rounded construction has an exact positive limiting ratio to the
paper's subcritical scale. No separation inequality is assumed. -/
theorem separationScale_ratio_tendsto (θ τ c0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => separationScale θ τ c0 R d n / RoughRegime.Rates.subcriticalScale n θ τ)
      atTop (nhds (separationConstant θ τ c0)) := by
  have herror := log_resolutionRatio_sub_tendsto_zero θ τ c0 hθ hθhalf hτ R hRpos hR d hd
  have hphase := frequency_phase_penalty_tendsto_zero θ τ hθ hθhalf hτ
  have hlogM := logFrequency_minus_half_logLog_tendsto θ τ hθ hθhalf hτ
  have hlim := (((herror.const_mul (-θ)).sub hphase).add (hlogM.const_mul θ)).sub_const (θ * c0)
  simp only [mul_zero, zero_sub, neg_zero, zero_add] at hlim
  have hloglim : Tendsto (fun n : ℝ => Real.log (separationScale θ τ c0 R d n / RoughRegime.Rates.subcriticalScale n θ τ))
      atTop (nhds (θ * ((1 / 2 : ℝ) * Real.log (θ * (1 - 2 * θ) / τ)) - θ * c0)) := by
    apply Filter.Tendsto.congr' _ hlim
    filter_upwards [hRpos, eventually_gt_atTop (1 : ℝ)] with n hRn hn
    have hRp : 0 < R n := zero_lt_one.trans_le hRn
    have hx : 0 < resolutionRatio θ τ c0 R d n := by
      rw [resolutionRatio_eq_inflation]
      exact mul_pos (blockInflation_positive θ τ c0 R d n (zero_lt_one.trans hn) hRp) hRp
    exact (log_separationScale_ratio θ τ c0 R d n hn hx).symm
  have he := Real.continuous_exp.continuousAt.tendsto.comp hloglim
  have hΔ : 0 < 1 - 2 * θ := by linarith
  have hc : 0 < θ * (1 - 2 * θ) / τ := by positivity
  have hconst : Real.exp (θ * ((1 / 2 : ℝ) * Real.log (θ * (1 - 2 * θ) / τ)) - θ * c0) = separationConstant θ τ c0 := by
    unfold separationConstant
    rw [Real.rpow_def_of_pos hc, ← Real.exp_add]
    congr 1
    ring
  rw [hconst] at he
  apply Filter.Tendsto.congr' _ he
  filter_upwards [hRpos, eventually_gt_atTop (1 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  have hx : 0 < resolutionRatio θ τ c0 R d n := by
    rw [resolutionRatio_eq_inflation]
    exact mul_pos (blockInflation_positive θ τ c0 R d n (zero_lt_one.trans hn) hRp) hRp
  have hsp : 0 < separationScale θ τ c0 R d n := by unfold separationScale; positivity
  simpa only [Function.comp_apply] using Real.exp_log (div_pos hsp (RoughRegime.Rates.scale_pos n θ τ hn))

/-- Concrete eventual separation constant for the exact selected blocks. -/
theorem separationScale_eventually_lower (θ τ c0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    ∀ᶠ n in atTop, (separationConstant θ τ c0 / 2) * RoughRegime.Rates.subcriticalScale n θ τ ≤ separationScale θ τ c0 R d n := by
  have hc := separationConstant_positive θ τ c0 hθ hθhalf hτ
  have hl := (separationScale_ratio_tendsto θ τ c0 hθ hθhalf hτ R hRpos hR d hd).eventually_const_le (by linarith : separationConstant θ τ c0 / 2 < separationConstant θ τ c0)
  filter_upwards [hl, eventually_gt_atTop (1 : ℝ)] with n hn1 hn
  exact (le_div_iff₀ (RoughRegime.Rates.scale_pos n θ τ hn)).mp hn1

end RoughRegime.ReductionScales
