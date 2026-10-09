module

public import RoughRegime.ReductionScaleLimits


@[expose] public section
/-! The stronger `O(log M)` scale expansions in Proposition 12. -/
noncomputable section
open Filter

namespace RoughRegime.ReductionScales

lemma frequency_linear_error_bound (n θ τ : ℝ) (hn : 1 < n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hlarge : 2 ≤ idealFrequency n θ τ) :
    |(1 - 2 * θ) * Real.log n / frequency n θ τ - (τ / θ) * frequency n θ τ| ≤ 3 * (τ / θ) := by
  have hc : 0 < τ / θ := div_pos hτ hθ
  have hM := nearestEven_comparison (idealFrequency n θ τ) hlarge
  have hMp : 0 < (frequency n θ τ : ℝ) := zero_lt_one.trans_le hM.1
  have hI : 0 ≤ idealFrequency n θ τ := by linarith
  have hdist : |idealFrequency n θ τ - frequency n θ τ| ≤ 1 := by
    simpa only [frequency, abs_sub_comm] using nearestEven_distance (idealFrequency n θ τ) (by linarith)
  have hsum : idealFrequency n θ τ + frequency n θ τ ≤ 3 * frequency n θ τ := by
    have hcomp : idealFrequency n θ τ / 2 ≤ (frequency n θ τ : ℝ) := hM.2.1
    linarith
  have hs := idealFrequency_sq n θ τ hn hθ hθhalf hτ
  have hid : (1 - 2 * θ) * Real.log n = (τ / θ) * idealFrequency n θ τ ^ 2 := by
    field_simp at hs ⊢
    nlinarith
  have heq : (1 - 2 * θ) * Real.log n / frequency n θ τ - (τ / θ) * frequency n θ τ =
      (τ / θ) * (idealFrequency n θ τ - frequency n θ τ) *
        (idealFrequency n θ τ + frequency n θ τ) / frequency n θ τ := by
    rw [hid]
    field_simp
    ring
  rw [heq, abs_div, abs_mul, abs_mul, abs_of_pos hc,
    abs_of_nonneg (add_nonneg hI hMp.le), abs_of_pos hMp]
  apply (div_le_iff₀ hMp).mpr
  calc
    (τ / θ) * |idealFrequency n θ τ - frequency n θ τ| * (idealFrequency n θ τ + frequency n θ τ) ≤
      (τ / θ) * 1 * (3 * frequency n θ τ) := by gcongr
    _ = (3 * (τ / θ)) * frequency n θ τ := by ring

lemma logResolution_linear_isBigO (θ τ c0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    (fun n => logResolution n θ τ c0 - (τ / θ) * frequency n θ τ) =O[atTop]
      (fun n => Real.log (frequency n θ τ)) := by
  have hi := idealFrequency_tendsto θ τ hθ hθhalf hτ
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hlog := Real.tendsto_log_atTop.comp hM
  refine Asymptotics.IsBigO.of_bound (3 * (τ / θ) + |c0| + 1) ?_
  filter_upwards [hi.eventually_ge_atTop 2, hlog.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)] with n hin hnL hn
  simp only [Function.comp_apply] at hnL
  have hb := frequency_linear_error_bound n θ τ hn hθ hθhalf hτ hin
  have hlogpos : 0 ≤ Real.log (frequency n θ τ) := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg hlogpos]
  have heq : logResolution n θ τ c0 - (τ / θ) * frequency n θ τ =
      ((1 - 2 * θ) * Real.log n / frequency n θ τ - (τ / θ) * frequency n θ τ) - Real.log (frequency n θ τ) + c0 := by
    unfold logResolution
    ring
  rw [heq]
  have ha := abs_add_le (((1 - 2 * θ) * Real.log n / frequency n θ τ - (τ / θ) * frequency n θ τ) - Real.log (frequency n θ τ)) c0
  have hs := abs_add_le ((1 - 2 * θ) * Real.log n / frequency n θ τ - (τ / θ) * frequency n θ τ) (-Real.log (frequency n θ τ))
  simp only [abs_neg, abs_of_nonneg hlogpos, ← sub_eq_add_neg] at hs
  have hconst : 0 ≤ 3 * (τ / θ) + |c0| := by positivity
  nlinarith

lemma log_rounding_isBigO (θ τ c0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    (fun n => Real.log (resolutionRatio θ τ c0 R d n) - logResolution n θ τ c0) =O[atTop]
      (fun n => Real.log (frequency n θ τ)) := by
  have he := log_resolutionRatio_sub_tendsto_zero θ τ c0 hθ hθhalf hτ R hRpos hR d hd
  have hn := (tendsto_norm.comp he).eventually_le_const (by norm_num : ‖(0 : ℝ)‖ < 1)
  have hlog := Real.tendsto_log_atTop.comp (frequency_tendsto θ τ hθ hθhalf hτ)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [hn, hlog.eventually_ge_atTop 1] with n hne hnL
  simp only [Function.comp_apply] at hne hnL
  simp only [one_mul, Real.norm_eq_abs]
  exact hne.trans ((le_abs_self _).trans' hnL)

/-- The source log-inflation expansion with a genuine `O(log M)` remainder. -/
theorem log_blockInflation_linear_isBigO (θ τ c0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    (fun n => Real.log (blockInflation θ τ c0 R d n) - (τ / θ) * frequency n θ τ) =O[atTop]
      (fun n => Real.log (frequency n θ τ)) := by
  have hb := ((log_rounding_isBigO θ τ c0 hθ hθhalf hτ R hRpos hR d hd).add
    (logResolution_linear_isBigO θ τ c0 hθ hθhalf hτ)).sub hR
  apply hb.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hRpos, eventually_gt_atTop (0 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  rw [resolutionRatio_eq_inflation, Real.log_mul (blockInflation_positive θ τ c0 R d n hn hRp).ne' hRp.ne']
  ring

lemma constant_isBigO_logFrequency (θ τ c : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    (fun _ : ℝ => c) =O[atTop] (fun n => Real.log (frequency n θ τ)) := by
  have hlog := Real.tendsto_log_atTop.comp (frequency_tendsto θ τ hθ hθhalf hτ)
  apply Asymptotics.IsBigO.of_bound |c|
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply] at hn
  simp only [Real.norm_eq_abs]
  nlinarith [le_abs_self (Real.log (frequency n θ τ)), abs_nonneg c]

/-- Exact source log-Lambda expansion, including its genuine `O(log M)` error. -/
theorem log_lambda_linear_isBigO (θ τ c0 v0 : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hv : 0 < v0)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    (fun n => Real.log (2 * v0 / blockInflation θ τ c0 R d n) + (τ / θ) * frequency n θ τ) =O[atTop]
      (fun n => Real.log (frequency n θ τ)) := by
  have hb := (constant_isBigO_logFrequency θ τ (Real.log (2 * v0)) hθ hθhalf hτ).sub
    (log_blockInflation_linear_isBigO θ τ c0 hθ hθhalf hτ R hRpos hR d hd)
  apply hb.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hRpos, eventually_gt_atTop (0 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  rw [Real.log_div (by positivity) (blockInflation_positive θ τ c0 R d n hn hRp).ne']
  ring

end RoughRegime.ReductionScales
