module

public import RoughRegime.ReductionScaleLimits


@[expose] public section
/-! Exact leading hardness and separation calculations in Proposition 12. -/
noncomputable section
open Filter

namespace RoughRegime.ReductionScales

def leadingHardness (n θ v0 ε R m CE C1 x : ℝ) (M : ℕ) : ℝ :=
  4 * v0 ^ 2 * ε ^ 2 * n ^ (1 - 2 * θ) * R ^ 2 * m ^ 4 * Real.exp (CE * M) * C1 ^ M /
    ((M.factorial : ℝ) * x ^ ((M : ℝ) + 1 + 2 * θ))

lemma leadingHardness_positive (n θ v0 ε R m CE C1 x : ℝ) (M : ℕ)
    (hn : 0 < n) (hv : 0 < v0) (hε : 0 < ε) (hR : 0 < R) (hm : 0 < m) (hC1 : 0 < C1) (hx : 0 < x) :
    0 < leadingHardness n θ v0 ε R m CE C1 x M := by unfold leadingHardness; positivity

lemma log_leadingHardness (n θ v0 ε R m CE C1 x : ℝ) (M : ℕ)
    (hn : 0 < n) (hv : 0 < v0) (hε : 0 < ε) (hR : 0 < R) (hm : 0 < m) (hC1 : 0 < C1) (hx : 0 < x) :
    Real.log (leadingHardness n θ v0 ε R m CE C1 x M) =
      Real.log (4 * v0 ^ 2) + 2 * Real.log ε + (1 - 2 * θ) * Real.log n +
        2 * Real.log R + 4 * Real.log m + CE * M + M * Real.log C1 -
          Real.log (M.factorial : ℝ) - ((M : ℝ) + 1 + 2 * θ) * Real.log x := by
  simp (disch := positivity) only [leadingHardness, Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_exp, Real.log_rpow]
  ring

/-- The exact source logarithmic hardness inequality after the factorial bound.
The margin `c0−1−log C1−CE` is what drives indistinguishability. -/
theorem leadingHardness_log_upper (n θ v0 ε R m CE C1 c0 x : ℝ) (M : ℕ)
    (hn : 0 < n) (hθ : 0 ≤ θ) (hv : 0 < v0) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (hm : 0 < m) (hC1 : 0 < C1) (hM : 1 ≤ M)
    (hx : Real.exp ((1 - 2 * θ) * Real.log n / M - Real.log M + c0) ≤ x) :
    Real.log (leadingHardness n θ v0 ε R m CE C1 x M) ≤
      Real.log (4 * v0 ^ 2) + 2 * Real.log R + 4 * Real.log m -
        (1 + 2 * θ) * ((1 - 2 * θ) * Real.log n / M - Real.log M + c0) -
          (c0 - 1 - Real.log C1 - CE) * M := by
  have hmR : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hxR : 0 < x := (Real.exp_pos _).trans_le hx
  have hlogx : (1 - 2 * θ) * Real.log n / M - Real.log M + c0 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    simpa only [Real.log_exp] using h
  have hεlog : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hfac := log_factorial_lower M hM
  have hc : 0 ≤ (M : ℝ) + 1 + 2 * θ := by positivity
  rw [log_leadingHardness n θ v0 ε R m CE C1 x M hn hv hε hR hm hC1 hxR]
  have hpower := mul_le_mul_of_nonneg_left hlogx hc
  have heq : (M : ℝ) * ((1 - 2 * θ) * Real.log n / M - Real.log M + c0) =
      (1 - 2 * θ) * Real.log n - M * Real.log M + c0 * M := by field_simp
  nlinarith

lemma log_multiplier_isBigO (θ τ c : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hc : 0 < c)
    (m : ℝ → ℝ) (hm1 : ∀ᶠ n in atTop, 1 ≤ m n)
    (hmM : ∀ᶠ n in atTop, m n ≤ c * frequency n θ τ) :
    (fun n => Real.log (m n)) =O[atTop] (fun n => Real.log (frequency n θ τ)) := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hlogM := Real.tendsto_log_atTop.comp hM
  refine Asymptotics.IsBigO.of_bound (1 + |Real.log c|) ?_
  filter_upwards [hm1, hmM, hM.eventually_ge_atTop 1, hlogM.eventually_ge_atTop 1] with n hn1 hnm hnM hnLog
  simp only [Function.comp_apply] at hnLog
  have hmp : 0 < m n := zero_lt_one.trans_le hn1
  have hMp : 0 < (frequency n θ τ : ℝ) := zero_lt_one.trans_le hnM
  have hlogm : 0 ≤ Real.log (m n) := Real.log_nonneg hn1
  have hlogbound := Real.log_le_log hmp hnm
  rw [Real.log_mul hc.ne' hMp.ne'] at hlogbound
  simp only [Real.norm_eq_abs, abs_of_nonneg hlogm, abs_of_nonneg (by linarith : 0 ≤ Real.log (frequency n θ τ))]
  nlinarith [le_abs_self (Real.log c), abs_nonneg (Real.log c)]

/-- The actual leading hardness term tends to zero for the source constant choice. -/
theorem leadingHardness_tendsto_zero (θ τ c0 v0 ε CE C1 c : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hv : 0 < v0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC1 : 0 < C1) (hc : 0 < c)
    (hmargin : 1 + Real.log C1 + CE < c0)
    (R m : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n) (hmpos : ∀ᶠ n in atTop, 1 ≤ m n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (hmM : ∀ᶠ n in atTop, m n ≤ c * frequency n θ τ)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => leadingHardness n θ v0 ε (R n) (m n) CE C1
      (resolutionRatio θ τ c0 R d n) (frequency n θ τ)) atTop (nhds 0) := by
  let margin := c0 - 1 - Real.log C1 - CE
  have hmarginp : 0 < margin := by dsimp [margin]; linarith
  let U : ℝ → ℝ := fun n => Real.log (4 * v0 ^ 2) + 2 * Real.log (R n) + 4 * Real.log (m n) - margin * frequency n θ τ
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hRsmall := logR_div_frequency_tendsto_zero θ τ hθ hθhalf hτ R hR
  have hmsmall := logR_div_frequency_tendsto_zero θ τ hθ hθhalf hτ m
    (log_multiplier_isBigO θ τ c hθ hθhalf hτ hc m hmpos hmM)
  have hconst := (tendsto_inv_atTop_zero.comp hM).const_mul (Real.log (4 * v0 ^ 2))
  have hsum := (hconst.add (hRsmall.const_mul 2)).add (hmsmall.const_mul 4)
  norm_num only [mul_zero, add_zero] at hsum
  have hratio := hsum.sub_const margin
  simp only [zero_sub] at hratio
  have hratioU : Tendsto (fun n : ℝ => U n / frequency n θ τ) atTop (nhds (-margin)) := by
    apply Filter.Tendsto.congr' _ hratio
    filter_upwards [hM.eventually_ge_atTop 1] with n hn
    have hm0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
    dsimp [U]
    field_simp
  have hUprod := hratioU.neg_mul_atTop (neg_neg_of_pos hmarginp) hM
  have hU : Tendsto U atTop atBot := by
    apply Filter.Tendsto.congr' _ hUprod
    filter_upwards [hM.eventually_ge_atTop 1] with n hn
    have hm0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
    exact div_mul_cancel₀ _ hm0
  have he := Real.tendsto_exp_atBot.comp hU
  refine squeeze_zero' ?_ ?_ he
  · filter_upwards [hRpos, hmpos, eventually_gt_atTop (0 : ℝ)] with n hRn hmn hn
    have hRp : 0 < R n := zero_lt_one.trans_le hRn
    have hmp : 0 < m n := zero_lt_one.trans_le hmn
    have hx : 0 < resolutionRatio θ τ c0 R d n := by
      rw [resolutionRatio_eq_inflation]
      exact mul_pos (blockInflation_positive θ τ c0 R d n hn hRp) hRp
    exact (leadingHardness_positive n θ v0 ε (R n) (m n) CE C1 _ _ hn hv hε hRp hmp hC1 hx).le
  · filter_upwards [hRpos, hmpos, eventually_ge_atTop (1 : ℝ), hM.eventually_ge_atTop 1,
      (logResolution_tendsto θ τ c0 hθ hθhalf hτ).eventually_ge_atTop 0] with n hRn hmn hn hnM ht
    have hnp : 0 < n := zero_lt_one.trans_le hn
    have hRp : 0 < R n := zero_lt_one.trans_le hRn
    have hmp : 0 < m n := zero_lt_one.trans_le hmn
    have hMn : 1 ≤ frequency n θ τ := by exact_mod_cast hnM
    rcases blockCount_rounding n (R n) (logResolution n θ τ c0) d hnp hRp hd with
      ⟨k, hke, hk, hmin, hlo, hhi⟩
    have hx : Real.exp (logResolution n θ τ c0) ≤ resolutionRatio θ τ c0 R d n := by
      have hlow : 1 ≤ resolutionRatio θ τ c0 R d n / Real.exp (logResolution n θ τ c0) := by
        simpa only [resolutionRatio, selectedBlockCount, Real.exp_neg, div_eq_mul_inv] using hlo
      simpa only [one_mul] using (le_div_iff₀ (Real.exp_pos _)).mp hlow
    have hlog := leadingHardness_log_upper n θ v0 ε (R n) (m n) CE C1 c0
      (resolutionRatio θ τ c0 R d n) (frequency n θ τ) hnp hθ.le hv hε hε1 hRp hmp hC1 hMn hx
    have hIU : Real.log (leadingHardness n θ v0 ε (R n) (m n) CE C1 (resolutionRatio θ τ c0 R d n) (frequency n θ τ)) ≤ U n := by
      have hpos : 0 ≤ (1 + 2 * θ) * logResolution n θ τ c0 := mul_nonneg (by positivity) ht
      dsimp [U, margin]
      change _ ≤ _ at hlog
      unfold logResolution at hpos
      linarith
    have hIp : 0 < leadingHardness n θ v0 ε (R n) (m n) CE C1 (resolutionRatio θ τ c0 R d n) (frequency n θ τ) := by
      apply leadingHardness_positive _ _ _ _ _ _ _ _ _ _ hnp hv hε hRp hmp hC1
      rw [resolutionRatio_eq_inflation]
      exact mul_pos (blockInflation_positive θ τ c0 R d n hnp hRp) hRp
    simpa only [Real.exp_log hIp, Function.comp_apply] using Real.exp_le_exp.mpr hIU

/-- Any fixed power of `n` defeats the remaining `exp(C M log M)` loss. -/
theorem frequency_exponential_loss_tendsto_zero (θ τ a C : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (ha : 0 < a) :
    Tendsto (fun n : ℝ => n ^ (-a) * Real.exp (C * frequency n θ τ * Real.log (frequency n θ τ))) atTop (nhds 0) := by
  have hsmall := (frequency_log_div_log_tendsto_zero θ τ hθ hθhalf hτ).const_mul C
  have hratio := hsmall.sub_const a
  simp only [mul_zero, zero_sub] at hratio
  have hL := Real.tendsto_log_atTop
  have hprod := hratio.neg_mul_atTop (neg_neg_of_pos ha) hL
  have hbot : Tendsto (fun n : ℝ => -a * Real.log n + C * frequency n θ τ * Real.log (frequency n θ τ)) atTop atBot := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    have hLn : Real.log n ≠ 0 := (Real.log_pos hn).ne'
    field_simp
    ring
  have he := Real.tendsto_exp_atBot.comp hbot
  apply Filter.Tendsto.congr' _ he
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [Function.comp_apply, Real.exp_add, Real.rpow_def_of_pos hn]
  congr 1
  congr 1
  ring

end RoughRegime.ReductionScales
