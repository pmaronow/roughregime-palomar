module

public import RoughRegime.UpperSubcriticalBias


@[expose] public section
/-! Eventual validity and the complete numeric risk bound for the actual
subcritical terminal and minimum degree rules. -/
noncomputable section
open Filter
namespace RoughRegime.UpperSubcritical
open RoughRegime.UpperDegreeRules RoughRegime.UpperParametric

structure TuningValid (n θ τ A Cv : ℝ) (ν : ℕ) : Prop where
  sample_positive : 0 < n
  log_sample_one : 1 ≤ Real.log n
  log_square_le_sample : (Real.log n) ^ 2 ≤ n
  resolution_small : Cv * highDegreeEnvelope n θ τ A ν ≤ (Real.log n) ^ 2
  budget_positive : 0 < budget n θ τ
  floor_large : (ν : ℝ) + 3 ≤ budget n θ τ / windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n
  low_degree_small : Cv * globalDegreeConstant θ τ A ν ≤ Real.log n
  degree_sample : ∀ j : Fin (terminal n θ τ + 1), (2 : ℝ) * chosenDegree n θ τ A Cv ν j ≤ n

lemma logSquare_div_sample_tendsto_zero :
    Tendsto (fun n : ℝ => (Real.log n) ^ 2 / n) atTop (nhds 0) := by
  have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).pow 2
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  have hid : (n ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    norm_num
  simp only [div_pow, hid]

/-- One genuine sample threshold validates all the source inequalities and
all chosen polynomial degrees simultaneously. -/
theorem tuning_valid_eventually (θ τ A Cv : ℝ) (ν : ℕ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hA : 0 ≤ A) (hCv : 1 ≤ Cv) :
    ∀ᶠ n : ℝ in atTop, TuningValid n θ τ A Cv ν := by
  let Δ := 1 - 2 * θ
  let κ := RoughRegime.Rates.kappa θ τ
  let CR := highDegreeConstant θ τ A ν
  let CX := windowConstant θ τ Cv CR
  let Cg := globalDegreeConstant θ τ A ν
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  have hκ : 0 < κ := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hCvp : 0 < Cv := zero_lt_one.trans_le hCv
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCR : 0 ≤ CR := by unfold CR highDegreeConstant; positivity
  have hCX : 0 ≤ CX := by unfold CX windowConstant; positivity
  have hCg : 0 ≤ Cg := by unfold Cg globalDegreeConstant levelCountConstant; positivity
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul (2 * Cg)
  simp only [mul_zero] at hsmall
  filter_upwards [eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (Cv * CR),
    Real.tendsto_log_atTop.eventually_ge_atTop (Cv * Cg),
    Real.tendsto_log_atTop.eventually_ge_atTop ((4 * κ / Δ) ^ 2),
    Real.tendsto_log_atTop.eventually_ge_atTop ((2 * CX * ((ν : ℝ) + 3) / Δ) ^ 2),
    logSquare_div_sample_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hsmall.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn hL hLC hLg hLκ hLX hSq hSz
  have hLp : 0 < Real.log n := zero_lt_one.trans_le hL
  have hsp : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hLp
  have hs := Real.sq_sqrt hLp.le
  have hsle : Real.sqrt (Real.log n) ≤ Real.log n := by nlinarith [Real.sqrt_nonneg (Real.log n)]
  have hnSq : (Real.log n) ^ 2 ≤ n := (div_le_one hn).mp hSq
  have hR := highDegreeEnvelope_bound n θ τ A ν hL hθ hθhalf hτ hA
  have hRs : Cv * highDegreeEnvelope n θ τ A ν ≤ (Real.log n) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hR hCvp.le
    have h2 := mul_le_mul_of_nonneg_right hLC hsp.le
    have h3 := mul_le_mul_of_nonneg_left hsle hLp.le
    dsimp [CR] at h2
    nlinarith
  have hκs : 4 * κ / Δ ≤ Real.sqrt (Real.log n) := by
    have h := Real.sqrt_le_sqrt hLκ
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 4 * κ / Δ)] using h
  have hκmul := (div_le_iff₀ hΔ).mp hκs
  have hBhalf : Δ * Real.log n / 2 ≤ budget n θ τ := by
    have hm := mul_le_mul_of_nonneg_right hκmul hsp.le
    dsimp [budget, Δ, κ] at *
    nlinarith
  have hBp : 0 < budget n θ τ := (by positivity : 0 < Δ * Real.log n / 2).trans_le hBhalf
  have hXs : 2 * CX * ((ν : ℝ) + 3) / Δ ≤ Real.sqrt (Real.log n) := by
    have h := Real.sqrt_le_sqrt hLX
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2 * CX * ((ν : ℝ) + 3) / Δ)] using h
  have hXmul := (div_le_iff₀ hΔ).mp hXs
  have hXenv := windowEndpoint_bound n θ τ A Cv ν hL hθ hθhalf hτ hA hCvp
  have hXp := windowEndpoint_positive n θ τ A Cv ν hL hθ hθhalf hτ hA hCv
  have hfloor : (ν : ℝ) + 3 ≤ budget n θ τ / windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n := by
    apply (le_div_iff₀ hXp).mpr
    have hm := mul_le_mul_of_nonneg_left hXenv (show 0 ≤ (ν : ℝ) + 3 by positivity)
    have hx := mul_le_mul_of_nonneg_right hXmul hsp.le
    dsimp [CX, CR] at hx
    nlinarith
  have hsize : 2 * Cg * Real.log n ≤ n := by
    simp only [id_eq] at hSz
    have h := (div_le_one hn).mp (show 2 * Cg * Real.log n / n ≤ 1 by convert hSz using 1; ring)
    simpa only [one_mul] using h
  refine ⟨hn, hL, hnSq, hRs, hBp, hfloor, hLg, ?_⟩
  intro j
  have hd := chosenDegree_global_bound n θ τ A Cv ν hL hθ hθhalf hτ hA j
  have hm := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [Cg] at hsize
  exact hm.trans (by convert hsize using 1; ring)

lemma sqrt_div_id_tendsto_zero :
    Tendsto (fun x : ℝ => Real.sqrt x / x) atTop (nhds 0) := by
  have h := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs := Real.sq_sqrt hx.le
  have hsp := Real.sqrt_pos.mpr hx
  simp only [Function.comp_apply]
  field_simp
  nlinarith

lemma logPower_negative_exp_sqrt_tendsto_zero (δ κ p : ℝ) (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => x ^ p * Real.exp (-δ * x + κ * Real.sqrt x)) atTop (nhds 0) := by
  have hratio := (((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).const_mul p).add
    (sqrt_div_id_tendsto_zero.const_mul κ)).sub_const δ
  simp only [mul_zero, zero_add, zero_sub] at hratio
  have hprod := hratio.neg_mul_atTop (neg_neg_of_pos hδ) tendsto_id
  have hbot : Tendsto (fun x : ℝ => p * Real.log x - δ * x + κ * Real.sqrt x) atTop atBot := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [id_eq]
    field_simp
    ring
  have he := Real.tendsto_exp_atBot.comp hbot
  apply Filter.Tendsto.congr' _ he
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Function.comp_apply, Real.rpow_def_of_pos hx, ← Real.exp_add]
  congr 1
  ring

lemma lowVariance_relative_rate_tendsto_zero (θ τ : ℝ) (ν : ℕ) (hθhalf : θ < 1 / 2) :
    Tendsto (fun n : ℝ => ((Real.log n) ^ (3 / 2 : ℝ) / Real.sqrt n) / rate n θ τ ν) atTop (nhds 0) := by
  have h := (logPower_negative_exp_sqrt_tendsto_zero (1 / 2 - θ) (RoughRegime.Rates.kappa θ τ)
    (3 / 2 - (θ / 2 + (ν : ℝ) / 2 + 1 / 4)) (by linarith)).comp Real.tendsto_log_atTop
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  have hnp : 0 < n := zero_lt_one.trans hn
  have hLp := Real.log_pos hn
  simp only [Function.comp_apply, rate, Real.sqrt_eq_rpow n, Real.rpow_def_of_pos hnp, Real.rpow_def_of_pos hLp]
  repeat rw [← Real.exp_add]
  repeat rw [← Real.exp_sub]
  congr 1
  ring

lemma highVariance_logPower_bound (n θ τ : ℝ) (ν : ℕ) (hn : 0 < n) (hL : 1 ≤ Real.log n) (hθ : 0 ≤ θ) (hν : 2 ≤ ν) :
    n ^ (-θ) * (Real.log n) ^ (5 / 4 : ℝ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) ≤ rate n θ τ ν := by
  have hνR : (2 : ℝ) ≤ ν := by exact_mod_cast hν
  have hp := Real.rpow_le_rpow_of_exponent_le hL (show (5 / 4 : ℝ) ≤ θ / 2 + (ν : ℝ) / 2 + 1 / 4 by linarith)
  unfold rate
  gcongr

lemma rate_positive (n θ τ : ℝ) (ν : ℕ) (hn : 1 < n) : 0 < rate n θ τ ν := by
  unfold rate
  have hnp : 0 < n := zero_lt_one.trans hn
  have hLp := Real.log_pos hn
  positivity

def riskConstant (θ τ A Cv C0 Cproj : ℝ) (ν : ℕ) : ℝ :=
  Cproj + C0 * (biasRuleConstant A ν + capConstant θ τ A Cv ν) +
    levelCountConstant θ τ * Real.sqrt (Cv * globalDegreeConstant θ τ A ν) +
    levelCountConstant θ τ * Real.sqrt (Cv * highDegreeConstant θ τ A ν)

/-- Complete numeric subcritical risk conclusion from the genuine population
bias and full Lemma 8 level variances. Every tuning condition is derived from
the original fixed parameters, uniformly over the level variance vector. -/
theorem chosen_total_error_bound_eventually (θ τ A Cv C0 Cproj q : ℝ) (ν : ℕ)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hA : 0 ≤ A) (hCv : 1 ≤ Cv)
    (hC0 : 0 ≤ C0) (hCproj : 0 ≤ Cproj) (hq : 0 ≤ q) (hν : 2 ≤ ν)
    (hdecay : θ * Real.log 2 + 1 ≤ τ * A) :
    ∀ᶠ n : ℝ in atTop, ∀ v : Fin (terminal n θ τ + 1) → ℝ,
      (∀ j, v j ≤ Cv * (parentCells (terminal n θ τ) j : ℝ) ^ (-2 * q) / n +
        ∑ k ∈ Finset.range (chosenDegree n θ τ A Cv ν j - 1),
          RoughRegime.LiftVariance.varianceTerm Cv (parentCells (terminal n θ τ) j) n (k + 2)) →
      Cproj * ((2 : ℝ) ^ terminal n θ τ) ^ (-θ) +
        C0 * (∑ j : Fin (terminal n θ τ + 1),
          approximationWeight (parentCells (terminal n θ τ) j) θ τ ν (chosenOrder n θ τ A Cv ν j)) +
        (∑ j : Fin (terminal n θ τ + 1), Real.sqrt (v j)) ≤ riskConstant θ τ A Cv C0 Cproj ν * rate n θ τ ν := by
  have hlow := (lowVariance_relative_rate_tendsto_zero θ τ ν hθhalf).eventually_le_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [tuning_valid_eventually θ τ A Cv ν hθ hθhalf hτ hA hCv, hlow, eventually_gt_atTop (1 : ℝ)] with n hn hl hn1
  intro v hv
  have hs := chosen_standard_deviation_sum_bound n θ τ A Cv q ν hn.sample_positive hn.log_sample_one hθ hθhalf hτ hA
    (zero_lt_one.trans_le hCv) hq hn.log_square_le_sample hn.budget_positive.le hn.low_degree_small hn.floor_large v hv
  have hb := chosen_bias_sum_bound n θ τ A Cv ν hn.sample_positive hn.log_sample_one hθ hθhalf hτ hA hCv hdecay
    hn.log_square_le_sample hn.resolution_small hn.budget_positive hn.floor_large
  have ht := terminal_bias_bound n θ τ hn.log_sample_one hn.sample_positive hθ hθhalf hτ
  have hrp := rate_positive n θ τ ν hn1
  have hlRate : (Real.log n) ^ (3 / 2 : ℝ) / Real.sqrt n ≤ rate n θ τ ν := (div_le_one hrp).mp hl
  have hp := highVariance_logPower_bound n θ τ ν hn.sample_positive hn.log_sample_one hθ.le hν
  have hpower : 1 ≤ (Real.log n) ^ (θ / 2 + (ν : ℝ) / 2 + 1 / 4) := Real.one_le_rpow hn.log_sample_one (by positivity)
  have htRate : ((2 : ℝ) ^ terminal n θ τ) ^ (-θ) ≤ rate n θ τ ν := by
    apply ht.trans
    unfold rate
    convert mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ n ^ (-θ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) by positivity) using 1 <;> ring
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCJ : 0 ≤ levelCountConstant θ τ := by unfold levelCountConstant; positivity
  have hsdRate : (∑ j : Fin (terminal n θ τ + 1), Real.sqrt (v j)) ≤
      (levelCountConstant θ τ * Real.sqrt (Cv * globalDegreeConstant θ τ A ν) +
        levelCountConstant θ τ * Real.sqrt (Cv * highDegreeConstant θ τ A ν)) * rate n θ τ ν := by
    refine hs.trans ?_
    convert add_le_add (mul_le_mul_of_nonneg_left hlRate (by positivity : 0 ≤ levelCountConstant θ τ * Real.sqrt (Cv * globalDegreeConstant θ τ A ν)))
      (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ levelCountConstant θ τ * Real.sqrt (Cv * highDegreeConstant θ τ A ν))) using 1 <;> ring
  unfold riskConstant
  convert add_le_add (add_le_add (mul_le_mul_of_nonneg_left htRate hCproj) (mul_le_mul_of_nonneg_left hb hC0)) hsdRate using 1; ring

lemma rate_eq_paper_scale (n θ τ : ℝ) (ν : ℕ) (hn : 1 < n) :
    rate n θ τ ν = RoughRegime.Rates.subcriticalScale n θ τ * (Real.log n) ^ ((ν : ℝ) / 2 + 1 / 4) := by
  unfold rate RoughRegime.Rates.subcriticalScale
  have heq : θ / 2 + (ν : ℝ) / 2 + 1 / 4 = θ / 2 + ((ν : ℝ) / 2 + 1 / 4) := by ring
  rw [heq, Real.rpow_add (Real.log_pos hn) (θ / 2) ((ν : ℝ) / 2 + 1 / 4)]
  ring

end RoughRegime.UpperSubcritical
