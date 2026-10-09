module

public import RoughRegime.UpperSubcriticalTuning


@[expose] public section
/-! The numerical domination assertions of the paper's combining-rates remark.
The rate is the literal piecewise upper-bracket rate, with arbitrary real ν. -/
noncomputable section
open Filter Asymptotics
namespace RoughRegime.RateCombination

def upperRate (n θ τ ν : ℝ) : ℝ :=
  if θ < 1 / 2 then
    Rates.subcriticalScale n θ τ * (Real.log n) ^ (ν / 2 + 1 / 4)
  else n ^ (-(1 / 2 : ℝ))

theorem upperRate_positive (n θ τ ν : ℝ) (hn : 1 < n) :
    0 < upperRate n θ τ ν := by
  unfold upperRate
  split_ifs
  · exact mul_pos (Rates.scale_pos n θ τ hn) (Real.rpow_pos_of_pos (Real.log_pos hn) _)
  · exact Real.rpow_pos_of_pos (zero_lt_one.trans hn) _

theorem subcritical_ratio_tendsto_zero (θ1 θ2 τ ν1 ν2 : ℝ)
    (hθ : θ1 < θ2) (h1 : θ1 < 1 / 2) (h2 : θ2 < 1 / 2) :
    Tendsto (fun n : ℝ => upperRate n θ2 τ ν2 / upperRate n θ1 τ ν1)
      atTop (nhds 0) := by
  have h := (UpperSubcritical.logPower_negative_exp_sqrt_tendsto_zero
    (θ2-θ1) (Rates.kappa θ1 τ-Rates.kappa θ2 τ)
    ((θ2+ν2-θ1-ν1)/2) (sub_pos.mpr hθ)).comp Real.tendsto_log_atTop
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  have hnp := zero_lt_one.trans hn
  have hLp := Real.log_pos hn
  simp only [Function.comp_apply,upperRate,if_pos h1,if_pos h2,
    Rates.subcriticalScale,Real.rpow_def_of_pos hnp,Real.rpow_def_of_pos hLp]
  repeat rw [← Real.exp_add]
  repeat rw [← Real.exp_sub]
  congr 1
  ring

theorem rootN_ratio_tendsto_zero (θ τ ν : ℝ) (hθ : θ < 1 / 2) :
    Tendsto (fun n : ℝ => n ^ (-(1/2:ℝ)) / upperRate n θ τ ν)
      atTop (nhds 0) := by
  have h := (UpperSubcritical.logPower_negative_exp_sqrt_tendsto_zero
    (1/2-θ) (Rates.kappa θ τ) (-(θ/2+ν/2+1/4)) (sub_pos.mpr hθ)).comp
    Real.tendsto_log_atTop
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  have hnp := zero_lt_one.trans hn
  have hLp := Real.log_pos hn
  simp only [Function.comp_apply,upperRate,if_pos hθ,Rates.subcriticalScale,
    Real.rpow_def_of_pos hnp,Real.rpow_def_of_pos hLp]
  repeat rw [← Real.exp_add]
  repeat rw [← Real.exp_sub]
  congr 1
  ring

theorem upperRate_ratio_tendsto_zero (θ1 θ2 τ ν1 ν2 : ℝ)
    (hθ : θ1 < θ2) (h1 : θ1 < 1 / 2) :
    Tendsto (fun n : ℝ => upperRate n θ2 τ ν2 / upperRate n θ1 τ ν1)
      atTop (nhds 0) := by
  by_cases h2 : θ2 < 1 / 2
  · exact subcritical_ratio_tendsto_zero θ1 θ2 τ ν1 ν2 hθ h1 h2
  · simpa only [upperRate,if_neg h2] using rootN_ratio_tendsto_zero θ1 τ ν1 h1

/-- A faster component and a parametric moment error are both negligible
relative to the slowest rough component. -/
theorem faster_plus_rootN_isLittleO (θ1 θ2 τ ν1 ν2 : ℝ)
    (hθ : θ1 < θ2) (h1 : θ1 < 1 / 2) :
    (fun n : ℝ => upperRate n θ2 τ ν2 + n ^ (-(1/2:ℝ)))
      =o[atTop] (fun n => upperRate n θ1 τ ν1) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
  · simpa only [zero_add,← add_div] using
      (upperRate_ratio_tendsto_zero θ1 θ2 τ ν1 ν2 hθ h1).add
        (rootN_ratio_tendsto_zero θ1 τ ν1 h1)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    exact fun hz => False.elim ((upperRate_positive n θ1 τ ν1 hn).ne' hz)

theorem upperRate_mono_nu (n θ τ ν1 ν2 : ℝ) (hn0 : 0 ≤ n)
    (hn : 1 ≤ Real.log n) (hν : ν1 ≤ ν2) :
    upperRate n θ τ ν1 ≤ upperRate n θ τ ν2 := by
  unfold upperRate
  split_ifs
  · apply mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
    unfold Rates.subcriticalScale
    positivity
  · exact le_rfl

/-- The minimum θ dominates every faster rate, and at equal θ the maximum ν
dominates. This also covers the parametric part of the piecewise definition. -/
theorem upperRate_eventually_le (θ1 θ2 τ ν1 ν2 : ℝ) (hθ : θ1 ≤ θ2)
    (hν : θ1 = θ2 → ν2 ≤ ν1) :
    ∀ᶠ n : ℝ in atTop, upperRate n θ2 τ ν2 ≤ upperRate n θ1 τ ν1 := by
  by_cases heq : θ1 = θ2
  · subst θ2
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_ge_atTop (0 : ℝ)] with n hn hn0
    exact upperRate_mono_nu n θ1 τ ν2 ν1 hn0 hn (hν rfl)
  · by_cases h1 : θ1 < 1 / 2
    · have hr := upperRate_ratio_tendsto_zero θ1 θ2 τ ν1 ν2 (lt_of_le_of_ne hθ heq) h1
      have hb := hr.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
      filter_upwards [hb,eventually_gt_atTop (1 : ℝ)] with n hn hn1
      exact ((div_lt_one (upperRate_positive n θ1 τ ν1 hn1)).mp hn).le
    · have h2 : ¬ θ2 < 1 / 2 := by intro h; exact h1 (hθ.trans_lt h)
      exact Filter.Eventually.of_forall (fun n => by
        simp only [upperRate,ite_eq_right h1,ite_eq_right h2]
        exact le_rfl)

theorem rootN_eventually_le (θ τ ν : ℝ) :
    ∀ᶠ n : ℝ in atTop, n ^ (-(1/2:ℝ)) ≤ upperRate n θ τ ν := by
  by_cases hθ : θ < 1 / 2
  · have hr := rootN_ratio_tendsto_zero θ τ ν hθ
    have hb := hr.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hb,eventually_gt_atTop (1 : ℝ)] with n hn hn1
    exact ((div_lt_one (upperRate_positive n θ τ ν hn1)).mp hn).le
  · exact Filter.Eventually.of_forall (fun n => by
      simp only [upperRate,ite_eq_right hθ]
      exact le_rfl)

/-- A finite sum of component upper rates plus a root-n moment error has the
selected minimum θ and maximum ν among the minimizing components. -/
theorem finite_rate_sum_eventually_le {ι : Type*} [Fintype ι]
    (θi νi Ci : ι → ℝ) (θ τ ν Croot : ℝ)
    (hθ : ∀ i, θ ≤ θi i) (hν : ∀ i, θ = θi i → νi i ≤ ν)
    (hC : ∀ i, 0 ≤ Ci i) (hCroot : 0 ≤ Croot) :
    ∀ᶠ n : ℝ in atTop,
      (∑ i, Ci i * upperRate n (θi i) τ (νi i)) + Croot * n ^ (-(1/2:ℝ)) ≤
      ((∑ i, Ci i) + Croot) * upperRate n θ τ ν := by
  classical
  have hall : ∀ᶠ n : ℝ in atTop, ∀ i, upperRate n (θi i) τ (νi i) ≤ upperRate n θ τ ν :=
    eventually_all.2 (fun i => upperRate_eventually_le θ (θi i) τ ν (νi i) (hθ i) (hν i))
  filter_upwards [hall,rootN_eventually_le θ τ ν] with n hn hroot
  calc
    _ ≤ (∑ i, Ci i * upperRate n θ τ ν) + Croot * upperRate n θ τ ν :=
      add_le_add (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hn i) (hC i)))
        (mul_le_mul_of_nonneg_left hroot hCroot)
    _ = _ := by rw [← Finset.sum_mul,add_mul]

end RoughRegime.RateCombination
