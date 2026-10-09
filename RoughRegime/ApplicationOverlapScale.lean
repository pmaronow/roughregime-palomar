module

public import RoughRegime.RateCombination


@[expose] public section
/-! The cubic overlap-ratio error is polynomially smaller than the literal
rough lower scale, including its logarithmic gain. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.Applications.Overlap

 theorem polynomial_over_lowerScale_tendsto_zero (θ τ δ : ℝ) (hδ : 0<δ) :
    Tendsto (fun n : ℝ=>n^(-(θ+δ))/(Rates.subcriticalScale n θ τ*Real.log n)) atTop (𝓝 0) := by
  have h := (UpperSubcritical.logPower_negative_exp_sqrt_tendsto_zero δ (Rates.kappa θ τ)
    (-(θ/2+1)) hδ).comp Real.tendsto_log_atTop
  apply Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (1:ℝ)] with n hn
  have hnp:=zero_lt_one.trans hn
  have hlp:=Real.log_pos hn
  simp only [Function.comp_apply,Rates.subcriticalScale,Real.rpow_def_of_pos hnp,Real.rpow_def_of_pos hlp]
  rw [← Real.rpow_one (Real.log n),Real.rpow_def_of_pos hlp]
  repeat rw [← Real.exp_add]
  repeat rw [← Real.exp_sub]
  simp only [Real.log_exp]
  congr 1;ring
 def independentErrorEnvelope (α β r : ℝ) (d n : ℕ) : ℝ:=
  8*((n:ℝ)^(-(α/(d:ℝ)))/r)^3*((n:ℝ)^(-(β/(d:ℝ)))/r)
 theorem independentErrorEnvelope_relative (α β r τ c : ℝ) (d : ℕ)
    (hα : 0<α) (hd : 0<d) (hc : c≠0) :
    Tendsto (fun n : ℕ=>independentErrorEnvelope α β r d n/
      (c*Rates.subcriticalScale n ((α+β)/d) τ*Real.log n)) atTop (𝓝 0) := by
  have hdr : 0<(d:ℝ):=by exact_mod_cast hd
  have h := (polynomial_over_lowerScale_tendsto_zero ((α+β)/d) τ (2*α/d) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  have h' := h.const_mul (8/(r^4*c))
  simp only [mul_zero] at h'
  apply Tendsto.congr' _ h'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnp : 0<(n:ℝ):=by exact_mod_cast hn
  unfold independentErrorEnvelope
  have hp : ((n:ℝ)^(-(α/(d:ℝ))))^3*(n:ℝ)^(-(β/(d:ℝ)))=
      (n:ℝ)^(-(((α+β)/d)+(2*α/d))) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hnp.le,← Real.rpow_add hnp]
    congr 1;ring
  simp only [Function.comp_apply,div_pow]
  by_cases hr : r=0
  · simp [hr]
  · rw [mul_comm c (Rates.subcriticalScale _ _ _)]
    rw [← hp]
    field_simp

end RoughRegime.Applications.Overlap
