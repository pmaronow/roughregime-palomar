module

public import RoughRegime.ModelPredicates
public import RoughRegime.RateCombination


@[expose] public section
/-! Actual sample-halving and exponentially small pilot-error bounds in the
literal bracket rates. These numerical statements do not assume any risk. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.Applications
set_option maxHeartbeats 700000

def halfRateConstant (θ τ : ℝ) : ℝ :=
  (2:ℝ)^θ*Real.exp (Rates.kappa θ τ*Real.sqrt (Real.log 2))+(2:ℝ)^(1/2 : ℝ)

theorem halfRateConstant_pos (θ τ : ℝ) : 0 < halfRateConstant θ τ := by
  unfold halfRateConstant
  positivity

theorem negative_power_half_bound (n m s : ℝ) (hn : 0 < n) (hm : 0 < m)
    (hsize : n ≤ 2*m) (hs : 0 ≤ s) : m^(-s) ≤ (2:ℝ)^s*n^(-s) := by
  have hhalf : n/2 ≤ m := by linarith
  have he := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < n/2) hhalf (neg_nonpos.mpr hs)
  rw [Real.div_rpow hn.le (by norm_num : (0:ℝ) ≤ 2),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul] at he
  simpa only [mul_comm] using he

theorem bracket_rate_within_factor_two (n m θ τ ν : ℝ) (hm : 1 < m) (hmn : m ≤ n)
    (hsize : n ≤ 2*m) (hθ : 0 ≤ θ) (hν : 0 ≤ ν) :
    RateCombination.upperRate m θ τ ν ≤ halfRateConstant θ τ*RateCombination.upperRate n θ τ ν := by
  have hmp : 0 < m := zero_lt_one.trans hm
  have hnp : 0 < n := hmp.trans_le hmn
  have hn : 1 < n := hm.trans_le hmn
  have hLm : 0 ≤ Real.log m := (Real.log_pos hm).le
  have hLn : 0 ≤ Real.log n := (Real.log_pos hn).le
  have hκ : 0 ≤ Rates.kappa θ τ := by unfold Rates.kappa; positivity
  have hC1 : 0 < (2:ℝ)^θ*Real.exp (Rates.kappa θ τ*Real.sqrt (Real.log 2)) := by positivity
  have hC2 : 0 < (2:ℝ)^(1/2 : ℝ) := by positivity
  unfold RateCombination.upperRate
  split_ifs with hrough
  · let b := θ/2+ν/2+1/4
    have hb : 0 ≤ b := by dsimp only [b]; linarith
    have heq (x : ℝ) (hx : 1 < x) :
        Rates.subcriticalScale x θ τ*(Real.log x)^(ν/2+1/4) =
          x^(-θ)*(Real.log x)^b*Real.exp (-Rates.kappa θ τ*Real.sqrt (Real.log x)) := by
      unfold Rates.subcriticalScale b
      rw [show θ/2+ν/2+1/4 = θ/2+(ν/2+1/4) by ring,
        Real.rpow_add (Real.log_pos hx) (θ/2) (ν/2+1/4)]
      ring
    rw [heq m hm,heq n hn]
    have hp := negative_power_half_bound n m θ hnp hmp hsize hθ
    have hl := Real.rpow_le_rpow (Real.log_pos hm).le (Real.log_le_log hmp hmn) hb
    have hlog : Real.log n ≤ Real.log m+Real.log 2 := by
      have hh := Real.log_le_log hnp hsize
      rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hmp.ne'] at hh
      linarith
    have hln := Real.sq_sqrt (Real.log_pos hn).le
    have hlm := Real.sq_sqrt (Real.log_pos hm).le
    have hl2 := Real.sq_sqrt (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
    have hsqrt : Real.sqrt (Real.log n) ≤ Real.sqrt (Real.log m)+Real.sqrt (Real.log 2) := by
      nlinarith [Real.sqrt_nonneg (Real.log n),Real.sqrt_nonneg (Real.log m),Real.sqrt_nonneg (Real.log 2),
        mul_nonneg (Real.sqrt_nonneg (Real.log m)) (Real.sqrt_nonneg (Real.log 2))]
    have he : Real.exp (-Rates.kappa θ τ*Real.sqrt (Real.log m)) ≤
        Real.exp (Rates.kappa θ τ*Real.sqrt (Real.log 2))*Real.exp (-Rates.kappa θ τ*Real.sqrt (Real.log n)) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ ≤ ((2:ℝ)^θ*n^(-θ))*(Real.log n)^b*
          (Real.exp (Rates.kappa θ τ*Real.sqrt (Real.log 2))*Real.exp (-Rates.kappa θ τ*Real.sqrt (Real.log n))) := by
        gcongr <;> positivity
      _ = ((2:ℝ)^θ*Real.exp (Rates.kappa θ τ*Real.sqrt (Real.log 2)))*
          (n^(-θ)*(Real.log n)^b*Real.exp (-Rates.kappa θ τ*Real.sqrt (Real.log n))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2.le) (by positivity)
  · have hp := negative_power_half_bound n m (1/2) hnp hmp hsize (by norm_num)
    exact hp.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1.le) (by positivity))

theorem estimation_half_tendsto : Tendsto (fun n : ℕ => n-n/2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2*b+2)] with n hn
  omega

theorem pilot_half_tendsto : Tendsto (fun n : ℕ => n/2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2*b+2)] with n hn
  omega

theorem upperBracketScale_estimation_half_bound (S : Model.BracketParameters) (ν : ℝ) (hν : 0 ≤ ν)
    (n : ℕ) (hn : 4 ≤ n) :
    Model.upperBracketScale S ν (n-n/2) ≤ halfRateConstant S.theta (Rates.tau S.lo S.hi)*Model.upperBracketScale S ν n := by
  have hm : (1:ℝ) < (n-n/2:ℕ) := by exact_mod_cast (show 1 < n-n/2 by omega)
  have hmn : ((n-n/2:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (n/2)
  have hsize : (n:ℝ) ≤ 2*(n-n/2:ℕ) := by exact_mod_cast (show n ≤ 2*(n-n/2) by omega)
  exact bracket_rate_within_factor_two n (n-n/2:ℕ) S.theta (Rates.tau S.lo S.hi) ν hm hmn hsize S.htheta.le hν

theorem sqrt_pilot_tail_eventually_le_rootN (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.sqrt (c⁻¹*Real.exp (-c*(n/2:ℕ))) ≤ (n:ℝ)^(-(1/2 : ℝ)) := by
  have hlim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2) (c/8) (by positivity)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop)).const_mul (Real.sqrt c⁻¹)
  simp only [mul_zero] at hlim
  have hsmall := hlim.eventually_le_const (by norm_num : (0:ℝ) < 1)
  filter_upwards [hsmall,eventually_ge_atTop (4:ℕ)] with n hs hn
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk : (n:ℝ)/4 ≤ (n/2:ℕ) := by
    have hh : n ≤ 4*(n/2) := by omega
    have hh' : (n:ℝ) ≤ 4*(n/2:ℕ) := by exact_mod_cast hh
    linarith
  have hexp : Real.exp (-c*(n/2:ℕ)/2) ≤ Real.exp (-(c/8)*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbase : Real.sqrt c⁻¹*Real.exp (-(c/8)*(n:ℝ)) ≤ (n:ℝ)^(-(1/2:ℝ)) := by
    rw [Real.rpow_neg hnp.le]
    have hh : Real.sqrt c⁻¹*Real.exp (-(c/8)*(n:ℝ)) ≤ 1/((n:ℝ)^(1/2:ℝ)) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hnp (1/2))).mpr
      convert hs using 1 <;> simp only [Function.comp_apply] <;> ring
    simpa only [one_div] using hh
  have hsqrtExp (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  rw [Real.sqrt_mul (inv_nonneg.mpr hc.le),hsqrtExp]
  exact (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)).trans hbase

theorem sqrt_pilot_tail_eventually_le_upperBracketScale (S : Model.BracketParameters) (ν c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.sqrt (c⁻¹*Real.exp (-c*(n/2:ℕ))) ≤ Model.upperBracketScale S ν n := by
  have hroot := (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).eventually
    (RateCombination.rootN_eventually_le S.theta (Rates.tau S.lo S.hi) ν)
  filter_upwards [sqrt_pilot_tail_eventually_le_rootN c hc,hroot] with n hp hr
  exact hp.trans hr

theorem split_upperBracket_rate_bound (S : Model.BracketParameters) (ν C c : ℝ)
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ D > 0, ∀ᶠ n : ℕ in atTop,
      C*Model.upperBracketScale S ν (n-n/2)+Real.sqrt (c⁻¹*Real.exp (-c*(n/2:ℕ))) ≤
        D*Model.upperBracketScale S ν n := by
  let D := C*halfRateConstant S.theta (Rates.tau S.lo S.hi)+1
  have hD : 0 < D := by dsimp only [D]; nlinarith [halfRateConstant_pos S.theta (Rates.tau S.lo S.hi)]
  refine ⟨D,hD,?_⟩
  filter_upwards [sqrt_pilot_tail_eventually_le_upperBracketScale S ν c hc,eventually_ge_atTop (4:ℕ)] with n hp hn
  have hh := mul_le_mul_of_nonneg_left (upperBracketScale_estimation_half_bound S ν hν n hn) hC
  convert add_le_add hh hp using 1 <;> dsimp only [D] <;> ring

theorem split_parametric_rate_bound (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ D > 0, ∀ᶠ n : ℕ in atTop,
      C/Real.sqrt (n-n/2:ℕ)+Real.sqrt (c⁻¹*Real.exp (-c*(n/2:ℕ))) ≤ D/Real.sqrt n := by
  let D := C*(2:ℝ)^(1/2:ℝ)+1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D,hD,?_⟩
  filter_upwards [sqrt_pilot_tail_eventually_le_rootN c hc,eventually_ge_atTop (4:ℕ)] with n hp hn
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmp : (0:ℝ) < (n-n/2:ℕ) := by exact_mod_cast (show 0 < n-n/2 by omega)
  have hsize : (n:ℝ) ≤ 2*(n-n/2:ℕ) := by exact_mod_cast (show n ≤ 2*(n-n/2) by omega)
  have hh := mul_le_mul_of_nonneg_left (negative_power_half_bound n (n-n/2:ℕ) (1/2) hnp hmp hsize (by norm_num)) hC
  have heq (x z : ℝ) (hx : 0 ≤ x) : z/Real.sqrt x = z*x^(-(1/2:ℝ)) := by
    rw [Real.sqrt_eq_rpow,div_eq_mul_inv,Real.rpow_neg hx]
  rw [heq (n-n/2:ℕ) C hmp.le,heq n D hnp.le]
  convert add_le_add hh hp using 1 <;> dsimp only [D] <;> ring

theorem split_subcritical_rate_bound (S : Model.BracketParameters) (ν : ℕ)
    (hrough : S.theta < 1/2) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ D > 0, ∀ᶠ n : ℕ in atTop,
      C*UpperSubcritical.rate (n-n/2:ℕ) S.theta (Rates.tau S.lo S.hi) ν+
        Real.sqrt (c⁻¹*Real.exp (-c*(n/2:ℕ))) ≤ D*UpperSubcritical.rate n S.theta (Rates.tau S.lo S.hi) ν := by
  obtain ⟨D,hD,he⟩ := split_upperBracket_rate_bound S ν C c (Nat.cast_nonneg _) hC hc
  refine ⟨D,hD,?_⟩
  filter_upwards [he,eventually_ge_atTop (4:ℕ)] with n he hn
  have hnp : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hmp : (1:ℝ) < (n-n/2:ℕ) := by exact_mod_cast (show 1 < n-n/2 by omega)
  rw [UpperSubcritical.rate_eq_paper_scale _ _ _ _ hmp,UpperSubcritical.rate_eq_paper_scale _ _ _ _ hnp]
  simpa only [Model.upperBracketScale,ite_eq_left hrough] using he

end RoughRegime.Applications
