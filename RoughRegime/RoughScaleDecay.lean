module

public import RoughRegime.ModelPredicates
public import RoughRegime.ReductionTestingScale


@[expose] public section
/-! The genuine rough lower bracket dominates the parametric squared scale. -/
noncomputable section
open Filter
namespace RoughRegime.Model

theorem rough_lowerBracket_squared_sample_tendsto (S : BracketParameters)
    (hrough : S.theta < 1/2) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ)*(c*lowerBracketScale S n)^2) atTop atTop := by
  have h := (ReductionScales.subcritical_testing_scale_tendsto S.theta (Rates.tau S.lo S.hi) hrough).comp
    (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop)
  have hc2 : 0 < c^2 := pow_pos hc 2
  have h' := h.const_mul_atTop hc2
  refine tendsto_atTop_mono' atTop ?_ h'
  filter_upwards [(Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop)).eventually_ge_atTop 1]
    with n hn
  simp only [lowerBracketScale,if_pos hrough]
  have hp : 1 ≤ (Real.log n)^2 := one_le_pow₀ hn
  calc
    c^2*((n : ℝ)*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi)^2) =
        (n : ℝ)*(c*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi))^2 := by ring
    _ ≤ (n : ℝ)*(c*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi))^2*(Real.log n)^2 :=
      le_mul_of_one_le_right (by positivity) hp
    _ = _ := by ring

end RoughRegime.Model
