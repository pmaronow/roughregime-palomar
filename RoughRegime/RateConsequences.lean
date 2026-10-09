module

public import RoughRegime.Rates


@[expose] public section
/-! Asymptotic consequences of the numerical risk bracket in Remark 1.
The bracket is an explicit hypothesis here; this module does not prove the
main minimax theorem. -/

noncomputable section
open Filter Asymptotics

namespace RoughRegime.RateConsequences
open RoughRegime.Rates

theorem log_refinement_of_bracket (R : ℝ → ℝ) (θ τ ν c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ n in atTop,
      c * subcriticalScale n θ τ * Real.log n ≤ R n ∧
      R n ≤ C * subcriticalScale n θ τ * (Real.log n) ^ (ν / 2 + 1 / 4)) :
    (fun n ↦ Real.log (R n) + θ * Real.log n + kappa θ τ * Real.sqrt (Real.log n))
      =O[atTop] (fun n ↦ Real.log (Real.log n)) := by
  let a := θ / 2 + 1
  let b := θ / 2 + ν / 2 + 1 / 4
  let M := |Real.log c| + |Real.log C| + |a| + |b|
  apply isBigO_iff.mpr
  refine ⟨M, ?_⟩
  have hloglog : ∀ᶠ n : ℝ in atTop, 1 ≤ Real.log (Real.log n) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ), hloglog] with n hn hn1 hll
  obtain ⟨hl, hu⟩ := log_bracket n θ τ ν c C (R n) hn1 hc hC hn.1 hn.2
  have hlow : Real.log c + a * Real.log (Real.log n) ≤
      Real.log (R n) + θ * Real.log n + kappa θ τ * Real.sqrt (Real.log n) := by
    dsimp [a]
    linarith
  have hupp : Real.log (R n) + θ * Real.log n + kappa θ τ * Real.sqrt (Real.log n) ≤
      Real.log C + b * Real.log (Real.log n) := by
    dsimp [b]
    linarith
  have hL : 0 ≤ Real.log (Real.log n) := by linarith
  have hca : -(|Real.log c| + |a|) * Real.log (Real.log n) ≤
      Real.log c + a * Real.log (Real.log n) := by
    have hc0 := neg_abs_le (Real.log c)
    have ha0 := neg_abs_le a
    nlinarith [abs_nonneg (Real.log c),
      mul_le_mul_of_nonneg_right ha0 hL]
  have hCb : Real.log C + b * Real.log (Real.log n) ≤
      (|Real.log C| + |b|) * Real.log (Real.log n) := by
    have hc0 := le_abs_self (Real.log C)
    have hb0 := le_abs_self b
    nlinarith [abs_nonneg (Real.log C),
      mul_le_mul_of_nonneg_right hb0 hL]
  have hMa : |Real.log c| + |a| ≤ M := by
    dsimp [M]
    linarith [abs_nonneg (Real.log C), abs_nonneg b]
  have hMb : |Real.log C| + |b| ≤ M := by
    dsimp [M]
    linarith [abs_nonneg (Real.log c), abs_nonneg a]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL]
  apply abs_le.mpr
  constructor
  · nlinarith [hlow, hca, mul_le_mul_of_nonneg_right hMa hL]
  · exact hupp.trans (hCb.trans (mul_le_mul_of_nonneg_right hMb hL))

theorem scale_ratio_diverges (R : ℝ → ℝ) (θ τ c : ℝ) (hc : 0 < c)
    (hl : ∀ᶠ n in atTop, c * subcriticalScale n θ τ * Real.log n ≤ R n) :
    Tendsto (fun n ↦ R n / subcriticalScale n θ τ) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hlog : ∀ᶠ n : ℝ in atTop, B / c ≤ Real.log n :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (B / c))
  filter_upwards [hl, eventually_gt_atTop (1 : ℝ), hlog] with n hn hn1 hln
  have hs := scale_pos n θ τ hn1
  have hBc : B ≤ c * Real.log n := by
    exact (div_le_iff₀ hc).mp hln |>.trans_eq (mul_comm _ _)
  apply (le_div_iff₀ hs).mpr
  calc
    B * subcriticalScale n θ τ ≤ c * Real.log n * subcriticalScale n θ τ :=
      mul_le_mul_of_nonneg_right hBc hs.le
    _ = c * subcriticalScale n θ τ * Real.log n := by ring
    _ ≤ R n := hn

end RoughRegime.RateConsequences
