module

public import RoughRegime.Rates


@[expose] public section
/-! Exact invariance of the reciprocal approximation parameter under the
response denominator's positive baseline normalization. -/
noncomputable section
namespace RoughRegime.Rates

theorem rho_div (lo hi w : ℝ) (hw : 0 < w) : rho (lo/w) (hi/w) = rho lo hi := by
  unfold rho
  rw [Real.sqrt_div' hi hw.le,Real.sqrt_div' lo hw.le]
  have hsw : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  rw [← sub_div,← add_div,div_div_div_cancel_right₀ hsw]

theorem tau_div (lo hi w : ℝ) (hw : 0 < w) : tau (lo/w) (hi/w) = tau lo hi := by
  unfold tau
  rw [rho_div lo hi w hw]

end RoughRegime.Rates
