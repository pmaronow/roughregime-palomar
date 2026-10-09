module

public import RoughRegime.SincDecay


@[expose] public section
noncomputable section
open Filter Asymptotics

namespace RoughRegime.LatticeFourier

/-- Nonzero rescaling preserves quadratic decay at infinity. -/
theorem isBigO_quadratic_rescale {f : ℝ → ℂ}
    (hf : IsBigO (cocompact ℝ) f (fun x : ℝ => |x| ^ (-(2 : ℝ))))
    {h : ℝ} (hh : h ≠ 0) :
    IsBigO (cocompact ℝ) (fun x => f (h * x))
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  have hc := hf.comp_tendsto (Filter.tendsto_cocompact_mul_left₀ hh)
  obtain ⟨C, hC⟩ := isBigO_iff.mp hc
  apply IsBigO.of_bound (C * |h| ^ (-(2 : ℝ)))
  filter_upwards [hC] with x hx
  have he : |h * x| ^ (-(2 : ℝ)) =
      |h| ^ (-(2 : ℝ)) * |x| ^ (-(2 : ℝ)) := by
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  simpa only [Function.comp_apply, he, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _),
    mul_assoc] using hx

/-- A compactly supported function satisfies every asymptotic decay bound. -/
theorem hasCompactSupport_isBigO {f : ℝ → ℂ} (hf : HasCompactSupport f) (g : ℝ → ℝ) :
    IsBigO (cocompact ℝ) f g := by
  apply IsBigO.of_bound 0
  filter_upwards [hf.isCompact.compl_mem_cocompact] with x hx
  rw [image_eq_zero_of_notMem_tsupport hx]
  simp

end RoughRegime.LatticeFourier
