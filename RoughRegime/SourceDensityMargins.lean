module

public import RoughRegime.SourceAmplitudeGrid


@[expose] public section
/-! The paper's shrinking density margin is positive, vanishes, and is
asymptotically larger than every negative power of the sample size. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors

 def sourceDensityMargin (n : ℕ) : ℝ := (Real.log (n:ℝ))^(-(2:ℝ))

 theorem sourceDensityMargin_pos (n : ℕ) (hn : 1 < n) : 0 < sourceDensityMargin n := by
   unfold sourceDensityMargin
   exact Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hn)) _

 theorem sourceDensityMargin_tendsto : Tendsto sourceDensityMargin atTop (𝓝 0) :=
   (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 2)).comp
     (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

 theorem polynomial_div_sourceDensityMargin_tendsto (t : ℝ) (ht : 0 < t) :
     Tendsto (fun n : ℕ => (n:ℝ)^(-t)/sourceDensityMargin n) atTop (𝓝 0) := by
   have he := ((isLittleO_log_rpow_rpow_atTop (2:ℝ) ht).tendsto_div_nhds_zero).comp
     tendsto_natCast_atTop_atTop
   apply he.congr'
   filter_upwards [eventually_gt_atTop 1] with n hn
   have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
   have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
   dsimp only [Function.comp_apply,sourceDensityMargin]
   rw [Real.rpow_neg hn0.le,Real.rpow_neg hl.le]
   field_simp

 theorem eventually_polynomial_le_sourceDensityMargin (C t κ : ℝ) (ht : 0 < t) (hκ : 0 < κ) :
     ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^(-t) ≤ κ*sourceDensityMargin n := by
   have he : Tendsto (fun n : ℕ => C*((n:ℝ)^(-t)/sourceDensityMargin n)) atTop (𝓝 0) := by
     simpa only [mul_zero] using (polynomial_div_sourceDensityMargin_tendsto t ht).const_mul C
   filter_upwards [he.eventually (Iio_mem_nhds hκ),eventually_gt_atTop 1] with n hn hn1
   have hm := sourceDensityMargin_pos n hn1
   apply (div_le_iff₀ hm).mp
   simpa only [mul_div_assoc] using hn.le

end RoughRegime.LatticePriors
