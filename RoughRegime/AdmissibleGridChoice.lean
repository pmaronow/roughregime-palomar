module

public import RoughRegime.ReductionNaturalScales


@[expose] public section
/-! The numerical block choice is literally an even-side grid and eventually
satisfies the original universal grid-existence hypothesis. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.ReductionScales.NaturalScaleChoice
set_option maxHeartbeats 800000
variable {A : AbstractScaleParameters} (S : NaturalScaleChoice A)

 theorem grid_power (n : ℕ) : ∃k:ℕ,Even k ∧ S.B n=k^A.d := by
   rw [S.B_eq_selected]
   refine ⟨evenCeiling (idealSideLength n (S.R n) (logResolution n A.theta A.tau A.c0) A.d),?_,rfl⟩
   unfold evenCeiling
   exact even_two.mul_right _

 theorem grid_even (n : ℕ) : Even (S.B n) := by
   obtain ⟨k,hk,hB⟩ := S.grid_power n
   rw [hB]
   exact hk.pow_of_ne_zero A.hd.ne'

 theorem grid_double_half (n : ℕ) : 2*(S.B n/2)=S.B n := by
   have hdiv : 2∣S.B n := even_iff_two_dvd.mp (S.grid_even n)
   exact Nat.mul_div_cancel' hdiv

 theorem block_eventually_ge_sample : ∀ᶠ n:ℕ in atTop,n ≤ S.B n := by
   have h := (S.block_superlog 0).eventually_ge_atTop 1
   filter_upwards [h,eventually_gt_atTop (0:ℕ)] with n hn hnp
   have hnreal : (0:ℝ)<n := by exact_mod_cast hnp
   simp only [Real.rpow_zero,mul_one] at hn
   exact_mod_cast (one_le_div hnreal).mp hn

 theorem grid_half_eventually_pos : ∀ᶠ n:ℕ in atTop,0<S.B n/2 := by
   filter_upwards [S.block_eventually_ge_sample,eventually_ge_atTop (2:ℕ)] with n hB hn
   exact Nat.div_pos (hn.trans hB) (by norm_num)


end RoughRegime.ReductionScales.NaturalScaleChoice
