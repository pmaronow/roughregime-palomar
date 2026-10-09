module

public import RoughRegime.Upper


@[expose] public section
/-! Stability of the spectral ratio under a shrinking density margin. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

def narrowedRho (lo hi δ : ℝ) : ℝ := intervalRho (lo + δ) (hi - δ)

theorem narrowedRho_differentiableAt (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    DifferentiableAt ℝ (narrowedRho lo hi) 0 := by
  have hh : DifferentiableAt ℝ (fun δ : ℝ => Real.sqrt (hi - δ)) 0 :=
    ((differentiableAt_const hi).sub differentiableAt_id).sqrt (by simpa using (hlo.trans hlt).ne')
  have hl : DifferentiableAt ℝ (fun δ : ℝ => Real.sqrt (lo + δ)) 0 :=
    ((differentiableAt_const lo).add differentiableAt_id).sqrt (by simpa using hlo.ne')
  have hd : Real.sqrt hi + Real.sqrt lo ≠ 0 :=
    (add_pos (Real.sqrt_pos.mpr (hlo.trans hlt)) (Real.sqrt_pos.mpr hlo)).ne'
  unfold narrowedRho intervalRho
  exact (hh.sub hl).div (hh.add hl) (by simpa using hd)

theorem narrowedRho_log_isBigO (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    (fun δ => Real.log (narrowedRho lo hi δ) - Real.log (intervalRho lo hi)) =O[𝓝 0]
      (fun δ : ℝ => δ) := by
  have hρ : narrowedRho lo hi 0 ≠ 0 := by
    simpa [narrowedRho] using (intervalRho_pos lo hi hlo hlt).ne'
  simpa [narrowedRho] using
    ((narrowedRho_differentiableAt lo hi hlo hlt).log hρ).isBigO_sub

/-- The exact spectral penalty changes by a factor tending to one whenever
frequency times the shrinking density margin tends to zero. -/
theorem narrowedRho_power_ratio_tendsto {ι : Type*} (l : Filter ι)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (δ : ι → ℝ) (M : ι → ℕ)
    (hδ : Tendsto δ l (𝓝 0)) (hMδ : Tendsto (fun i => (M i : ℝ) * δ i) l (𝓝 0)) :
    Tendsto (fun i => narrowedRho lo hi (δ i) ^ M i / intervalRho lo hi ^ M i) l (𝓝 1) := by
  have hlog := (narrowedRho_log_isBigO lo hi hlo hlt).comp_tendsto hδ
  obtain ⟨C, hC, hbound⟩ := hlog.exists_pos
  have hB := hbound.bound
  have hzero : Tendsto (fun i => (M i : ℝ) *
      (Real.log (narrowedRho lo hi (δ i)) - Real.log (intervalRho lo hi))) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (g := fun i => C * |(M i : ℝ) * δ i|)
    · exact Filter.Eventually.of_forall fun i => norm_nonneg _
    · filter_upwards [hB] with i hi'
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (M i : ℝ) * (C * |δ i|) := mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hi') (Nat.cast_nonneg _)
        _ = C * |(M i : ℝ) * δ i| := by
          rw [abs_mul, show |(M i : ℝ)| = (M i : ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
          ring
    · simpa using tendsto_const_nhds.mul hMδ.abs
  have hpos : ∀ᶠ i in l, 0 < narrowedRho lo hi (δ i) :=
    ((narrowedRho_differentiableAt lo hi hlo hlt).continuousAt.tendsto.comp hδ).eventually
      (eventually_gt_nhds (by simpa [narrowedRho] using intervalRho_pos lo hi hlo hlt))
  have hρ := intervalRho_pos lo hi hlo hlt
  have heq : (fun i => narrowedRho lo hi (δ i) ^ M i / intervalRho lo hi ^ M i) =ᶠ[l]
      fun i => Real.exp ((M i : ℝ) *
        (Real.log (narrowedRho lo hi (δ i)) - Real.log (intervalRho lo hi))) := by
    filter_upwards [hpos] with i hi'
    rw [mul_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hi', Real.exp_log hρ]
  exact Filter.Tendsto.congr' heq.symm (by
    simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.continuousAt.tendsto.comp hzero))

end RoughRegime.Upper
