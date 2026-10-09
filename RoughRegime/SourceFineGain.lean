module

public import RoughRegime.SourceFineResolution
public import RoughRegime.ReductionAmplitudes


@[expose] public section
/-! The genuine logarithmic gain from the largest source hierarchy level,
and its consequence for the actual rounded-block amplitude product. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales

 theorem selectedFineScale_sq_log_bounds (θ τ s c : ℝ)
     (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hs : 0 < s) (hc : 0 < c) :
     ∃ CL > 0, ∃ CU > 0, ∀ᶠ n : ℝ in atTop,
       CL*Real.log n ≤ (selectedFineScale θ τ s c n)^2 ∧
       (selectedFineScale θ τ s c n)^2 ≤ CU*Real.log n := by
   let k := θ*(1-2*θ)/τ
   have hk : 0 < k := by
     dsimp [k]
     have : 0 < 1-2*θ := by linarith
     positivity
   let A := (2:ℝ)^s
   have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
   let CL := (c/A)^2*(k/2)
   let CU := c^2*(2*k)
   have hCL : 0 < CL := by dsimp [CL]; positivity
   have hCU : 0 < CU := by dsimp [CU]; positivity
   refine ⟨CL,hCL,CU,hCU,?_⟩
   have hM := frequency_tendsto θ τ hθ hθhalf hτ
   have hq := frequency_sq_log_tendsto θ τ hθ hθhalf hτ
   have hlo := hq.eventually (Ioi_mem_nhds (show k/2 < k by linarith))
   have hhi := hq.eventually (Iio_mem_nhds (show k < 2*k by linarith))
   filter_upwards [hM.eventually_ge_atTop (1/c),hlo,hhi,eventually_gt_atTop (1:ℝ)] with n hMn hln hhn hn
   have hlog : 0 < Real.log n := Real.log_pos hn
   have hCM : 1 ≤ c*(frequency n θ τ:ℝ) := by
     have hh := (div_le_iff₀ hc).mp hMn
     nlinarith only [hh]
   have hb := largestFineScale_bounds s c (frequency n θ τ) hs hCM
   have hm : 0 < selectedFineScale θ τ s c n := by
     unfold selectedFineScale largestFineScale
     positivity
   have hMp : 0 < (frequency n θ τ:ℝ) := (pos_of_mul_pos_right (zero_lt_one.trans_le hCM) hc.le)
   have hml : (c/A)*(frequency n θ τ:ℝ) ≤ selectedFineScale θ τ s c n := by
     have hh : c*(frequency n θ τ:ℝ)/A ≤ selectedFineScale θ τ s c n :=
       (div_le_iff₀ hA).mpr (by simpa only [A,selectedFineScale,mul_comm] using hb.2)
     convert hh using 1 <;> ring
   have hmu : selectedFineScale θ τ s c n ≤ c*(frequency n θ τ:ℝ) := hb.1
   have hlM : (k/2)*Real.log n ≤ (frequency n θ τ:ℝ)^2 :=
     (le_div_iff₀ hlog).mp hln.le
   have huM : (frequency n θ τ:ℝ)^2 ≤ (2*k)*Real.log n :=
     (div_le_iff₀ hlog).mp hhn.le
   constructor
   · calc
       CL*Real.log n = (c/A)^2*((k/2)*Real.log n) := by dsimp [CL]; ring
       _ ≤ (c/A)^2*(frequency n θ τ:ℝ)^2 := mul_le_mul_of_nonneg_left hlM (sq_nonneg _)
       _ = ((c/A)*(frequency n θ τ:ℝ))^2 := by ring
       _ ≤ (selectedFineScale θ τ s c n)^2 := by nlinarith [mul_pos (div_pos hc hA) hMp]
   · calc
       (selectedFineScale θ τ s c n)^2 ≤ (c*(frequency n θ τ:ℝ))^2 := by nlinarith [mul_pos hc hMp]
       _ = c^2*(frequency n θ τ:ℝ)^2 := by ring
       _ ≤ c^2*((2*k)*Real.log n) := mul_le_mul_of_nonneg_left huM (sq_nonneg _)
       _ = CU*Real.log n := by dsimp [CU]; ring

 theorem selected_fine_amplitude_product_eventually_lower
     (θ τ c0 εu εv a b s c : ℝ) (d : ℕ)
     (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (hεu : 0 < εu) (hεv : 0 < εv) (hab : a+b=θ)
     (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 0 < d) :
     ∃ C > 0, ∀ᶠ n : ℝ in atTop,
       C*Real.log n*RoughRegime.Rates.subcriticalScale n θ τ ≤
       amplitude εu (selectedBlockCount θ τ c0 (selectedFineVolume d θ τ s c) d n)
         (selectedFineVolume d θ τ s c n) a (selectedFineScale θ τ s c n) *
       amplitude εv (selectedBlockCount θ τ c0 (selectedFineVolume d θ τ s c) d n)
         (selectedFineVolume d θ τ s c n) b (selectedFineScale θ τ s c n) *
         Real.exp (-τ*frequency n θ τ) := by
   obtain ⟨CL,hCL,CU,hCU,hgain⟩ := selectedFineScale_sq_log_bounds θ τ s c hθ hθhalf hτ hs hc
   let K := εu*εv*separationConstant θ τ c0/2
   have hK : 0 < K := by dsimp [K]; exact div_pos (mul_pos (mul_pos hεu hεv)
     (separationConstant_positive θ τ c0 hθ hθhalf hτ)) (by norm_num)
   have hprod := selected_amplitude_product_eventually_lower θ τ c0 εu εv a b hθ hθhalf hτ
     hεu.le hεv.le hab (selectedFineVolume d θ τ s c) (selectedFineScale θ τ s c)
     (Eventually.of_forall (selectedFineVolume_ge_one d θ τ s c))
     (selectedFineVolume_log_isBigO d θ τ s c hθ hθhalf hτ hs hc hc1) d hd
   refine ⟨K*CL,mul_pos hK hCL,?_⟩
   filter_upwards [hgain,hprod,eventually_gt_atTop (1:ℝ)] with n hn hp hnp
   calc
     (K*CL)*Real.log n*RoughRegime.Rates.subcriticalScale n θ τ =
       K*(CL*Real.log n)*RoughRegime.Rates.subcriticalScale n θ τ := by ring
     _ ≤ K*(selectedFineScale θ τ s c n)^2*RoughRegime.Rates.subcriticalScale n θ τ := by
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn.1 hK.le)
         (RoughRegime.Rates.scale_pos n θ τ hnp).le
     _ ≤ _ := hp

end RoughRegime.LatticePriors
