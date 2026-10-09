module

public import RoughRegime.ReductionScales


@[expose] public section
/-! The literal largest admissible hierarchical level in the rough source
construction, with its exact frequency and logarithmic budgets. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales

 def largestFineLevel (s c M : ℝ) : ℕ := Nat.floor (Real.log (c*M)/(s*Real.log 2))
 def largestFineScale (s c M : ℝ) : ℝ := (2:ℝ)^((largestFineLevel s c M:ℝ)*s)
 def largestFineVolume (d : ℕ) (s c M : ℝ) : ℝ := (2:ℝ)^(largestFineLevel s c M*d)

 theorem largestFineScale_bounds (s c M : ℝ) (hs : 0 < s) (hcM : 1 ≤ c*M) :
     largestFineScale s c M ≤ c*M ∧ c*M ≤ (2:ℝ)^s*largestFineScale s c M := by
   have hCM : 0 < c*M := zero_lt_one.trans_le hcM
   have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
   have hx : 0 ≤ Real.log (c*M)/(s*Real.log 2) := div_nonneg (Real.log_nonneg hcM) (mul_pos hs hl).le
   have hlo := Nat.floor_le hx
   have hhi := Nat.lt_floor_add_one (Real.log (c*M)/(s*Real.log 2))
   have hlo' := (le_div_iff₀ (mul_pos hs hl)).mp hlo
   have hhi' := (div_lt_iff₀ (mul_pos hs hl)).mp hhi
   have hm : 0 < largestFineScale s c M := by unfold largestFineScale; positivity
   have hlog : Real.log (largestFineScale s c M) =
       (largestFineLevel s c M:ℝ)*s*Real.log 2 := by
     unfold largestFineScale
     rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)]
   constructor
   · apply (Real.log_le_log_iff hm hCM).mp
     rw [hlog]
     simpa only [largestFineLevel, mul_assoc] using hlo'
   · apply (Real.log_le_log_iff hCM (mul_pos (by positivity) hm)).mp
     rw [Real.log_mul (by positivity : (2:ℝ)^s ≠ 0) hm.ne',Real.log_rpow (by norm_num : (0:ℝ) < 2),hlog]
     dsimp [largestFineLevel] at *
     nlinarith only [hhi']

 theorem largestFineLevel_maximal (s c M : ℝ) (hs : 0 < s) (hcM : 1 ≤ c*M)
     (J : ℕ) (hJ : (2:ℝ)^((J:ℝ)*s) ≤ c*M) : J ≤ largestFineLevel s c M := by
   have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
   apply (Nat.le_floor_iff (div_nonneg (Real.log_nonneg hcM) (mul_pos hs hl).le)).mpr
   apply (le_div_iff₀ (mul_pos hs hl)).mpr
   have he := Real.log_le_log (show 0 < (2:ℝ)^((J:ℝ)*s) by positivity) hJ
   rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)] at he
   simpa only [mul_assoc] using he

 theorem largestFineScale_level_budgets (s a b alpha0 c M : ℝ) (hs : 0 < s)
     (has : s ≤ a) (hbs : s ≤ b) (ha0 : alpha0 ≤ s) :
     (2:ℝ)^((largestFineLevel s c M:ℝ)*alpha0) ≤ largestFineScale s c M ∧
       largestFineScale s c M ≤ (2:ℝ)^((largestFineLevel s c M:ℝ)*a) ∧
       largestFineScale s c M ≤ (2:ℝ)^((largestFineLevel s c M:ℝ)*b) := by
   unfold largestFineScale
   exact ⟨Real.rpow_le_rpow_of_exponent_le (by norm_num)
     (mul_le_mul_of_nonneg_left ha0 (Nat.cast_nonneg _)),
     Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left has (Nat.cast_nonneg _)),
     Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hbs (Nat.cast_nonneg _))⟩

 theorem largestFineVolume_log_bound (d : ℕ) (s c M : ℝ) (hs : 0 < s) (hc : 0 < c)
     (hc1 : c ≤ 1) (hcM : 1 ≤ c*M) :
     0 ≤ Real.log (largestFineVolume d s c M) ∧
       Real.log (largestFineVolume d s c M) ≤ (d:ℝ)/s*Real.log M := by
   have hm := largestFineScale_bounds s c M hs hcM
   have hM : 0 < M := (pos_of_mul_pos_right (zero_lt_one.trans_le hcM) hc.le)
   have hR : 1 ≤ largestFineVolume d s c M := by unfold largestFineVolume; exact one_le_pow₀ (by norm_num)
   have hlogm := Real.log_le_log (by unfold largestFineScale; positivity) hm.1
   have hlogR : Real.log (largestFineVolume d s c M) =
       ((d:ℝ)/s)*Real.log (largestFineScale s c M) := by
     unfold largestFineVolume largestFineScale
     rw [Real.log_pow,Real.log_rpow (by norm_num : (0:ℝ) < 2)]
     push_cast
     field_simp <;> ring
   have hCM : 0 < c*M := mul_pos hc hM
   have hlogCM : Real.log (c*M) ≤ Real.log M := Real.log_le_log hCM
     (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hM.le)
   refine ⟨Real.log_nonneg hR,?_⟩
   rw [hlogR]
   exact mul_le_mul_of_nonneg_left (hlogm.trans hlogCM) (by positivity)

 def selectedFineLevel (θ τ s c : ℝ) (n : ℝ) : ℕ := largestFineLevel s c (frequency n θ τ)
 def selectedFineScale (θ τ s c : ℝ) (n : ℝ) : ℝ := largestFineScale s c (frequency n θ τ)
 def selectedFineVolume (d : ℕ) (θ τ s c : ℝ) (n : ℝ) : ℝ := largestFineVolume d s c (frequency n θ τ)

 theorem selectedFineVolume_ge_one (d : ℕ) (θ τ s c : ℝ) (n : ℝ) : 1 ≤ selectedFineVolume d θ τ s c n := by
   unfold selectedFineVolume largestFineVolume
   exact one_le_pow₀ (by norm_num)

 theorem selectedFineVolume_log_isBigO (d : ℕ) (θ τ s c : ℝ)
     (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1) :
     (fun n => Real.log (selectedFineVolume d θ τ s c n)) =O[atTop]
       (fun n => Real.log (frequency n θ τ)) := by
   have he := (frequency_tendsto θ τ hθ hθhalf hτ).eventually_ge_atTop (1/c)
   apply Asymptotics.IsBigO.of_bound (d/s)
   filter_upwards [he] with n hn
   have hCM : 1 ≤ c*(frequency n θ τ:ℝ) := by
     have hh := mul_le_mul_of_nonneg_left hn hc.le
     field_simp at hh
     nlinarith only [hh]
   have hh := largestFineVolume_log_bound d s c (frequency n θ τ) hs hc hc1 hCM
   change ‖Real.log (largestFineVolume d s c (frequency n θ τ))‖ ≤ _
   rw [Real.norm_eq_abs,abs_of_nonneg hh.1,Real.norm_eq_abs]
   exact hh.2.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

end RoughRegime.LatticePriors
