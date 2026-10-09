module

public import RoughRegime.SourceConcentration
public import RoughRegime.TaylorSeparationScales


@[expose] public section
/-! The original selected amplitudes satisfy the sample envelopes and the
actual nonlinear Taylor remainder is negligible at the true narrowed gap. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales
set_option maxHeartbeats 800000

 theorem selectedSourceAmplitude_sample_bound (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 epsilon : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (hε : 0 < epsilon) (hε1 : epsilon ≤ 1) :
     (∀ᶠ n : ℝ in atTop, |selectedSourceAmplitude A d θ τ c0 epsilon A.α n| ≤ n^(-(A.α/d))) ∧
     (∀ᶠ n : ℝ in atTop, |selectedSourceAmplitude A d θ τ c0 epsilon A.β n| ≤ n^(-(A.β/d))) := by
   have hR := selectedSourceVolume_log_isBigO A d hd θ τ hθ hθhalf hτ
   have hRpos : ∀ᶠ n : ℝ in atTop, 1 ≤ selectedSourceVolume A d θ τ n :=
     Eventually.of_forall (selectedSourceVolume_ge_one A d θ τ)
   have hu := selected_amplitude_eventually_le_sample θ τ c0 epsilon (A.α/d)
     hθ hθhalf hτ hε.le hε1 (div_nonneg A.hα.le (Nat.cast_nonneg _))
     (selectedSourceVolume A d θ τ) (selectedSourceMultiplier A d θ τ) hRpos hR
     (Eventually.of_forall (fun n => (selectedSourceMultiplier_volume_budgets A d hd θ τ n).1)) d hd
   have hv := selected_amplitude_eventually_le_sample θ τ c0 epsilon (A.β/d)
     hθ hθhalf hτ hε.le hε1 (div_nonneg A.hβ.le (Nat.cast_nonneg _))
     (selectedSourceVolume A d θ τ) (selectedSourceMultiplier A d θ τ) hRpos hR
     (Eventually.of_forall (fun n => (selectedSourceMultiplier_volume_budgets A d hd θ τ n).2)) d hd
   have habs (n : ℝ) (hn : 0 < n) (t : ℝ) :
       0 ≤ selectedSourceAmplitude A d θ τ c0 epsilon t n := by
     have hRn : 0 < selectedSourceVolume A d θ τ n := zero_lt_one.trans_le (selectedSourceVolume_ge_one A d θ τ n)
     have hBn : 0 < (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) := by
       unfold selectedBlockCount
       exact_mod_cast blockCount_positive n _ _ d hn hRn
     exact (amplitude_positive epsilon _ _ _ _ hε hBn hRn
       (zero_lt_one.trans_le (selectedSourceMultiplier_ge_one A d θ τ n))).le
   refine ⟨?_,?_⟩
   · filter_upwards [hu,eventually_gt_atTop (0 : ℝ)] with n hn hnp
     rw [abs_of_nonneg (habs n hnp A.α)]
     exact hn
   · filter_upwards [hv,eventually_gt_atTop (0 : ℝ)] with n hn hnp
     rw [abs_of_nonneg (habs n hnp A.β)]
     exact hn

 theorem selectedSourceTaylorErrorRatio_tendsto_zero (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ c0 epsilonU epsilonV lo hi : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2)
     (hεu : 0 < epsilonU) (hεu1 : epsilonU ≤ 1) (hεv : 0 < epsilonV) (hεv1 : epsilonV ≤ 1)
     (hlo : 0 < lo) (hlt : lo < hi) :
     Tendsto (fun n : ℝ =>
       ((selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU A.α n)^2 +
        (selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonV A.β n)^2) /
        (Upper.narrowedRho lo hi ((Real.log n)^(-2 : ℝ)))^(frequency n θ (RoughRegime.Rates.tau lo hi)))
       atTop (nhds 0) := by
   have hτ := RoughRegime.Rates.tau_pos lo hi hlo hlt
   exact nonlinear_remainder_ratio_tendsto θ (RoughRegime.Rates.tau lo hi) (A.α/d) (A.β/d) lo hi
     hθ hθhalf hτ (div_pos A.hα (Nat.cast_pos.mpr hd)) (div_pos A.hβ (Nat.cast_pos.mpr hd)) hlo hlt
     (selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU A.α)
     (selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonV A.β)
     (selectedSourceAmplitude_sample_bound A d hd θ _ c0 epsilonU hθ hθhalf hτ hεu hεu1).1
     (selectedSourceAmplitude_sample_bound A d hd θ _ c0 epsilonV hθ hθhalf hτ hεv hεv1).2

 theorem selectedSource_scaled_TaylorError_gapRatio_tendsto_zero
     (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ c0 epsilonU epsilonV lo hi C : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2)
     (hεu : 0 < epsilonU) (hεu1 : epsilonU ≤ 1) (hεv : 0 < epsilonV) (hεv1 : epsilonV ≤ 1)
     (hlo : 0 < lo) (hlt : lo < hi) :
     Tendsto (fun n : ℝ =>
       C * selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU A.α n *
         selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonV A.β n *
       ((selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU A.α n)^2 +
        (selectedSourceAmplitude A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonV A.β n)^2) /
       selectedSourceGapScale A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU epsilonV lo hi n)
       atTop (nhds 0) := by
   let τ := RoughRegime.Rates.tau lo hi
   have he := (selectedSourceTaylorErrorRatio_tendsto_zero A d hd θ c0 epsilonU epsilonV lo hi
     hθ hθhalf hεu hεu1 hεv hεv1 hlo hlt).const_mul C
   simp only [mul_zero] at he
   apply Filter.Tendsto.congr' _ he
   filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
   have hR : 0 < selectedSourceVolume A d θ τ n := zero_lt_one.trans_le (selectedSourceVolume_ge_one A d θ τ n)
   have hB : 0 < (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) := by
     unfold selectedBlockCount
     exact_mod_cast blockCount_positive n _ _ d (zero_lt_one.trans hn) hR
   have hu : selectedSourceAmplitude A d θ τ c0 epsilonU A.α n ≠ 0 :=
     (amplitude_positive epsilonU _ _ _ _ hεu hB hR (zero_lt_one.trans_le (selectedSourceMultiplier_ge_one A d θ τ n))).ne'
   have hv : selectedSourceAmplitude A d θ τ c0 epsilonV A.β n ≠ 0 :=
     (amplitude_positive epsilonV _ _ _ _ hεv hB hR (zero_lt_one.trans_le (selectedSourceMultiplier_ge_one A d θ τ n))).ne'
   unfold selectedSourceGapScale
   dsimp only [τ] at hu hv
   by_cases hρ : (Upper.narrowedRho lo hi ((Real.log n)^(-2 : ℝ)))^(frequency n θ (RoughRegime.Rates.tau lo hi)) = 0
   · simp only [hρ,mul_zero,div_zero]
   · field_simp [hu,hv,hρ]

end RoughRegime.LatticePriors
