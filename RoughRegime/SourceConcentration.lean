module

public import RoughRegime.SourcePoissonBudgets
public import RoughRegime.RhoPerturbation
public import RoughRegime.ReductionTestingScale


@[expose] public section
/-! Actual selected source target gaps dominate the logarithmically improved
lower scale, and the derived 1/B prior variance is negligible at that gap. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales
set_option maxHeartbeats 800000

 def selectedSourceGapScale (A : Model.Parameters) (d : ℕ)
     (θ τ c0 epsilonU epsilonV lo hi n : ℝ) : ℝ :=
   selectedSourceAmplitude A d θ τ c0 epsilonU A.α n *
     selectedSourceAmplitude A d θ τ c0 epsilonV A.β n *
     (Upper.narrowedRho lo hi ((Real.log n)^(-2 : ℝ)))^(frequency n θ τ)

 theorem rho_power_eq_exp_tau (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : ℕ) :
     Upper.intervalRho lo hi ^ M = Real.exp (-RoughRegime.Rates.tau lo hi * M) := by
   have hρ : 0 < RoughRegime.Rates.rho lo hi := RoughRegime.Rates.rho_pos lo hi hlo hlt
   change RoughRegime.Rates.rho lo hi ^ M = _
   unfold RoughRegime.Rates.tau
   rw [neg_neg,mul_comm,Real.exp_nat_mul,Real.exp_log hρ]

 theorem selectedSourceGapScale_eventually_log_lower (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ c0 epsilonU epsilonV lo hi : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2)
     (hεu : 0 < epsilonU) (hεv : 0 < epsilonV) (hlo : 0 < lo) (hlt : lo < hi)
     (hab : A.α/d + A.β/d = θ) :
     ∃ C > 0, ∀ᶠ n : ℝ in atTop,
       C * Real.log n * RoughRegime.Rates.subcriticalScale n θ (RoughRegime.Rates.tau lo hi) ≤
         selectedSourceGapScale A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU epsilonV lo hi n := by
   let τ := RoughRegime.Rates.tau lo hi
   have hτ := RoughRegime.Rates.tau_pos lo hi hlo hlt
   obtain ⟨C,hC,hprod⟩ := selectedSource_product_log_gain A d hd θ τ c0 epsilonU epsilonV
     hθ hθhalf hτ hεu hεv hab
   have hratio := Upper.narrowedRho_power_ratio_tendsto atTop lo hi hlo hlt
     (fun n : ℝ => (Real.log n)^(-2 : ℝ)) (fun n => frequency n θ τ)
     logarithmicMargin_tendsto_zero (frequencyTimesMargin_tendsto_zero θ τ hθ hθhalf hτ)
   have hhalf := hratio.eventually_const_le (by norm_num : (1/2 : ℝ) < 1)
   refine ⟨C/2,by positivity,?_⟩
   filter_upwards [hprod,hhalf,eventually_gt_atTop (1 : ℝ)] with n hp hr hn
   have hnp : 0 < n := zero_lt_one.trans hn
   have hR : 0 < selectedSourceVolume A d θ τ n := zero_lt_one.trans_le (selectedSourceVolume_ge_one A d θ τ n)
   have hB : 0 < (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) := by
     unfold selectedBlockCount
     exact_mod_cast blockCount_positive n _ _ d hnp hR
   have hu : 0 < selectedSourceAmplitude A d θ τ c0 epsilonU A.α n :=
     amplitude_positive epsilonU _ _ _ _ hεu hB hR (zero_lt_one.trans_le (selectedSourceMultiplier_ge_one A d θ τ n))
   have hv : 0 < selectedSourceAmplitude A d θ τ c0 epsilonV A.β n :=
     amplitude_positive epsilonV _ _ _ _ hεv hB hR (zero_lt_one.trans_le (selectedSourceMultiplier_ge_one A d θ τ n))
   have hρ := Upper.intervalRho_pos lo hi hlo hlt
   have heq : selectedSourceGapScale A d θ τ c0 epsilonU epsilonV lo hi n =
       (selectedSourceAmplitude A d θ τ c0 epsilonU A.α n *
        selectedSourceAmplitude A d θ τ c0 epsilonV A.β n * Real.exp (-τ * frequency n θ τ)) *
       ((Upper.narrowedRho lo hi ((Real.log n)^(-2 : ℝ)))^(frequency n θ τ) /
         Upper.intervalRho lo hi ^ (frequency n θ τ)) := by
     rw [← rho_power_eq_exp_tau lo hi hlo hlt]
     unfold selectedSourceGapScale
     field_simp [pow_ne_zero _ hρ.ne']
   rw [heq]
   calc
     _ = (1/2 : ℝ) * (C * Real.log n * RoughRegime.Rates.subcriticalScale n θ τ) := by ring
     _ ≤ (1/2 : ℝ) *
         (selectedSourceAmplitude A d θ τ c0 epsilonU A.α n *
          selectedSourceAmplitude A d θ τ c0 epsilonV A.β n * Real.exp (-τ * frequency n θ τ)) :=
       mul_le_mul_of_nonneg_left hp (by norm_num)
     _ ≤ _ := by
       convert mul_le_mul_of_nonneg_left hr (mul_pos (mul_pos hu hv) (Real.exp_pos _)).le using 1; ring

 theorem selectedSource_prior_variance_ratio_tendsto_zero (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ c0 epsilonU epsilonV lo hi : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2)
     (hεu : 0 < epsilonU) (hεv : 0 < epsilonV) (hlo : 0 < lo) (hlt : lo < hi)
     (hab : A.α/d + A.β/d = θ) :
     Tendsto (fun n : ℝ =>
       (1 / (selectedBlockCount θ (RoughRegime.Rates.tau lo hi) c0
         (selectedSourceVolume A d θ (RoughRegime.Rates.tau lo hi)) d n : ℝ)) /
       (selectedSourceGapScale A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU epsilonV lo hi n)^2)
       atTop (nhds 0) := by
   let τ := RoughRegime.Rates.tau lo hi
   have hτ := RoughRegime.Rates.tau_pos lo hi hlo hlt
   obtain ⟨C,hC,hgap⟩ := selectedSourceGapScale_eventually_log_lower A d hd θ c0 epsilonU epsilonV lo hi
     hθ hθhalf hεu hεv hlo hlt hab
   have hB := (selectedSource_grid_superlinear A d hd θ τ c0 0 hθ hθhalf hτ).eventually_ge_atTop 1
   simp only [Real.rpow_zero,mul_one] at hB
   have hlarge := subcritical_testing_scale_tendsto θ τ hθhalf
   have hlim := (tendsto_inv_atTop_zero.comp hlarge).const_mul (C^2)⁻¹
   simp only [mul_zero] at hlim
   apply squeeze_zero' (g := fun n : ℝ => (C^2)⁻¹*(n*RoughRegime.Rates.subcriticalScale n θ τ ^2)⁻¹) _ _ hlim
   · filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
     have hR : 0 < selectedSourceVolume A d θ τ n := zero_lt_one.trans_le (selectedSourceVolume_ge_one A d θ τ n)
     have hBpos : 0 < (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) := by
       unfold selectedBlockCount
       exact_mod_cast blockCount_positive n _ _ d (zero_lt_one.trans hn) hR
     positivity
   · filter_upwards [hgap,hB,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1 : ℝ)]
       with n hg hb hl hn
     have hnp : 0 < n := zero_lt_one.trans hn
     have hscale := RoughRegime.Rates.scale_pos n θ τ hn
     have hBn : n ≤ (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) :=
       by simpa only [one_mul] using (le_div_iff₀ hnp).mp hb
     have hbase : C*RoughRegime.Rates.subcriticalScale n θ τ ≤
         selectedSourceGapScale A d θ τ c0 epsilonU epsilonV lo hi n := by
       apply (show C*RoughRegime.Rates.subcriticalScale n θ τ ≤
         C*Real.log n*RoughRegime.Rates.subcriticalScale n θ τ from ?_).trans hg
       exact mul_le_mul_of_nonneg_right (by nlinarith) hscale.le
     have hgp : 0 < selectedSourceGapScale A d θ τ c0 epsilonU epsilonV lo hi n :=
       (mul_pos hC hscale).trans_le hbase
     have hsquare : C^2*RoughRegime.Rates.subcriticalScale n θ τ ^2 ≤
         (selectedSourceGapScale A d θ τ c0 epsilonU epsilonV lo hi n)^2 := by
       simpa only [mul_pow] using pow_le_pow_left₀ (mul_pos hC hscale).le hbase 2
     have hden : n*(C^2*RoughRegime.Rates.subcriticalScale n θ τ ^2) ≤
         (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ)*
         (selectedSourceGapScale A d θ τ c0 epsilonU epsilonV lo hi n)^2 :=
       mul_le_mul hBn hsquare (by positivity) (hnp.trans_le hBn).le
     calc
       _ = 1 / ((selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ)*
           (selectedSourceGapScale A d θ τ c0 epsilonU epsilonV lo hi n)^2) := by rw [div_div]
       _ ≤ 1 / (n*(C^2*RoughRegime.Rates.subcriticalScale n θ τ ^2)) :=
         one_div_le_one_div_of_le (by positivity) hden
       _ = _ := by ring

 theorem selectedSource_scaled_prior_variance_ratio_tendsto_zero
     (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ c0 epsilonU epsilonV lo hi Cvar cgap : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2)
     (hεu : 0 < epsilonU) (hεv : 0 < epsilonV) (hlo : 0 < lo) (hlt : lo < hi)
     (hab : A.α/d + A.β/d = θ) (hcgap : cgap ≠ 0) :
     Tendsto (fun n : ℝ =>
       (Cvar / (selectedBlockCount θ (RoughRegime.Rates.tau lo hi) c0
         (selectedSourceVolume A d θ (RoughRegime.Rates.tau lo hi)) d n : ℝ)) /
       (cgap * selectedSourceGapScale A d θ (RoughRegime.Rates.tau lo hi) c0 epsilonU epsilonV lo hi n)^2)
       atTop (nhds 0) := by
   have he := (selectedSource_prior_variance_ratio_tendsto_zero A d hd θ c0 epsilonU epsilonV lo hi
     hθ hθhalf hεu hεv hlo hlt hab).const_mul (Cvar/cgap^2)
   simp only [mul_zero] at he
   apply Filter.Tendsto.congr' _ he
   exact Eventually.of_forall (fun n => by field_simp [hcgap])

end RoughRegime.LatticePriors
