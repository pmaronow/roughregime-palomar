module

public import RoughRegime.Model
public import RoughRegime.SourceAnalyticParameters
public import RoughRegime.SourceFineResolution
public import RoughRegime.SourceFineGain
public import RoughRegime.ReductionRawHardness


@[expose] public section
/-! Instantiation of the original source construction with the actual largest
admissible lattice level, rounded even frequency, and superlinear rounded grid.
All scale budgets follow from the original fixed model parameters. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def selectedSourceLevel (A : Model.Parameters) (d : ℕ) (θ τ : ℝ) (n : ℝ) : ℕ :=
   selectedFineLevel θ τ (min A.α A.β) (sourceBandConstant d A.α A.β) n
 def selectedSourceMultiplier (A : Model.Parameters) (d : ℕ) (θ τ : ℝ) (n : ℝ) : ℝ :=
   selectedFineScale θ τ (min A.α A.β) (sourceBandConstant d A.α A.β) n
 def selectedSourceVolume (A : Model.Parameters) (d : ℕ) (θ τ : ℝ) (n : ℝ) : ℝ :=
   selectedFineVolume d θ τ (min A.α A.β) (sourceBandConstant d A.α A.β) n

 theorem selectedSourceVolume_rpow (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ n t : ℝ) : (selectedSourceVolume A d θ τ n) ^ (t/d) =
       (2 : ℝ) ^ ((selectedSourceLevel A d θ τ n : ℝ) * t) := by
   unfold selectedSourceVolume selectedFineVolume largestFineVolume
   rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
   congr 1
   push_cast
   have hd' : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
   field_simp
   dsimp [selectedSourceLevel,selectedFineLevel]
   ring

 theorem selectedSourceVolume_ge_one (A : Model.Parameters) (d : ℕ) (θ τ n : ℝ) :
     1 ≤ selectedSourceVolume A d θ τ n := selectedFineVolume_ge_one _ _ _ _ _ _

 theorem selectedSourceMultiplier_ge_one (A : Model.Parameters) (d : ℕ) (θ τ n : ℝ) :
     1 ≤ selectedSourceMultiplier A d θ τ n := by
   dsimp [selectedSourceMultiplier,selectedFineScale,largestFineScale ]
   exact Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (le_min A.hα.le A.hβ.le))

 theorem selectedSource_level_budgets (A : Model.Parameters) (d : ℕ) (θ τ n : ℝ) :
     (2 : ℝ) ^ ((selectedSourceLevel A d θ τ n : ℝ) * sourceAlpha0 A.α A.β) ≤
       selectedSourceMultiplier A d θ τ n ∧
     selectedSourceMultiplier A d θ τ n ≤ (2 : ℝ) ^ ((selectedSourceLevel A d θ τ n : ℝ) * A.α) ∧
     selectedSourceMultiplier A d θ τ n ≤ (2 : ℝ) ^ ((selectedSourceLevel A d θ τ n : ℝ) * A.β) := by
   exact largestFineScale_level_budgets (min A.α A.β) A.α A.β (sourceAlpha0 A.α A.β)
     (sourceBandConstant d A.α A.β) (frequency n θ τ) (lt_min A.hα A.hβ)
     (min_le_left _ _) (min_le_right _ _)
     (le_min (sourceAlpha0_lt_alpha _ _ A.hα).le (sourceAlpha0_lt_beta _ _ A.hβ).le)

 theorem selectedSourceVolume_log_isBigO (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) :
     (fun n => Real.log (selectedSourceVolume A d θ τ n)) =O[atTop]
       (fun n => Real.log (frequency n θ τ)) :=
   selectedFineVolume_log_isBigO d θ τ (min A.α A.β) (sourceBandConstant d A.α A.β)
     hθ hθhalf hτ (lt_min A.hα A.hβ)
     (sourceBandConstant_bounds d hd _ _ A.hα A.hβ).1
     (sourceBandConstant_bounds d hd _ _ A.hα A.hβ).2.le

 theorem selectedSourceMultiplier_frequency_budget (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) :
     ∀ᶠ n : ℝ in atTop, selectedSourceMultiplier A d θ τ n ≤
       sourceBandConstant d A.α A.β * frequency n θ τ := by
   let c := sourceBandConstant d A.α A.β
   have hc := (sourceBandConstant_bounds d hd _ _ A.hα A.hβ).1
   have he := (frequency_tendsto θ τ hθ hθhalf hτ).eventually_ge_atTop (1/c)
   filter_upwards [he] with n hn
   have hCM : 1 ≤ c*(frequency n θ τ : ℝ) := by
     have hh : c * (1/c) ≤ c * (frequency n θ τ : ℝ) := mul_le_mul_of_nonneg_left hn hc.le
     have hcc : c * (1/c) = 1 := by field_simp [show c ≠ 0 from hc.ne']
     rw [hcc] at hh
     exact hh
   exact (largestFineScale_bounds (min A.α A.β) c _ (lt_min A.hα A.hβ) hCM).1

 theorem selectedSourceMultiplier_volume_budgets (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ n : ℝ) :
     selectedSourceMultiplier A d θ τ n ≤ (selectedSourceVolume A d θ τ n) ^ (A.α/d) ∧
       selectedSourceMultiplier A d θ τ n ≤ (selectedSourceVolume A d θ τ n) ^ (A.β/d) := by
   have hb := selectedSource_level_budgets A d θ τ n
   have ha : (selectedSourceVolume A d θ τ n) ^ (A.α/d) =
       (2 : ℝ) ^ ((selectedSourceLevel A d θ τ n : ℝ) * A.α) :=
     selectedSourceVolume_rpow A d hd θ τ n A.α
   have hbeta : (selectedSourceVolume A d θ τ n) ^ (A.β/d) =
       (2 : ℝ) ^ ((selectedSourceLevel A d θ τ n : ℝ) * A.β) :=
     selectedSourceVolume_rpow A d hd θ τ n A.β
   exact ⟨hb.2.1.trans_eq ha.symm,hb.2.2.trans_eq hbeta.symm⟩

 theorem selectedSource_rawHardness_tendsto_zero (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 v0 ε CE C1 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (hv : 0 < v0) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC1 : 0 < C1)
     (hmargin : 1 + Real.log C1 + CE < c0) :
     Tendsto (fun n : ℝ => rawLeadingHardness n
       (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n) θ v0 ε
       (selectedSourceVolume A d θ τ n) (selectedSourceMultiplier A d θ τ n) CE C1 (frequency n θ τ))
       atTop (nhds 0) :=
   selected_rawLeadingHardness_tendsto_zero θ τ c0 v0 ε CE C1 (sourceBandConstant d A.α A.β)
     hθ hθhalf hτ hv hε hε1 hC1 (sourceBandConstant_bounds d hd _ _ A.hα A.hβ).1 hmargin
     (selectedSourceVolume A d θ τ) (selectedSourceMultiplier A d θ τ)
     (Eventually.of_forall (selectedSourceVolume_ge_one A d θ τ))
     (Eventually.of_forall (selectedSourceMultiplier_ge_one A d θ τ))
     (selectedSourceVolume_log_isBigO A d hd θ τ hθ hθhalf hτ)
     (selectedSourceMultiplier_frequency_budget A d hd θ τ hθ hθhalf hτ) d hd

 theorem selectedSource_grid_superlinear (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 q : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) :
     Tendsto (fun n : ℝ => (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) /
       (n * (Real.log n)^q)) atTop atTop := by
   have he := blockInflation_div_logPower_tendsto θ τ c0 q hθ hθhalf hτ
     (selectedSourceVolume A d θ τ) (Eventually.of_forall (selectedSourceVolume_ge_one A d θ τ))
     (selectedSourceVolume_log_isBigO A d hd θ τ hθ hθhalf hτ) d hd
   apply Filter.Tendsto.congr' _ he
   exact Eventually.of_forall (fun n => by unfold blockInflation; ring)

 theorem selectedSource_poisson_tail_budget_tendsto_zero (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 C1 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hC1 : 0 < C1) :
     Tendsto (fun n : ℝ => (C1 / blockInflation θ τ c0 (selectedSourceVolume A d θ τ) d n) *
       (selectedSourceVolume A d θ τ n) ^ Real.sqrt (frequency n θ τ)) atTop (nhds 0) :=
   tilted_tail_ratio_tendsto_zero θ τ c0 C1 hθ hθhalf hτ hC1 (selectedSourceVolume A d θ τ)
     (Eventually.of_forall (selectedSourceVolume_ge_one A d θ τ))
     (selectedSourceVolume_log_isBigO A d hd θ τ hθ hθhalf hτ) d hd

 theorem selectedSource_remainderRatio_tendsto_zero (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 epsilonU epsilonV C v0 CE CΓ : ℝ)
     (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (hεu : 0 < epsilonU) (hεu1 : epsilonU ≤ 1) (hεv : 0 < epsilonV) (hεv1 : epsilonV ≤ 1)
     (hC : 0 ≤ C) (hv : 0 < v0) (hCE : 0 ≤ CE) (hCΓ : 1 ≤ CΓ) :
     Tendsto (fun n : ℝ => remainderRatio C
       (2 * v0 / blockInflation θ τ c0 (selectedSourceVolume A d θ τ) d n)
       (amplitude epsilonU (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n)
         (selectedSourceVolume A d θ τ n) (A.α/d) (selectedSourceMultiplier A d θ τ n))
       (amplitude epsilonV (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n)
         (selectedSourceVolume A d θ τ n) (A.β/d) (selectedSourceMultiplier A d θ τ n))
       (selectedSourceVolume A d θ τ n) CE CΓ (frequency n θ τ)) atTop (nhds 0) :=
   selected_remainderRatio_tendsto_zero θ τ c0 epsilonU epsilonV (A.α/d) (A.β/d) C v0 CE CΓ
     hθ hθhalf hτ (div_pos A.hα (Nat.cast_pos.mpr hd)) (div_pos A.hβ (Nat.cast_pos.mpr hd))
     hεu hεu1 hεv hεv1 hC hv hCE hCΓ
     (selectedSourceVolume A d θ τ) (selectedSourceMultiplier A d θ τ)
     (Eventually.of_forall (selectedSourceVolume_ge_one A d θ τ))
     (Eventually.of_forall (selectedSourceMultiplier_ge_one A d θ τ))
     (selectedSourceVolume_log_isBigO A d hd θ τ hθ hθhalf hτ)
     (Eventually.of_forall (fun n => (selectedSourceMultiplier_volume_budgets A d hd θ τ n).1))
     (Eventually.of_forall (fun n => (selectedSourceMultiplier_volume_budgets A d hd θ τ n).2)) d hd

 theorem selectedSource_separation_eventually_lower (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 epsilonU epsilonV : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (hεu : 0 ≤ epsilonU) (hεv : 0 ≤ epsilonV) (hab : A.α/d + A.β/d = θ) :
     ∀ᶠ n : ℝ in atTop,
       (epsilonU * epsilonV * separationConstant θ τ c0 / 2) * (selectedSourceMultiplier A d θ τ n)^2 *
         RoughRegime.Rates.subcriticalScale n θ τ ≤
       amplitude epsilonU (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n)
         (selectedSourceVolume A d θ τ n) (A.α/d) (selectedSourceMultiplier A d θ τ n) *
       amplitude epsilonV (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n)
         (selectedSourceVolume A d θ τ n) (A.β/d) (selectedSourceMultiplier A d θ τ n) *
       Real.exp (-τ * frequency n θ τ) :=
   selected_amplitude_product_eventually_lower θ τ c0 epsilonU epsilonV (A.α/d) (A.β/d)
     hθ hθhalf hτ hεu hεv hab
     (selectedSourceVolume A d θ τ) (selectedSourceMultiplier A d θ τ)
     (Eventually.of_forall (selectedSourceVolume_ge_one A d θ τ))
     (selectedSourceVolume_log_isBigO A d hd θ τ hθ hθhalf hτ) d hd

 theorem selectedSourceMultiplier_log_gain (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) :
     ∃ CL > 0, ∃ CU > 0, ∀ᶠ n : ℝ in atTop,
       CL * Real.log n ≤ (selectedSourceMultiplier A d θ τ n)^2 ∧
       (selectedSourceMultiplier A d θ τ n)^2 ≤ CU * Real.log n :=
   selectedFineScale_sq_log_bounds θ τ (min A.α A.β) (sourceBandConstant d A.α A.β)
     hθ hθhalf hτ (lt_min A.hα A.hβ) (sourceBandConstant_bounds d hd _ _ A.hα A.hβ).1

 theorem selectedSource_product_log_gain (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
     (θ τ c0 epsilonU epsilonV : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ)
     (hεu : 0 < epsilonU) (hεv : 0 < epsilonV) (hab : A.α/d + A.β/d = θ) :
     ∃ C > 0, ∀ᶠ n : ℝ in atTop,
       C * Real.log n * RoughRegime.Rates.subcriticalScale n θ τ ≤
       amplitude epsilonU (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n)
         (selectedSourceVolume A d θ τ n) (A.α/d) (selectedSourceMultiplier A d θ τ n) *
       amplitude epsilonV (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n)
         (selectedSourceVolume A d θ τ n) (A.β/d) (selectedSourceMultiplier A d θ τ n) *
       Real.exp (-τ * frequency n θ τ) :=
   selected_fine_amplitude_product_eventually_lower θ τ c0 epsilonU epsilonV (A.α/d) (A.β/d)
     (min A.α A.β) (sourceBandConstant d A.α A.β) d hθ hθhalf hτ hεu hεv hab
     (lt_min A.hα A.hβ) (sourceBandConstant_bounds d hd _ _ A.hα A.hβ).1
     (sourceBandConstant_bounds d hd _ _ A.hα A.hβ).2.le hd

end RoughRegime.LatticePriors
