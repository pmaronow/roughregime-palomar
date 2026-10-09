module

public import RoughRegime.ModelProductEstimator


@[expose] public section
/-! The literal model estimator with the paper's deterministic tuning rules,
and uniform risks derived from their proved numerical inequalities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
open RoughRegime.UpperDegreeRules RoughRegime.UpperTuning RoughRegime.LiftVariance
open RoughRegime.UpperParametric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def modelDegreeSlope (A : Parameters) : ℝ :=
  (A.theta * Real.log 2 + 1) / RoughRegime.Rates.tau A.gminus A.gplus

 theorem modelDegreeSlope_nonneg (A : Parameters) : 0 ≤ modelDegreeSlope A := by
  unfold modelDegreeSlope
  have := A.theta_pos
  have := A.tau_pos
  have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

 theorem modelDegreeSlope_decay (A : Parameters) :
    A.theta * Real.log 2 + 1 ≤ RoughRegime.Rates.tau A.gminus A.gplus * modelDegreeSlope A := by
  unfold modelDegreeSlope
  rw [mul_div_cancel₀ _ A.tau_pos.ne']

 def modelSmoothnessExponent (A : Parameters) : ℝ := min (min A.α A.β) 1 / A.d

 theorem modelSmoothnessExponent_pos (A : Parameters) : 0 < modelSmoothnessExponent A :=
  div_pos (lt_min (lt_min A.hα A.hβ) zero_lt_one)
    (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one A.hd))

 def parametricProductEstimator (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (Cv : ℝ) (n : ℕ) :=
  let J := terminalLevel (terminalConstant (modelDegreeSlope A) Cv A.nu) n
  productEstimator A hαβ F J (fun j => biasDegree (modelDegreeSlope A) (levelDistance J j)) n

 def subcriticalProductEstimator (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (Cv : ℝ) (n : ℕ) :=
  let τ := RoughRegime.Rates.tau A.gminus A.gplus
  productEstimator A hαβ F (RoughRegime.UpperSubcritical.terminal n A.theta τ)
    (RoughRegime.UpperSubcritical.chosenOrder n A.theta τ (modelDegreeSlope A) Cv A.nu) n

 theorem uniform_parametricProductEstimator_risk (A : Parameters) (hαβ : A.α ≤ A.β)
    (hθ : 1 / 2 ≤ A.theta) :
    ∃ Cv C : ℝ, 1 ≤ Cv ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
        (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P),
        lpNorm (fun xs => parametricProductEstimator A hαβ F Cv n xs - W.productTarget) 2
          (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤ C / Real.sqrt n := by
  obtain ⟨Cb,Cv,Cproj,hCb,hCv,hCproj,hrisk⟩ := uniform_productEstimator_risk.{u} A hαβ
  let D := modelDegreeSlope A
  let cK := terminalConstant D Cv A.nu
  let B := (Cproj + Cb * biasRuleConstant D A.nu) * (2 / cK) ^ A.theta
  let S := Real.sqrt Cv * (1 + (1 - (2 : ℝ) ^ (-modelSmoothnessExponent A))⁻¹) +
    2 * Cv * sqrtResolutionConstant * Real.sqrt cK
  have hD : 0 ≤ D := modelDegreeSlope_nonneg A
  have hCvp : 0 < Cv := zero_lt_one.trans_le hCv
  have hcK : 0 < cK := by dsimp [cK,terminalConstant]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (add_nonneg hCproj.le (mul_nonneg (zero_le_one.trans hCb)
      (biasRuleConstant_nonneg D A.nu hD))) (Real.rpow_nonneg (by positivity) _)
  refine ⟨Cv,|B + S| + 1,hCv,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (uncappedThreshold D Cv A.nu),eventually_ge_atTop (3 : ℕ)] with n hn hn3
  intro Z _ F P W
  let J := terminalLevel cK n
  let m : Fin (J + 1) → ℕ := fun j => biasDegree D (levelDistance J j)
  let μ := Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))
  have ht := uncapped_tuning_valid D Cv A.nu n hD hCvp hn
  have ht' : 0 < cK ∧ cK ≤ 1 ∧ cK * n / 2 < (2 : ℝ) ^ J ∧ (2 : ℝ) ^ J ≤ cK * n ∧
      ∀ j : Fin (J + 1), 2 * (m j + A.nu + 2) ≤ n ∧
        Cv * (m j + A.nu + 2 : ℕ) * parentCells J j / n ≤ 1 / 2 := ht
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hcn : 1 ≤ cK * n := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans ht'.2.2.2.1
  have hr := hrisk Z F P W J m n (fun j => (ht'.2.2.2.2 j).1)
  let v : Fin (J + 1) → ℝ := fun j => variance (levelEstimator A hαβ F J m n j) μ
  have hv (j : Fin (J + 1)) : v j ≤ Cv * (parentCells J j : ℝ) ^ (-2 * modelSmoothnessExponent A) / n +
      4 * Cv ^ 2 * parentCells J j / (n : ℝ) ^ 2 := by
    exact (hr.2 j).trans (add_le_add le_rfl
      (variance_tail_small_resolution Cv (parentCells J j) n (m j + A.nu + 2)
        hCvp.le (Nat.cast_nonneg _) hnr (ht'.2.2.2.2 j).2))
  have hb := uncapped_total_error_bound D Cv Cb Cproj cK n A.theta
    (RoughRegime.Rates.tau A.gminus A.gplus) (modelSmoothnessExponent A) A.nu
    hD hCvp.le (zero_le_one.trans hCb) hCproj.le ht'.1 hnr A.theta_pos.le A.tau_pos.le
    (modelSmoothnessExponent_pos A) (modelDegreeSlope_decay A) hcn v hv
  have hnum := parametric_rate_comparison n A.theta B S hn1 hθ hB
  change lpNorm (fun xs => productEstimator A hαβ F J m n xs - W.productTarget) 2 μ ≤ _
  exact hr.1.trans (hb.trans (hnum.trans (div_le_div_of_nonneg_right
    ((le_abs_self (B + S)).trans (by linarith)) (Real.sqrt_nonneg _))))

 theorem uniform_subcriticalProductEstimator_risk (A : Parameters) (hαβ : A.α ≤ A.β)
    (hθ : A.theta < 1 / 2) :
    ∃ Cv C : ℝ, 1 ≤ Cv ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
        (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P),
        lpNorm (fun xs => subcriticalProductEstimator A hαβ F Cv n xs - W.productTarget) 2
          (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
            C * RoughRegime.UpperSubcritical.rate n A.theta
              (RoughRegime.Rates.tau A.gminus A.gplus) A.nu := by
  obtain ⟨Cb,Cv,Cproj,hCb,hCv,hCproj,hrisk⟩ := uniform_productEstimator_risk.{u} A hαβ
  let τ := RoughRegime.Rates.tau A.gminus A.gplus
  let D := modelDegreeSlope A
  have hD := modelDegreeSlope_nonneg A
  have hvalid := RoughRegime.UpperSubcritical.tuning_valid_eventually A.theta τ D Cv A.nu
    A.theta_pos hθ A.tau_pos hD hCv
  have hbound := RoughRegime.UpperSubcritical.chosen_total_error_bound_eventually A.theta τ D Cv Cb Cproj
    (modelSmoothnessExponent A) A.nu A.theta_pos hθ A.tau_pos hD hCv
    (zero_le_one.trans hCb) hCproj.le (modelSmoothnessExponent_pos A).le A.nu_ge_two (modelDegreeSlope_decay A)
  let C := RoughRegime.UpperSubcritical.riskConstant A.theta τ D Cv Cb Cproj A.nu
  refine ⟨Cv,|C| + 1,hCv,by positivity,?_⟩
  have hvnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hvalid
  have hbnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound
  filter_upwards [hvnat,hbnat,eventually_ge_atTop (3 : ℕ)] with n hn hb hn3
  intro Z _ F P W
  let J := RoughRegime.UpperSubcritical.terminal n A.theta τ
  let m := RoughRegime.UpperSubcritical.chosenOrder n A.theta τ D Cv A.nu
  have hdegree (j : Fin (J + 1)) : 2 * (m j + A.nu + 2) ≤ n := by
    have ht := hn.degree_sample j
    unfold RoughRegime.UpperSubcritical.chosenDegree at ht
    exact_mod_cast ht
  have hr := hrisk Z F P W J m n hdegree
  have hnum := hb (fun j => variance (levelEstimator A hαβ F J m n j)
    (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z))))) hr.2
  have hrate : 0 ≤ RoughRegime.UpperSubcritical.rate n A.theta τ A.nu :=
    (RoughRegime.UpperSubcritical.rate_positive n A.theta τ A.nu (by exact_mod_cast (show 1 < n by omega))).le
  exact hr.1.trans (hnum.trans (mul_le_mul_of_nonneg_right
    ((le_abs_self C).trans (by linarith)) hrate))

 theorem rootN_le_subcriticalRate_eventually (A : Parameters) (hθ : A.theta < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, 1 / Real.sqrt (n : ℝ) ≤
      RoughRegime.UpperSubcritical.rate n A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu := by
  let τ := RoughRegime.Rates.tau A.gminus A.gplus
  have hratio := (RoughRegime.UpperSubcritical.lowVariance_relative_rate_tendsto_zero A.theta τ A.nu hθ).eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
  have hn := eventually_gt_atTop (1 : ℝ)
  have he := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (hratio.and (hlog.and hn))
  filter_upwards [he] with n hn
  have hr := RoughRegime.UpperSubcritical.rate_positive n A.theta τ A.nu hn.2.2
  have hL : 1 ≤ (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow hn.2.1 (by norm_num)
  exact (div_le_div_of_nonneg_right hL (Real.sqrt_nonneg _)).trans ((div_le_one hr).mp hn.1)

end RoughRegime.Model
