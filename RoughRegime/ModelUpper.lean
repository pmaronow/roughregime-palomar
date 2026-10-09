module

public import RoughRegime.ModelProductRates
public import RoughRegime.ModelEstimatorCombination


@[expose] public section
/-! The uniform upper statement for the actual model and actual measurable
shared-sample estimator, with both source tuning regimes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem minimaxRMSE_le_fixed_estimator {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (E : Estimator Ω n) (r : ℝ≥0∞)
    (hr : ∀ P ∈ C, eLpNorm (fun o => E.val o - T P) 2 (randomizedExperiment n P) ≤ r) :
    minimaxRMSE n T C ≤ r := by
  apply (iInf_le _ E).trans
  exact iSup_le (fun P => iSup_le (fun hP => hr P hP))

 theorem uniformUpperClaim_ordered_parametric (A : Parameters) (hαβ : A.α ≤ A.β)
    (hθ : 1 / 2 ≤ A.theta) (L MW : ℝ) : UniformUpperClaim.{u} A L MW := by
  obtain ⟨Cv,Cp,hCv,hCp,hprod⟩ := uniform_parametricProductEstimator_risk.{u} A hαβ hθ
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp hprod
  let C := |MW| + |L| * Cp + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,max 3 n0,le_max_left _ _,?_⟩
  intro Z mZ F hL hMW n hn _
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hnn0 : n0 ≤ n := (le_max_right _ _).trans hn
  have hnp : 0 < n := by omega
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  refine ⟨fun _ => ?_,fun hsub => False.elim (by linarith [hsub.2])⟩
  let E := parametricProductEstimator A hαβ F Cv n
  have hE : Measurable E := by
    dsimp [E,parametricProductEstimator]
    exact productEstimator_measurable _ _ _ _ _ _
  apply minimaxRMSE_le_fixed_estimator n (target A F) (modelClass A F)
    (combinedEstimator A F n E hE)
  intro P hP
  obtain ⟨W⟩ := hP
  have hmem : MemLp E 2 (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) := by
    dsimp [E,parametricProductEstimator]
    exact productEstimator_memLp _ _ _ _ _ _ _
  have hc := combinedEstimator_eLpNorm_error A F P W n hnp E hE hmem MW hMW
  have hp := hn0 n hnn0 Z F P W
  have hlam : |F.lam| ≤ |L| := by rw [hL]; exact le_abs_self _
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg F.lam)
  have hmul := mul_le_mul_of_nonneg_right hlam (div_nonneg hCp.le hsqrt)
  have hnum : |MW| / Real.sqrt (n : ℝ) + |F.lam| *
      lpNorm (fun xs => E xs - W.productTarget) 2
        (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
      (|MW| + |L| * Cp) / Real.sqrt n := by
    calc
      _ ≤ |MW| / Real.sqrt n + |L| * (Cp / Real.sqrt n) := add_le_add le_rfl (hm.trans hmul)
      _ = _ := by ring
  have ht := div_le_div_of_nonneg_right (show |MW| + |L| * Cp ≤ C by dsimp [C]; linarith) hsqrt
  have heq : C / Real.sqrt (n : ℝ) = C * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg (Nat.cast_nonneg _) (1 / 2),← Real.sqrt_eq_rpow]
    rfl
  exact hnum.trans (ht.trans_eq heq)

 theorem uniformUpperClaim_ordered_subcritical (A : Parameters) (hαβ : A.α ≤ A.β)
    (hθ : A.theta < 1 / 2) (L MW : ℝ) : UniformUpperClaim.{u} A L MW := by
  obtain ⟨Cv,Cp,hCv,hCp,hprod⟩ := uniform_subcriticalProductEstimator_risk.{u} A hαβ hθ
  have hroot := rootN_le_subcriticalRate_eventually A hθ
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (hprod.and hroot)
  let C := |MW| + |L| * Cp + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,max 3 n0,le_max_left _ _,?_⟩
  intro Z mZ F hL hMW n hn _
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hnn0 : n0 ≤ n := (le_max_right _ _).trans hn
  have hnp : 0 < n := by omega
  let τ := RoughRegime.Rates.tau A.gminus A.gplus
  let r := RoughRegime.UpperSubcritical.rate n A.theta τ A.nu
  have hrp : 0 < r := RoughRegime.UpperSubcritical.rate_positive n A.theta τ A.nu
    (by exact_mod_cast (show 1 < n by omega))
  refine ⟨fun hcrit => False.elim (by linarith),fun _ => ?_⟩
  let E := subcriticalProductEstimator A hαβ F Cv n
  have hE : Measurable E := by
    dsimp [E,subcriticalProductEstimator]
    exact productEstimator_measurable _ _ _ _ _ _
  apply minimaxRMSE_le_fixed_estimator n (target A F) (modelClass A F)
    (combinedEstimator A F n E hE)
  intro P hP
  obtain ⟨W⟩ := hP
  have hmem : MemLp E 2 (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) := by
    dsimp [E,subcriticalProductEstimator]
    exact productEstimator_memLp _ _ _ _ _ _ _
  have hc := combinedEstimator_eLpNorm_error A F P W n hnp E hE hmem MW hMW
  have hp := (hn0 n hnn0).1 Z F P W
  have hroot := (hn0 n hnn0).2
  have hlam : |F.lam| ≤ |L| := by rw [hL]; exact le_abs_self _
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  have hw : |MW| / Real.sqrt (n : ℝ) ≤ |MW| * r := by
    convert mul_le_mul_of_nonneg_left hroot (abs_nonneg MW) using 1; ring
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg F.lam)
  have hmul := mul_le_mul_of_nonneg_right hlam (mul_nonneg hCp.le hrp.le)
  have hnum : |MW| / Real.sqrt (n : ℝ) + |F.lam| *
      lpNorm (fun xs => E xs - W.productTarget) 2
        (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤ C * r := by
    calc
      _ ≤ |MW| * r + |L| * (Cp * r) := add_le_add hw (hm.trans hmul)
      _ = (|MW| + |L| * Cp) * r := by ring
      _ ≤ C * r := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hrp.le
  have heq := RoughRegime.UpperSubcritical.rate_eq_paper_scale n A.theta τ A.nu
    (by exact_mod_cast (show 1 < n by omega))
  dsimp only [r] at hnum
  rw [heq] at hnum
  simpa only [mul_assoc] using hnum

 theorem uniformUpperClaim_ordered (A : Parameters) (hαβ : A.α ≤ A.β) (L MW : ℝ) :
    UniformUpperClaim.{u} A L MW := by
  by_cases hθ : 1 / 2 ≤ A.theta
  · exact uniformUpperClaim_ordered_parametric A hαβ hθ L MW
  · exact uniformUpperClaim_ordered_subcritical A hαβ (lt_of_not_ge hθ) L MW

/-- Main Theorem 1(a), uniform over all response spaces and observable
functions with the stated fixed bounds. The estimator and its tuning depend
only on these observables and model constants. -/
 theorem uniformUpperClaim (A : Parameters) (L MW : ℝ) : UniformUpperClaim.{u} A L MW := by
  by_cases hαβ : A.α ≤ A.β
  · exact uniformUpperClaim_ordered A hαβ L MW
  · apply uniformUpperClaim_of_swap A L MW
    exact uniformUpperClaim_ordered A.swap (le_of_lt (lt_of_not_ge hαβ)) L MW

end RoughRegime.Model
