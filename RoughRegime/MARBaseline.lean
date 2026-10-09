module

public import RoughRegime.ApplicationMARClass


@[expose] public section
/-! The actual finite-support MAR baseline and its nondegeneracy. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.Applications.MAR

def missingPoint : Response := Sum.inl ()
def zeroPoint : Response := Sum.inr ⟨0, by norm_num⟩
def onePoint : Response := Sum.inr ⟨1, by norm_num⟩
def baselinePoint : Fin 3 → Response := ![missingPoint, zeroPoint, onePoint]

def baselinePMF : PMF (Fin 3) := PMF.ofFintype (fun i => ENNReal.ofReal (marBaseline i))
  (by
    simp only [Fin.sum_univ_succ, marBaseline, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 4),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 4 + 1 / 4)]
    norm_num)

def baseline : ProbabilityMeasure Response :=
  ProbabilityMeasure.map ⟨baselinePMF.toMeasure, inferInstance⟩ baselinePoint

theorem baseline_integral (f : Response → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(baseline : Measure Response)) =
      (1 / 2) * f missingPoint + (1 / 4) * f zeroPoint + (1 / 4) * f onePoint := by
  change (∫ z, f z ∂baselinePMF.toMeasure.map baselinePoint) = _
  rw [integral_map (measurable_of_countable baselinePoint).aemeasurable hf.aestronglyMeasurable,
    PMF.integral_eq_sum]
  norm_num [baselinePMF, PMF.ofFintype_apply, Fin.sum_univ_succ, marBaseline,
    baselinePoint, smul_eq_mul]
  ring

theorem baseline_finite_support :
    ∃ s : Finset Response, (baseline : Measure Response) (s : Set Response) = 1 := by
  classical
  refine ⟨Finset.univ.image baselinePoint, ?_⟩
  change baselinePMF.toMeasure.map baselinePoint (↑(Finset.univ.image baselinePoint)) = 1
  rw [Measure.map_apply (measurable_of_countable baselinePoint) (Finset.measurableSet _)]
  have hs : baselinePoint ⁻¹' (↑(Finset.univ.image baselinePoint) : Set Response) = univ := by
    ext i
    simp
  rw [hs, measure_univ]

theorem baseline_response_moments :
    (∫ z, observed z ∂(baseline : Measure Response)) = 1 / 2 ∧
    (∫ z, observedOutcome z ∂(baseline : Measure Response)) = 1 / 4 := by
  rw [baseline_integral observed observed_measurable,
    baseline_integral observedOutcome observedOutcome_measurable]
  norm_num [observed, observedOutcome, missingPoint, zeroPoint, onePoint]

theorem baseline_ratios (A : Model.Parameters) (hM : 1 ≤ A.M0) :
    Model.baselineW A (observables A hM) baseline = 1 / 2 ∧
    Model.baselineA A (observables A hM) baseline = 2 ∧
    Model.baselineB A (observables A hM) baseline = 1 / 2 := by
  have hD : Model.baselineW A (observables A hM) baseline = 1 / 2 :=
    baseline_response_moments.1
  refine ⟨hD, ?_, ?_⟩
  · unfold Model.baselineA
    rw [hD]
    change (∫ _z, (1 : ℝ) ∂(baseline : Measure Response)) / (1 / 2) = 2
    norm_num [integral_const, probReal_univ]
  · unfold Model.baselineB
    rw [hD]
    change (∫ z, observedOutcome z ∂(baseline : Measure Response)) / (1 / 2) = 1 / 2
    rw [baseline_response_moments.2]
    norm_num

theorem baseline_residual_covariance :
    (∫ z, (1 - 2 * observed z) ^ 2 ∂(baseline : Measure Response)) = 1 ∧
    (∫ z, (1 - 2 * observed z) * (observedOutcome z - (1 / 2) * observed z)
      ∂(baseline : Measure Response)) = 0 ∧
    (∫ z, (observedOutcome z - (1 / 2) * observed z) ^ 2 ∂(baseline : Measure Response)) = 1 / 8 := by
  have hm1 : Measurable (fun z => 1 - 2 * observed z) :=
    measurable_const.sub (observed_measurable.const_mul 2)
  have hm2 : Measurable (fun z => observedOutcome z - (1 / 2) * observed z) :=
    observedOutcome_measurable.sub (observed_measurable.const_mul (1 / 2))
  rw [baseline_integral _ (hm1.pow_const 2),
    baseline_integral (fun z => (1 - 2 * observed z) * (observedOutcome z - (1 / 2) * observed z))
      (hm1.mul hm2),
    baseline_integral _ (hm2.pow_const 2)]
  norm_num [observed, observedOutcome, missingPoint, zeroPoint, onePoint]

/-- The source's finite-support baseline satisfies the actual statistical
nondegeneracy definition, including the residual covariance determinant. -/
theorem baseline_nondegenerate (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1 / 2) (hhi : 1 / 2 < A.gplus) (hH : 2 < A.H) :
    Model.Nondegenerate A (observables A hM) baseline := by
  have hm := baseline_ratios A hM
  refine ⟨baseline_finite_support, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hm.1] using hlo
  · simpa only [hm.1] using hhi
  · simpa only [hm.2.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hH
  · rw [hm.2.2]
    norm_num [abs_of_pos] at *
    linarith
  · dsimp only
    rw [hm.2.1, hm.2.2]
    left
    change (0 < ∫ z, (1 - 2 * observed z) ^ 2 ∂(baseline : Measure Response)) ∧
      0 < (∫ z, (1 - 2 * observed z) ^ 2 ∂(baseline : Measure Response)) *
        (∫ z, (observedOutcome z - (1 / 2) * observed z) ^ 2 ∂(baseline : Measure Response)) -
        (∫ z, (1 - 2 * observed z) * (observedOutcome z - (1 / 2) * observed z)
          ∂(baseline : Measure Response)) ^ 2
    rw [baseline_residual_covariance.1, baseline_residual_covariance.2.1,
      baseline_residual_covariance.2.2]
    norm_num

end RoughRegime.Applications.MAR
