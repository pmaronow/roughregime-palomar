module

public import RoughRegime.DesignProjection
public import RoughRegime.Foundation


@[expose] public section
/-! Actual uniform product bias, with no assumed approximation hypotheses. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RoughRegime.Model
universe u

theorem uniform_cell_projection_bias (A : Parameters) (k : ℕ)
    (hak : holderOrder A.α ≤ k) (hbk : holderOrder A.β ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j : ℕ) (c : DyadicCell A.d j),
      |W.cellProductTarget c - W.cellProjectionTarget k c| ≤
        C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ (A.α + A.β) := by
  obtain ⟨Ha, hHa, ha⟩ := uniform_model_cell_approximation.{u} A A.α
  obtain ⟨Hb, hHb, hb⟩ := uniform_model_cell_approximation.{u} A A.β
  refine ⟨4 * Ha * Hb, by positivity, ?_⟩
  intro Z _ F P W j c
  let K := HilbertGram.basisSpan (W.weightedParentBasis k c)
  obtain ⟨hqa, hda, hea⟩ := ha Z F P W j c W.a W.measurableA W.smoothA
  obtain ⟨hqb, hdb, heb⟩ := hb Z F P W j c W.b W.measurableB W.smoothB
  have hma := W.weighted_polynomial_parent_member c _ (hda.trans hak) hqa
  have hmb := W.weighted_polynomial_parent_member c _ (hdb.trans hbk) hqb
  have hna : ‖W.cellALp c - K.starProjection (W.cellALp c)‖ ≤
      2 * Ha * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.α := by
    exact (projection_residual_le_approximation K _ _ hma).trans
      ((mul_le_mul_of_nonneg_left hea (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  have hnb : ‖W.cellBLp c - K.starProjection (W.cellBLp c)‖ ≤
      2 * Hb * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.β := by
    exact (projection_residual_le_approximation K _ _ hmb).trans
      ((mul_le_mul_of_nonneg_left heb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  have h := Foundation.projection_product_bias_bound K (W.cellALp c) (W.cellBLp c)
  calc
    _ ≤ ‖W.cellALp c - K.starProjection (W.cellALp c)‖ *
        ‖W.cellBLp c - K.starProjection (W.cellBLp c)‖ := h
    _ ≤ (2 * Ha * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.α) *
        (2 * Hb * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.β) := by gcongr
    _ = (4 * Ha * Hb) * (((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.α *
        ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.β) := by ring
    _ = _ := by rw [← Real.rpow_add (by positivity)]

end RoughRegime.Model
