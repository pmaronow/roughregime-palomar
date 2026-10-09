module

public import RoughRegime.AffineResponseLower
public import RoughRegime.MeasureScores


@[expose] public section
/-! Bounded measurable source scores derived from actual model nondegeneracy. -/

noncomputable section
open MeasureTheory

namespace RoughRegime.MeasureScores

theorem nondegenerate_has_scores (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Model.Observables Z A) (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate A F π) :
    ∃ su sv : Z → ℝ, ∃ K : ℝ,
      Measurable su ∧ Measurable sv ∧ 0 ≤ K ∧
      (∀ z, |su z| ≤ K) ∧ (∀ z, |sv z| ≤ K) ∧
      (∫ z, su z ∂(π : Measure Z)) = 0 ∧ (∫ z, sv z ∂(π : Measure Z)) = 0 ∧
      (((∫ z, (F.U z - Model.baselineA A F π * F.D z) * su z ∂(π : Measure Z)) = 1 ∧
        (∫ z, (F.U z - Model.baselineA A F π * F.D z) * sv z ∂(π : Measure Z)) = 0 ∧
        (∫ z, (F.V z - Model.baselineB A F π * F.D z) * su z ∂(π : Measure Z)) = 0 ∧
        (∫ z, (F.V z - Model.baselineB A F π * F.D z) * sv z ∂(π : Measure Z)) = 1) ∨
       (F.U = F.V ∧ su = sv ∧
        (∫ z, (F.U z - Model.baselineA A F π * F.D z) * su z ∂(π : Measure Z)) = 1)) := by
  let a0 := Model.baselineA A F π
  let b0 := Model.baselineB A F π
  let rU := fun z => F.U z - a0 * F.D z
  let rV := fun z => F.V z - b0 * F.D z
  let C := (1 + |a0| + |b0|) * A.M0
  have hC : 0 ≤ C := mul_nonneg (by positivity) (le_of_lt A.hM0)
  have hmU : Measurable rU := F.measurableU.sub (F.measurableD.const_mul a0)
  have hmV : Measurable rV := F.measurableV.sub (F.measurableD.const_mul b0)
  have hDb (z : Z) : |F.D z| ≤ A.M0 := by
    rw [abs_of_nonneg (F.boundD z).1]
    exact (F.boundD z).2
  have hbU (z : Z) : |rU z| ≤ C := by
    have h : |F.U z - a0 * F.D z| ≤ |F.U z| + |a0 * F.D z| := by
      simpa using abs_sub_le (F.U z) 0 (a0 * F.D z)
    rw [abs_mul] at h
    have hd := mul_le_mul_of_nonneg_left (hDb z) (abs_nonneg a0)
    dsimp [rU, C]
    nlinarith [F.boundU z, mul_nonneg (abs_nonneg b0) (le_of_lt A.hM0)]
  have hbV (z : Z) : |rV z| ≤ C := by
    have h : |F.V z - b0 * F.D z| ≤ |F.V z| + |b0 * F.D z| := by
      simpa using abs_sub_le (F.V z) 0 (b0 * F.D z)
    rw [abs_mul] at h
    have hd := mul_le_mul_of_nonneg_left (hDb z) (abs_nonneg b0)
    dsimp [rV, C]
    nlinarith [F.boundV z, mul_nonneg (abs_nonneg a0) (le_of_lt A.hM0)]
  have hD := AffineResponseLower.score_integrable (π : Measure Z) F.D F.measurableD A.M0 hDb
  have hU := AffineResponseLower.score_integrable (π : Measure Z) F.U F.measurableU A.M0 F.boundU
  have hV := AffineResponseLower.score_integrable (π : Measure Z) F.V F.measurableV A.M0 F.boundV
  have hw : Model.baselineW A F π ≠ 0 := ne_of_gt
    (lt_trans A.hδ ((le_max_left _ _).trans_lt hnd.2.1))
  have hzU : (∫ z, rU z ∂(π : Measure Z)) = 0 := by
    dsimp [rU, a0, Model.baselineA]
    rw [integral_sub hU (hD.const_mul _), integral_const_mul]
    unfold Model.baselineW
    have hw' : (∫ z, F.D z ∂(π : Measure Z)) ≠ 0 := hw
    field_simp
    ring
  have hzV : (∫ z, rV z ∂(π : Measure Z)) = 0 := by
    dsimp [rV, b0, Model.baselineB]
    rw [integral_sub hV (hD.const_mul _), integral_const_mul]
    unfold Model.baselineW
    have hw' : (∫ z, F.D z ∂(π : Measure Z)) ≠ 0 := hw
    field_simp
    ring
  rcases hnd.2.2.2.2.2 with hpos | hdiag
  · have hdet : det (π : Measure Z) rU rV ≠ 0 := ne_of_gt hpos.2
    obtain ⟨su, sv, K, hsu, hsv, hK, hbu, hbv, hmu, hmv, hRu, hSu, hRv, hSv⟩ :=
      exists_bounded_scores (π : Measure Z) rU rV hmU hmV C hC hbU hbV hzU hzV hdet
    exact ⟨su, sv, K, hsu, hsv, hK, hbu, hbv, hmu, hmv, Or.inl ⟨hRu, hRv, hSu, hSv⟩⟩
  · obtain ⟨s, K, hs, hK, hb, hm, hR⟩ := exists_bounded_diagonal_score (π : Measure Z)
      rU hmU C hC hbU hzU (ne_of_gt hdiag.2.2)
    exact ⟨s, s, K, hs, hs, hK, hb, hb, hm, hm, Or.inr ⟨hdiag.1, rfl, hR⟩⟩

end RoughRegime.MeasureScores
