module

public import RoughRegime.SplitBasis


@[expose] public section
/-! Orthonormality of the actual two-child polynomial basis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem cubeCoordinateFace_volume_zero {d : ℕ} (r : Fin d) (t : ℝ) :
    volume {x : Covariate d | x ∈ cube d ∧ x r = t} = 0 := by
  classical
  let o : Covariate d := WithLp.toLp 2 (fun i => if i = r then t else 0)
  let s : Fin d → ℝ := fun i => if i = r then 0 else 1
  apply measure_mono_null (t := rectangle o s)
  · intro x hx i
    by_cases hi : i = r
    · subst i
      simpa [o, s, hx.2]
    · simpa [o, s, hi] using hx.1 i
  · rw [rectangle_volume]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [s])

theorem splitRectangle_inter_volume_zero {d : ℕ} (r : Fin d) {b c : Bool}
    (hbc : b ≠ c) : volume (splitRectangle r b ∩ splitRectangle r c) = 0 := by
  apply measure_mono_null (t := {x : Covariate d | x ∈ cube d ∧ x r = (1 / 2 : ℝ)})
  · intro x hx
    refine ⟨splitRectangle_subset_cube r b hx.1, ?_⟩
    have hb := hx.1 r
    have hc := hx.2 r
    cases b <;> cases c <;> simp_all [splitRectangle, splitOrigin, splitSides, Bool.toNat]
    all_goals linarith
  · exact cubeCoordinateFace_volume_zero r _

theorem splitBasisLp_ae {d : ℕ} (k : ℕ) (r : Fin d) (i : SplitIndex d k) :
    splitBasisLp k r i =ᵐ[cubeVolume d] splitBasisFunction k r i :=
  (splitBasisFunction_memLp k r i).coeFn_toLp

theorem splitBasisLp_inner_integral {d : ℕ} (k : ℕ) (r : Fin d) (i j : SplitIndex d k) :
    inner ℝ (splitBasisLp k r i) (splitBasisLp k r j) =
      ∫ x, splitBasisFunction k r i x * splitBasisFunction k r j x ∂cubeVolume d := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [splitBasisLp_ae k r i, splitBasisLp_ae k r j] with x hi hj
  simp [hi, hj, mul_comm]

theorem splitBasisLp_inner_same {d : ℕ} (k : ℕ) (r : Fin d) (b : Bool)
    (i j : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    inner ℝ (splitBasisLp k r (b, i)) (splitBasisLp k r (b, j)) =
      if i = j then 1 else 0 := by
  classical
  let f : Covariate d → ℝ := fun x =>
    polynomialEvaluation (basisPolynomial d k i) x *
      polynomialEvaluation (basisPolynomial d k j) x
  have hf : Continuous f := (polynomialEvaluation_continuous _).mul
    (polynomialEvaluation_continuous _)
  have hp := rectangleCoords_preserving (splitOrigin r b) (splitSides r) (splitSides_pos r)
  have hint : (∫ x, f (rectangleCoords (splitOrigin r b) (splitSides r) x)
      ∂rectangleVolume (splitOrigin r b) (splitSides r)) = ∫ x, f x ∂cubeVolume d := by
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm
  have hnormal := hint
  rw [splitRectangle_normalizedVolume, integral_smul_measure] at hnormal
  norm_num only [ENNReal.toReal_ofReal, Nat.ofNat_nonneg, smul_eq_mul] at hnormal
  rw [splitBasisLp_inner_integral]
  calc
    _ = ∫ x, (splitRectangle r b).indicator
        (fun x => 2 * f (rectangleCoords (splitOrigin r b) (splitSides r) x)) x
        ∂cubeVolume d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ splitRectangle r b
        · simp only [splitBasisFunction, indicator_of_mem hx]
          dsimp [f]
          have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
          calc
            _ = (Real.sqrt 2 * Real.sqrt 2) *
                (polynomialEvaluation (basisPolynomial d k i)
                  (rectangleCoords (splitOrigin r b) (splitSides r) x) *
                polynomialEvaluation (basisPolynomial d k j)
                  (rectangleCoords (splitOrigin r b) (splitSides r) x)) := by ring
            _ = _ := by rw [← pow_two, hs]
        · simp [splitBasisFunction, hx]
    _ = 2 * ∫ x in splitRectangle r b,
        f (rectangleCoords (splitOrigin r b) (splitSides r) x) ∂cubeVolume d := by
      rw [integral_indicator (splitRectangle_measurable r b), integral_const_mul]
    _ = ∫ x, f x ∂cubeVolume d := hnormal
    _ = inner ℝ (polynomialToLp d (basisPolynomial d k i))
        (polynomialToLp d (basisPolynomial d k j)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [polynomialToLp_ae (basisPolynomial d k i),
        polynomialToLp_ae (basisPolynomial d k j)] with x hi hj
      simp [f, hi, hj, mul_comm]
    _ = _ := orthonormal_iff_ite.mp (basisPolynomial_orthonormal d k) i j

theorem splitBasisLp_inner_different {d : ℕ} (k : ℕ) (r : Fin d)
    (i j : SplitIndex d k) (hij : i.1 ≠ j.1) :
    inner ℝ (splitBasisLp k r i) (splitBasisLp k r j) = 0 := by
  have hz : cubeVolume d (splitRectangle r i.1 ∩ splitRectangle r j.1) = 0 := by
    apply le_antisymm _ bot_le
    exact (Measure.restrict_le_self _).trans_eq (splitRectangle_inter_volume_zero r hij)
  have hae : ∀ᵐ x ∂cubeVolume d, x ∉ splitRectangle r i.1 ∩ splitRectangle r j.1 := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hz
  rw [splitBasisLp_inner_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with x hx
  by_cases hi : x ∈ splitRectangle r i.1
  · have hj : x ∉ splitRectangle r j.1 := fun hj => hx ⟨hi, hj⟩
    simp [splitBasisFunction, hj]
  · simp [splitBasisFunction, hi]

theorem splitBasisLp_orthonormal {d : ℕ} (k : ℕ) (r : Fin d) :
    Orthonormal ℝ (splitBasisLp k r) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hb : i.1 = j.1
  · obtain ⟨b, i⟩ := i
    obtain ⟨c, j⟩ := j
    dsimp only at hb
    subst c
    simpa using splitBasisLp_inner_same k r b i j
  · rw [splitBasisLp_inner_different k r i j hb]
    simp only [ite_eq_right (fun he => hb (congrArg Prod.fst he))]

end RoughRegime.Model
