module

public import RoughRegime.SplitInclusion
public import RoughRegime.DyadicRefinement


@[expose] public section
/-! The actual source cells carry the transported parent and child spaces. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Matrix
namespace RoughRegime.Model

def dyadicOrigin {d j : ℕ} (c : DyadicCell d j) : Covariate d :=
  WithLp.toLp 2 (fun i => (c i : ℝ) / (2 : ℝ) ^ axisDepth d j i)

def dyadicSides {d j : ℕ} (_c : DyadicCell d j) (i : Fin d) : ℝ :=
  1 / (2 : ℝ) ^ axisDepth d j i

theorem dyadicSides_pos {d j : ℕ} (c : DyadicCell d j) (i : Fin d) : 0 < dyadicSides c i := by
  unfold dyadicSides
  positivity

theorem dyadicRectangle_eq_rectangle {d j : ℕ} (c : DyadicCell d j) :
    dyadicRectangle c = rectangle (dyadicOrigin c) (dyadicSides c) := by
  ext x
  simp only [dyadicRectangle, rectangle, mem_ofPred_eq, dyadicOrigin, dyadicSides,
    WithLp.ofLp_toLp, add_div]

theorem dyadicSides_prod {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    (∏ i, dyadicSides c i) = 1 / (2 : ℝ) ^ j := by
  simp only [dyadicSides, one_div, Finset.prod_inv_distrib]
  rw [Finset.prod_pow_eq_pow_sum, axisDepth_sum d j hd]

theorem dyadicRectangle_normalizedVolume {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    rectangleVolume (dyadicOrigin c) (dyadicSides c) =
      ENNReal.ofReal ((2 : ℝ) ^ j) • (cubeVolume d).restrict (dyadicPartitionCell c) := by
  rw [rectangleVolume, dyadicSides_prod hd c, one_div_div,
    ← dyadicRectangle_eq_rectangle]
  have hrestrict : (cubeVolume d).restrict (dyadicPartitionCell c) =
      volume.restrict (dyadicPartitionCell c) := by
    rw [cubeVolume, Measure.restrict_restrict (dyadicPartitionCell_measurable c),
      inter_eq_left.mpr (fun _ hx => hx.1)]
  rw [hrestrict, ← Measure.restrict_congr_set (dyadicRectangle_ae_eq_partition c)]
  simp only [div_one]

def dyadicSplitAxis (d j : ℕ) (hd : 0 < d) : Fin d := ⟨j % d, Nat.mod_lt j hd⟩

def dyadicChildBasis {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j)
    (i : SplitIndex d k) : Lp ℝ 2 (rectangleVolume (dyadicOrigin c) (dyadicSides c)) :=
  rectangleLpTransport (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
    (splitBasisLp k (dyadicSplitAxis d j hd) i)

theorem dyadicChildBasis_orthonormal {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j) :
    Orthonormal ℝ (dyadicChildBasis hd k c) :=
  (rectangleLpTransport (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)).orthonormal_comp_iff.mpr
    (splitBasisLp_orthonormal k (dyadicSplitAxis d j hd))

def dyadicChildBasisFunction {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j)
    (i : SplitIndex d k) (x : Covariate d) : ℝ :=
  splitBasisFunction k (dyadicSplitAxis d j hd) i
    (rectangleCoords (dyadicOrigin c) (dyadicSides c) x)

theorem dyadicChildBasis_ae {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j)
    (i : SplitIndex d k) : dyadicChildBasis hd k c i =ᵐ[rectangleVolume (dyadicOrigin c) (dyadicSides c)]
      dyadicChildBasisFunction hd k c i := by
  have hp := rectangleCoords_preserving (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  exact (Lp.coeFn_compMeasurePreserving _ hp).trans
    (hp.quasiMeasurePreserving.ae_eq_comp (splitBasisLp_ae k _ i))

theorem dyadicChildBasisFunction_measurable {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j)
    (i : SplitIndex d k) : Measurable (dyadicChildBasisFunction hd k c i) :=
  (splitBasisFunction_measurable k _ i).comp (rectangleCoords_continuous _ _).measurable

theorem dyadicChildBasisFunction_uniform_bound (d k : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (hd : 0 < d) (j : ℕ) (c : DyadicCell d j) i x,
      |dyadicChildBasisFunction hd k c i x| ≤ B := by
  classical
  by_cases hd : 0 < d
  · have hex (r : Fin d) := splitBasisFunction_uniform_bound k r
    choose B hB hb using hex
    refine ⟨1 + ∑ r, |B r|, le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
    intro hd j c i x
    have hs := Finset.single_le_sum (fun r _ => abs_nonneg (B r))
      (Finset.mem_univ (dyadicSplitAxis d j hd))
    exact (hb _ _ _).trans ((le_abs_self _).trans (by linarith))
  · exact ⟨1, le_rfl, fun h => (hd h).elim⟩

theorem reference_parent_matrix {d k l : ℕ} (r : Fin d) (hkl : k ≤ l) :
    ∃ L : Matrix (SplitIndex d l) (Fin (Module.finrank ℝ (polynomialLpSpace d k))) ℝ,
      Lᵀ * L = 1 ∧ HilbertGram.parentBasis (splitBasisLp l r) L =
        (fun i => polynomialToLp d (basisPolynomial d k i)) := by
  apply HilbertGram.exists_parent_matrix _ (splitBasisLp_orthonormal l r) _
    (basisPolynomial_orthonormal d k)
  apply Submodule.span_le.mpr
  rintro f ⟨i, rfl⟩
  exact polynomialToLp_mem_splitSpace r _ ((basisPolynomial_degree d k i).trans hkl)

end RoughRegime.Model
