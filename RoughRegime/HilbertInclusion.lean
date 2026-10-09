module

public import RoughRegime.HilbertGram


@[expose] public section
/-! The fixed isometric coefficient matrix comes from genuine orthonormal parent
and child bases under the same reference Hilbert inner product. -/
noncomputable section
open scoped BigOperators
open RealInnerProductSpace Matrix
namespace RoughRegime.HilbertGram
variable {E n a : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]

def inclusionMatrix (z : n → E) (w : a → E) : Matrix n a ℝ := fun i j => ⟪z i, w j⟫

omit [Fintype n] in
lemma orthonormal_gram_eq_one (z : n → E) (hz : Orthonormal ℝ z) :
    Matrix.gram ℝ z = 1 := by
  ext i j
  simp only [Matrix.gram_apply, orthonormal_iff_ite.mp hz, Matrix.one_apply]

omit [DecidableEq n] [Fintype a] [DecidableEq a] in
/-- A parent basis really contained in the child space has the inner-product
coefficient matrix, rather than a postulated coordinate representation. -/
theorem parentBasis_inclusionMatrix (z : n → E) (hz : Orthonormal ℝ z)
    (w : a → E) (hsub : basisSpan w ≤ basisSpan z) :
    parentBasis z (inclusionMatrix z w) = w := by
  funext j
  have hw : w j ∈ basisSpan z := hsub (Submodule.subset_span (Set.mem_range_self j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  simp only [parentBasis, inclusionMatrix]
  conv_lhs => enter [2, i]; rw [← hc, hz.inner_right_fintype]
  exact hc

/-- The source `LᵀL=I` is a consequence of orthonormality and actual subspace
inclusion. -/
theorem inclusionMatrix_orthonormal (z : n → E) (hz : Orthonormal ℝ z)
    (w : a → E) (hw : Orthonormal ℝ w) (hsub : basisSpan w ≤ basisSpan z) :
    (inclusionMatrix z w)ᵀ * inclusionMatrix z w = 1 := by
  calc
    _ = ProjectionGram.gram (Matrix.gram ℝ z) (inclusionMatrix z w) := by
      rw [orthonormal_gram_eq_one z hz]
      simp [ProjectionGram.gram]
    _ = Matrix.gram ℝ (parentBasis z (inclusionMatrix z w)) :=
      (parentBasis_gram z _).symm
    _ = Matrix.gram ℝ w := by rw [parentBasis_inclusionMatrix z hz w hsub]
    _ = 1 := orthonormal_gram_eq_one w hw

/-- Existence of the exact fixed orthonormal column matrix needed in the weighted
Gram geometry, constructed from the reference Hilbert bases. -/
theorem exists_parent_matrix (z : n → E) (hz : Orthonormal ℝ z)
    (w : a → E) (hw : Orthonormal ℝ w) (hsub : basisSpan w ≤ basisSpan z) :
    ∃ L : Matrix n a ℝ, Lᵀ * L = 1 ∧ parentBasis z L = w :=
  ⟨inclusionMatrix z w, inclusionMatrix_orthonormal z hz w hw hsub,
    parentBasis_inclusionMatrix z hz w hsub⟩

end RoughRegime.HilbertGram
