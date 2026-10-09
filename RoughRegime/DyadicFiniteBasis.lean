module

public import RoughRegime.DyadicApproximation


@[expose] public section
/-! Exact finite-coordinate child bases and fixed parent inclusion matrices. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Matrix
namespace RoughRegime.Model

abbrev dyadicChildDimension (d k : ℕ) : ℕ := Fintype.card (SplitIndex d k)

theorem dyadicChildDimension_eq (d k : ℕ) : dyadicChildDimension d k = 2 * (d + k).choose d := by
  simp [dyadicChildDimension, polynomialLpSpace_finrank]

def referenceChildFinBasis {d : ℕ} (k : ℕ) (r : Fin d) (i : Fin (dyadicChildDimension d k)) :
    Lp ℝ 2 (cubeVolume d) := splitBasisLp k r ((Fintype.equivFin (SplitIndex d k)).symm i)

theorem referenceChildFinBasis_orthonormal {d : ℕ} (k : ℕ) (r : Fin d) :
    Orthonormal ℝ (referenceChildFinBasis k r) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simpa only [referenceChildFinBasis, (Fintype.equivFin (SplitIndex d k)).symm.injective.eq_iff]
    using orthonormal_iff_ite.mp (splitBasisLp_orthonormal k r)
    ((Fintype.equivFin (SplitIndex d k)).symm i) ((Fintype.equivFin (SplitIndex d k)).symm j)

theorem referenceChildFinBasis_span {d : ℕ} (k : ℕ) (r : Fin d) :
    HilbertGram.basisSpan (referenceChildFinBasis k r) = splitLpSpace k r := by
  unfold HilbertGram.basisSpan splitLpSpace
  congr 1
  apply Set.ext
  intro f
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin (SplitIndex d k)) i, by simp [referenceChildFinBasis]⟩

theorem reference_fin_parent_matrix {d k l : ℕ} (r : Fin d) (hkl : k ≤ l) :
    ∃ L : Matrix (Fin (dyadicChildDimension d l)) (Fin (Module.finrank ℝ (polynomialLpSpace d k))) ℝ,
      Lᵀ * L = 1 ∧ HilbertGram.parentBasis (referenceChildFinBasis l r) L =
        (fun i => polynomialToLp d (basisPolynomial d k i)) := by
  apply HilbertGram.exists_parent_matrix _ (referenceChildFinBasis_orthonormal l r) _
    (basisPolynomial_orthonormal d k)
  rw [referenceChildFinBasis_span]
  apply Submodule.span_le.mpr
  rintro f ⟨i, rfl⟩
  exact polynomialToLp_mem_splitSpace r _ ((basisPolynomial_degree d k i).trans hkl)

def dyadicFinChildBasis {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j)
    (i : Fin (dyadicChildDimension d k)) : Lp ℝ 2 (rectangleVolume (dyadicOrigin c) (dyadicSides c)) :=
  rectangleLpTransport (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
    (referenceChildFinBasis k (dyadicSplitAxis d j hd) i)

theorem dyadicFinChildBasis_orthonormal {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j) :
    Orthonormal ℝ (dyadicFinChildBasis hd k c) :=
  (rectangleLpTransport (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)).orthonormal_comp_iff.mpr
    (referenceChildFinBasis_orthonormal k (dyadicSplitAxis d j hd))

def dyadicParentBasis {d j : ℕ} (k : ℕ) (c : DyadicCell d j)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    Lp ℝ 2 (rectangleVolume (dyadicOrigin c) (dyadicSides c)) :=
  rectangleBasis k (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c) i

theorem dyadicParentBasis_orthonormal {d j : ℕ} (k : ℕ) (c : DyadicCell d j) :
    Orthonormal ℝ (dyadicParentBasis k c) := rectangleBasis_orthonormal k _ _ _

theorem dyadic_parent_matrix {d j k l : ℕ} (hd : 0 < d) (c : DyadicCell d j) (hkl : k ≤ l) :
    ∃ L : Matrix (Fin (dyadicChildDimension d l)) (Fin (Module.finrank ℝ (polynomialLpSpace d k))) ℝ,
      Lᵀ * L = 1 ∧ HilbertGram.parentBasis (dyadicFinChildBasis hd l c) L = dyadicParentBasis k c := by
  obtain ⟨L, hL, he⟩ := reference_fin_parent_matrix (dyadicSplitAxis d j hd) hkl
  refine ⟨L, hL, ?_⟩
  funext i
  have hi := congrFun he i
  apply_fun (rectangleLpTransport (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)) at hi
  simpa only [HilbertGram.parentBasis, map_sum, map_smul, dyadicFinChildBasis,
    dyadicParentBasis, rectangleBasis] using hi

theorem dyadicPolynomialLp_mem_parentSpan {d j k : ℕ} (c : DyadicCell d j)
    (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ k) :
    dyadicPolynomialLp c p ∈ HilbertGram.basisSpan (dyadicParentBasis k c) := by
  obtain ⟨a, ha⟩ := basisPolynomial_expansion (rectangleEmbedPolynomial (dyadicOrigin c) (dyadicSides c) p)
    ((rectangleEmbedPolynomial_degree _ _ p).trans hp)
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨a, ?_⟩
  unfold dyadicPolynomialLp
  rw [← ha, map_sum, map_sum]
  simp only [map_smul, dyadicParentBasis, rectangleBasis]

end RoughRegime.Model
