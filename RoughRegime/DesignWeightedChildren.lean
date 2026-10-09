module

public import RoughRegime.DesignParentCells
public import RoughRegime.DyadicDesign


@[expose] public section
/-! Fixed parent matrices and genuine weighted child Gram matrices in the model. -/
noncomputable section
open MeasureTheory Set
open scoped Matrix
namespace RoughRegime.Model
variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}

def ModelWitness.weightedChildBasis (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (i : Fin (dyadicChildDimension A.d k)) : Lp ℝ 2 (W.cellDesignMeasure c) := by
  haveI := W.cellDesignMeasure_finite c
  exact designLp (W.cellDesignMeasure c)
    (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c i)
    (dyadicFinChildBasisFunction_measurable _ _ _ _) (dyadicDesignBasisBound A.d k)
    (dyadicFinChildBasisFunction_bound _ _ _ _)

theorem ModelWitness.weightedChildBasis_ae (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (i : Fin (dyadicChildDimension A.d k)) :
    W.weightedChildBasis k c i =ᵐ[W.cellDesignMeasure c]
      dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c i := by
  haveI := W.cellDesignMeasure_finite c
  exact designLp_ae _ _ _ _ _

theorem ModelWitness.weightedChildBasis_gram (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) :
    Matrix.gram ℝ (W.weightedChildBasis k c) =
      designGram (rectangleVolume (dyadicOrigin c) (dyadicSides c)) W.designDensity
        (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c) := by
  haveI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  exact weighted_designLp_gram _ _ W.designDensity_measurable A.gplus
    ((W.dyadic_density_bounds c).mono (fun _ hx => A.hgminus.le.trans hx.1))
    ((W.dyadic_density_bounds c).mono (fun _ hx => hx.2)) _
    (dyadicFinChildBasisFunction_measurable _ _ _) _ (dyadicFinChildBasisFunction_bound _ _ _)

theorem ModelWitness.weightedChildBasis_spectrum (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) :
    spectrum ℝ (Matrix.gram ℝ (W.weightedChildBasis k c)) ⊆ Icc A.gminus A.gplus := by
  rw [W.weightedChildBasis_gram]
  exact dyadicDesign_spectrum A F P W k c

theorem ModelWitness.weightedChildBasis_linearIndependent (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) : LinearIndependent ℝ (W.weightedChildBasis k c) := by
  haveI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  exact weighted_designLp_linearIndependent _ _ W.designDensity_measurable _ _ A.hgminus
    (W.dyadic_density_bounds c) _ (dyadicFinChildBasisFunction_measurable _ _ _)
    _ (le_trans zero_le_one (dyadicDesignBasisBound_ge_one _ _))
    (dyadicFinChildBasisFunction_bound _ _ _) (dyadicFinChildBasisFunction_orthogonality _ _ _)

theorem transport_reference_parent_expansion {d j k l : ℕ} (hd : 0 < d) (c : DyadicCell d j)
    (L : Matrix (Fin (dyadicChildDimension d l)) (Fin (Module.finrank ℝ (polynomialLpSpace d k))) ℝ)
    (he : HilbertGram.parentBasis (referenceChildFinBasis l (dyadicSplitAxis d j hd)) L =
      fun i => polynomialToLp d (basisPolynomial d k i)) :
    HilbertGram.parentBasis (dyadicFinChildBasis hd l c) L = dyadicParentBasis k c := by
  funext i
  have hi := congrFun he i
  apply_fun (rectangleLpTransport (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)) at hi
  simpa only [HilbertGram.parentBasis, map_sum, map_smul, dyadicFinChildBasis,
    dyadicParentBasis, rectangleBasis] using hi

theorem ModelWitness.weighted_parent_expansion (W : ModelWitness A F P) {j k l : ℕ}
    (c : DyadicCell A.d j)
    (L : Matrix (Fin (dyadicChildDimension A.d l)) (Fin (Module.finrank ℝ (polynomialLpSpace A.d k))) ℝ)
    (he : HilbertGram.parentBasis (dyadicFinChildBasis (lt_of_lt_of_le Nat.zero_lt_one A.hd) l c) L =
      dyadicParentBasis k c) :
    HilbertGram.parentBasis (W.weightedChildBasis l c) L = W.weightedParentBasis k c :=
  transfer_parentBasis _ _ (W.cellDesignMeasure_ac c)
    _ _ _ _ _ _ (dyadicFinChildBasisFunction_ae _ _ _) (dyadicParentBasis_ae_function _ _)
    (W.weightedChildBasis_ae _ _) (W.weightedParentBasis_ae _ _) L he

theorem ModelWitness.weighted_parent_expansion_reference (W : ModelWitness A F P) {j k l : ℕ}
    (c : DyadicCell A.d j)
    (L : Matrix (Fin (dyadicChildDimension A.d l)) (Fin (Module.finrank ℝ (polynomialLpSpace A.d k))) ℝ)
    (he : HilbertGram.parentBasis
      (referenceChildFinBasis l (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd))) L =
        fun i => polynomialToLp A.d (basisPolynomial A.d k i)) :
    HilbertGram.parentBasis (W.weightedChildBasis l c) L = W.weightedParentBasis k c :=
  W.weighted_parent_expansion c L (transport_reference_parent_expansion _ c L he)

end RoughRegime.Model
