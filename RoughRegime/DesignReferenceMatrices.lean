module

public import RoughRegime.DesignWeightedChildren
public import RoughRegime.DesignDyadicPopulation


@[expose] public section
/-! Fixed reference parent matrices and the actual model's increment polynomial. -/
noncomputable section
open Matrix MeasureTheory
namespace RoughRegime.Model
open RoughRegime.HilbertGram RoughRegime.ProjectionIncrementPolynomial

 def referenceParentMatrix {d : ℕ} (k l : ℕ) (hkl : k ≤ l) (r : Fin d) :
    Matrix (Fin (dyadicChildDimension d l)) (Fin (Module.finrank ℝ (polynomialLpSpace d k))) ℝ :=
  Classical.choose (reference_fin_parent_matrix r hkl)

lemma referenceParentMatrix_orthonormal {d : ℕ} (k l : ℕ) (hkl : k ≤ l) (r : Fin d) :
    (referenceParentMatrix k l hkl r)ᵀ * referenceParentMatrix k l hkl r = 1 :=
  (Classical.choose_spec (reference_fin_parent_matrix r hkl)).1

lemma referenceParentMatrix_expansion {d : ℕ} (k l : ℕ) (hkl : k ≤ l) (r : Fin d) :
    parentBasis (referenceChildFinBasis l r) (referenceParentMatrix k l hkl r) =
      fun i => polynomialToLp d (basisPolynomial d k i) :=
  (Classical.choose_spec (reference_fin_parent_matrix r hkl)).2

lemma ModelWitness.referenceParentMatrix_expansion {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) (k l : ℕ) (hkl : k ≤ l) :
    parentBasis (W.weightedChildBasis l c)
      (referenceParentMatrix k l hkl (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd))) =
        W.weightedParentBasis k c :=
  W.weighted_parent_expansion_reference c _ (RoughRegime.Model.referenceParentMatrix_expansion k l hkl _)

abbrev localChildDimension (A : Parameters) := dyadicChildDimension A.d (holderOrder A.β)
abbrev localAlphaDimension (A : Parameters) := Module.finrank ℝ (polynomialLpSpace A.d (holderOrder A.α))
abbrev localBetaDimension (A : Parameters) := Module.finrank ℝ (polynomialLpSpace A.d (holderOrder A.β))
abbrev localMomentDimension (A : Parameters) := designMomentDimension (localChildDimension A)

 def localAlphaMatrix (A : Parameters) (hαβ : A.α ≤ A.β) (r : Fin A.d) :
    Matrix (Fin (localChildDimension A)) (Fin (localAlphaDimension A)) ℝ :=
  referenceParentMatrix (holderOrder A.α) (holderOrder A.β) (holderOrder_monotone hαβ) r
 def localBetaMatrix (A : Parameters) (r : Fin A.d) :
    Matrix (Fin (localChildDimension A)) (Fin (localBetaDimension A)) ℝ :=
  referenceParentMatrix (holderOrder A.β) (holderOrder A.β) le_rfl r

 def localIncrementPolynomial (A : Parameters) (hαβ : A.α ≤ A.β) (r : Fin A.d) (m : ℕ) :
    MvPolynomial (Fin (localMomentDimension A)) ℝ :=
  incrementPolynomial A.gminus A.gplus (designGramPolynomial (localChildDimension A))
    (localAlphaMatrix A hαβ r) (localBetaMatrix A r)
    (designFirstPolynomial (localChildDimension A)) (designSecondPolynomial (localChildDimension A)) m

 theorem localIncrementPolynomial_degree (A : Parameters) (hαβ : A.α ≤ A.β) (r : Fin A.d) (m : ℕ) :
    (localIncrementPolynomial A hαβ r m).totalDegree ≤ m + A.nu + 2 := by
  have hb := incrementPolynomial_degree A.gminus A.gplus (designGramPolynomial (localChildDimension A))
    (localAlphaMatrix A hαβ r) (localBetaMatrix A r)
    (designFirstPolynomial (localChildDimension A)) (designSecondPolynomial (localChildDimension A)) m
    (designGramPolynomial_degree _) (designFirstPolynomial_degree _) (designSecondPolynomial_degree _)
  simpa only [localIncrementPolynomial, localAlphaDimension, localBetaDimension,
    polynomialLpSpace_finrank, Parameters.nu, Nat.add_assoc] using hb

end RoughRegime.Model
