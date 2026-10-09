module

public import RoughRegime.DesignReferenceMatrices
public import RoughRegime.PointwiseProjectionGradient


@[expose] public section
/-! One genuine complex neighborhood for all fixed split axes and all actual
local increment polynomials, chosen before the statistical model. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.Model
open RoughRegime.ProjectionIncrementComplex RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions

 theorem uniform_localIncrement_components (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ ε B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧
      ∀ t : Fin (localMomentDimension A) → ℂ,
        (∃ x ∈ designMomentSet (localChildDimension A) A.gminus A.gplus (A.H * A.gplus),
          ‖t - realParametersCLM (localMomentDimension A) x‖ < ε) →
        ∀ r : Fin A.d,
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localAlphaMatrix A hαβ r)
            (designFirstPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localBetaMatrix A r)
            (designSecondPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ m i j, ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix A.gminus A.gplus
            (designGramPolynomial (localChildDimension A))
            (twoGramPolynomials (designGramPolynomial (localChildDimension A))
              (localAlphaMatrix A hαβ r) (localBetaMatrix A r)) m i j))‖ ≤ B) ∧
          (∀ m, ‖MvPolynomial.eval t (complexify (localIncrementPolynomial A hαβ r m))‖ ≤
            (localChildDimension A : ℝ) ^ 2 * B ^ 3) := by
  classical
  let V := designMomentSet (localChildDimension A) A.gminus A.gplus (A.H * A.gplus)
  have hV : Bornology.IsBounded V := designMomentSet_bounded _ _ _ _ A.hgminus.le
    (A.hgminus.trans A.hgplus).le
  have perAxis (r : Fin A.d) := uniform_incrementPolynomial_components A.gminus A.gplus
    A.hgminus A.hgplus V hV (designGramPolynomial (localChildDimension A))
    (fun x _ => designMatrix_isHermitian x) (fun x hx => hx.1)
    (localAlphaMatrix A hαβ r) (localBetaMatrix A r)
    (referenceParentMatrix_orthonormal _ _ _ r) (referenceParentMatrix_orthonormal _ _ _ r)
    (designFirstPolynomial (localChildDimension A)) (designSecondPolynomial (localChildDimension A))
  have aux (s : Finset (Fin A.d)) : ∃ ε B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧
      ∀ t : Fin (localMomentDimension A) → ℂ,
        (∃ x ∈ V, ‖t - realParametersCLM (localMomentDimension A) x‖ < ε) →
        ∀ r ∈ s,
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localAlphaMatrix A hαβ r)
            (designFirstPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial (localChildDimension A)) (localBetaMatrix A r)
            (designSecondPolynomial (localChildDimension A)) i))‖ ≤ B) ∧
          (∀ m i j, ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix A.gminus A.gplus
            (designGramPolynomial (localChildDimension A))
            (twoGramPolynomials (designGramPolynomial (localChildDimension A))
              (localAlphaMatrix A hαβ r) (localBetaMatrix A r)) m i j))‖ ≤ B) ∧
          (∀ m, ‖MvPolynomial.eval t (complexify (localIncrementPolynomial A hαβ r m))‖ ≤
            (localChildDimension A : ℝ) ^ 2 * B ^ 3) := by
    induction s using Finset.induction with
    | empty => exact ⟨1, 0, by norm_num, le_rfl, le_rfl, by simp⟩
    | @insert r s hr ih =>
      obtain ⟨εs, Bs, hεs, hεs1, hBs, hs⟩ := ih
      obtain ⟨εr, Br, hεr, hεr1, hBr, hb⟩ := perAxis r
      refine ⟨min εs εr, max Bs Br, lt_min hεs hεr,
        (min_le_left _ _).trans hεs1, hBs.trans (le_max_left _ _), ?_⟩
      intro t ht q hq
      obtain ⟨x, hx, hnear⟩ := ht
      rcases Finset.mem_insert.mp hq with rfl | hq
      · obtain ⟨ha, hb', hS, hP⟩ := hb t ⟨x, hx, hnear.trans_le (min_le_right _ _)⟩
        refine ⟨fun i => (ha i).trans (le_max_right _ _),
          fun i => (hb' i).trans (le_max_right _ _),
          fun m i j => (hS m i j).trans (le_max_right _ _), ?_⟩
        intro m
        apply (hP m).trans
        gcongr
        exact le_max_right Bs Br
      · obtain ⟨ha, hb', hS, hP⟩ := hs t ⟨x, hx, hnear.trans_le (min_le_left _ _)⟩ q hq
        refine ⟨fun i => (ha i).trans (le_max_left _ _),
          fun i => (hb' i).trans (le_max_left _ _),
          fun m i j => (hS m i j).trans (le_max_left _ _), ?_⟩
        intro m
        apply (hP m).trans
        gcongr
        exact le_max_left Bs Br
  obtain ⟨ε, B, hε, hε1, hB, hb⟩ := aux Finset.univ
  exact ⟨ε, B, hε, hε1, hB, fun t ht r => hb t ht r (Finset.mem_univ r)⟩

end RoughRegime.Model
