module

public import RoughRegime.DesignPolynomial
public import RoughRegime.PointwiseProjectionGradient


@[expose] public section
/-! The literal nonsplit base polynomial with empty parent spaces. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.Model
open RoughRegime.HilbertGram RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.ProjectionIncrementComplex RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionPolynomial RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions

 def emptyParentMatrix (n : ℕ) : Matrix (Fin n) (Fin 0) ℝ := 0
 lemma emptyParentMatrix_orthonormal (n : ℕ) :
    (emptyParentMatrix n)ᵀ * emptyParentMatrix n = 1 := by ext i; exact Fin.elim0 i

 lemma emptyParentBasis_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (z : Fin n → E) : basisSpan (parentBasis z (emptyParentMatrix n)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

 def packedInversePolynomial (n : ℕ) (lo hi : ℝ) (m : ℕ) :
    MvPolynomial (Fin (designMomentDimension n)) ℝ :=
  incrementPolynomial lo hi (designGramPolynomial n) (emptyParentMatrix n) (emptyParentMatrix n)
    (designFirstPolynomial n) (designSecondPolynomial n) m

 theorem packedInversePolynomial_degree (n : ℕ) (lo hi : ℝ) (m : ℕ) :
    (packedInversePolynomial n lo hi m).totalDegree ≤ m + 2 := by
  simpa only [packedInversePolynomial, Nat.add_zero] using incrementPolynomial_degree lo hi
    (designGramPolynomial n) (emptyParentMatrix n) (emptyParentMatrix n)
    (designFirstPolynomial n) (designSecondPolynomial n) m
    (designGramPolynomial_degree n) (designFirstPolynomial_degree n) (designSecondPolynomial_degree n)

 theorem uniform_packedInverse_components (n : ℕ) (lo hi R : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    ∃ ε B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧
      ∀ t : Fin (designMomentDimension n) → ℂ,
        (∃ x ∈ designMomentSet n lo hi R, ‖t - realParametersCLM (designMomentDimension n) x‖ < ε) →
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial n) (emptyParentMatrix n) (designFirstPolynomial n) i))‖ ≤ B) ∧
          (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial
            (designGramPolynomial n) (emptyParentMatrix n) (designSecondPolynomial n) i))‖ ≤ B) ∧
          (∀ m i j, ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix lo hi
            (designGramPolynomial n) (twoGramPolynomials (designGramPolynomial n)
              (emptyParentMatrix n) (emptyParentMatrix n)) m i j))‖ ≤ B) ∧
          (∀ m, ‖MvPolynomial.eval t (complexify (packedInversePolynomial n lo hi m))‖ ≤
            (n : ℝ) ^ 2 * B ^ 3) :=
  uniform_incrementPolynomial_components lo hi hlo hlt (designMomentSet n lo hi R)
    (designMomentSet_bounded n lo hi R hlo.le (hlo.trans hlt).le) (designGramPolynomial n)
    (fun x _ => designMatrix_isHermitian x) (fun x hx => hx.1)
    (emptyParentMatrix n) (emptyParentMatrix n) (emptyParentMatrix_orthonormal n)
    (emptyParentMatrix_orthonormal n) (designFirstPolynomial n) (designSecondPolynomial n)

end RoughRegime.Model
