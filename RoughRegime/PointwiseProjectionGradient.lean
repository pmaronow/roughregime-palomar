module

public import RoughRegime.ProjectionIncrementHolder


@[expose] public section
/-! A pointwise Hilbert specialization using already derived common component
bounds, so the numerical constant does not depend on the Hilbert realization. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ProjectionFrame
open RoughRegime.HilbertGram RoughRegime.ComplexDerivativeBridge RoughRegime.BilinearDerivative

 def incrementGradientConstant (hi : ℝ) (p n a b : ℕ) (Ha Hb ε A : ℝ) : ℝ :=
  (Real.sqrt p * derivativeConstant n A ε) *
    ((2 * hi ^ a * Real.sqrt hi) * Ha + (2 * hi ^ b * Real.sqrt hi) * Hb +
      ((2 * hi ^ a * Real.sqrt hi) * Ha) * ((2 * hi ^ b * Real.sqrt hi) * Hb))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem incrementPolynomial_gradient_holder_bound {p n a b : ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (x : Fin p → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (u v : Fin n → MvPolynomial (Fin p) ℝ) (m : ℕ)
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A)
    (hbound : ∀ t : Fin p → ℂ, ‖t - (fun i => (x i : ℂ))‖ < ε →
      (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial Ω La u i))‖ ≤ A) ∧
      (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial Ω Lb v i))‖ ≤ A) ∧
      (∀ i j, ‖MvPolynomial.eval t (complexify
        (truncationPolynomialMatrix lo hi Ω (twoGramPolynomials Ω La Lb) m i j))‖ ≤ A))
    (z : Fin n → E) (hz : LinearIndependent ℝ z)
    (hGram : Ω.map (MvPolynomial.eval x) = Matrix.gram ℝ z)
    (hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi)
    (f g ta tb : E) (hta : ta ∈ basisSpan (parentBasis z La))
    (htb : tb ∈ basisSpan (parentBasis z Lb))
    (hu : (fun i => MvPolynomial.eval x (u i)) = moments z f)
    (hv : (fun i => MvPolynomial.eval x (v i)) = moments z g)
    (h α β Ha Hb : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hα : 0 < α) (hβ : 0 < β) (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb)
    (hfa : ‖f - ta‖ ≤ Ha * h ^ α) (hgb : ‖g - tb‖ ≤ Hb * h ^ β) :
    ‖polynomialGradient (incrementPolynomial lo hi Ω La Lb u v m) x‖ ≤
      incrementGradientConstant hi p n a b Ha Hb ε A * h ^ min (min α β) 1 := by
  have hhi : 0 < hi := hlo.trans hlt
  let Ka := 2 * hi ^ a * Real.sqrt hi
  let Kb := 2 * hi ^ b * Real.sqrt hi
  let D := Real.sqrt p * derivativeConstant n A ε
  let U := ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω La u i))‖
  let W := ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω Lb v i))‖
  have hKa : 0 ≤ Ka := by dsimp [Ka]; positivity
  have hKb : 0 ≤ Kb := by dsimp [Kb]; positivity
  have hD : 0 ≤ D := by dsimp [D, derivativeConstant]; positivity
  have hU : U ≤ (Ka * Ha) * h ^ α := by
    have hb := residualMomentPolynomial_parent_bound lo hi hlo hlt x Ω La hLa u
      z hz hGram hSpec f ta hta hu
    exact hb.trans ((mul_le_mul_of_nonneg_left hfa hKa).trans_eq (mul_assoc Ka Ha (h ^ α)).symm)
  have hW : W ≤ (Kb * Hb) * h ^ β := by
    have hb := residualMomentPolynomial_parent_bound lo hi hlo hlt x Ω Lb hLb v
      z hz hGram hSpec g tb htb hv
    exact hb.trans ((mul_le_mul_of_nonneg_left hgb hKb).trans_eq (mul_assoc Kb Hb (h ^ β)).symm)
  have hsum := residual_holder_scale hh hh1 hα hβ
    (mul_nonneg hKa hHa) (mul_nonneg hKb hHb) (norm_nonneg _) (norm_nonneg _) hU hW
  calc
    _ ≤ D * (U + W + U * W) := bilinearPolynomial_gradient_norm_bound _ _ _ x ε A hε hA
      (fun i t ht => (hbound t ht).1 i) (fun i t ht => (hbound t ht).2.1 i)
      (fun i j t ht => (hbound t ht).2.2 i j)
    _ ≤ D * ((Ka * Ha + Kb * Hb + (Ka * Ha) * (Kb * Hb)) * h ^ min (min α β) 1) :=
      mul_le_mul_of_nonneg_left hsum hD
    _ = _ := by simp only [incrementGradientConstant, Ka, Kb, D]; ring

end RoughRegime.ProjectionIncrementComplex
