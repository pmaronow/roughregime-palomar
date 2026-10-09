module

public import RoughRegime.ProjectionIncrementGradient


@[expose] public section
/-! Source Lemma 6's uniform complex bound and `h^min(α,β,1)` gradient,
proved for the concrete approximant from real spectra and actual Hilbert parent
approximations. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.ProjectionPolynomial
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ProjectionFrame
open RoughRegime.HilbertGram RoughRegime.ComplexDerivativeBridge RoughRegime.BilinearDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single source constant controls the actual polynomial on a complex
neighborhood and its actual Euclidean gradient at every population parameter.
The gradient smallness follows from membership of the approximating functions
in the true parent spaces and their Hölder approximation errors. -/
theorem uniform_incrementPolynomial_holder {p n a b : ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℝ)) (hV : Bornology.IsBounded V)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (hΩ : ∀ x ∈ V, (Ω.map (MvPolynomial.eval x)).IsHermitian)
    (hSpec : ∀ x ∈ V, spectrum ℝ (Ω.map (MvPolynomial.eval x)) ⊆ Set.Icc lo hi)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (α β Ha Hb : ℝ) (hα : 0 < α) (hβ : 0 < β) (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      (∀ t : Fin p → ℂ, (∃ x ∈ V, ‖t - realParametersCLM p x‖ < ε) → ∀ m,
        ‖MvPolynomial.eval t (complexify (incrementPolynomial lo hi Ω La Lb u v m))‖ ≤ C) ∧
      (∀ x ∈ V, ∀ (z : Fin n → E), LinearIndependent ℝ z →
        Ω.map (MvPolynomial.eval x) = Matrix.gram ℝ z →
        ∀ f g ta tb : E,
        ta ∈ basisSpan (parentBasis z La) → tb ∈ basisSpan (parentBasis z Lb) →
        (fun i => MvPolynomial.eval x (u i)) = moments z f →
        (fun i => MvPolynomial.eval x (v i)) = moments z g →
        ∀ h : ℝ, 0 < h → h ≤ 1 →
        ‖f - ta‖ ≤ Ha * h ^ α → ‖g - tb‖ ≤ Hb * h ^ β → ∀ m,
        ‖polynomialGradient (incrementPolynomial lo hi Ω La Lb u v m) x‖ ≤
          C * h ^ min (min α β) 1) := by
  obtain ⟨ε, A, hε, hε1, hA, hcomplex, hgradient⟩ :=
    uniform_incrementPolynomial_gradient lo hi hlo hlt V hV Ω hΩ hSpec La Lb hLa hLb u v
  have hhi : 0 < hi := hlo.trans hlt
  let Ka := 2 * hi ^ a * Real.sqrt hi
  let Kb := 2 * hi ^ b * Real.sqrt hi
  let D := Real.sqrt p * derivativeConstant n A ε
  let C := max ((n : ℝ) ^ 2 * A ^ 3)
    (D * (Ka * Ha + Kb * Hb + (Ka * Ha) * (Kb * Hb)))
  have hKa : 0 ≤ Ka := by dsimp [Ka]; positivity
  have hKb : 0 ≤ Kb := by dsimp [Kb]; positivity
  have hD : 0 ≤ D := by dsimp [D, derivativeConstant]; positivity
  have hC : 0 ≤ C := (by positivity : 0 ≤ (n : ℝ) ^ 2 * A ^ 3).trans (le_max_left _ _)
  refine ⟨ε, C, hε, hε1, hC, ?_, ?_⟩
  · intro t ht m
    exact (hcomplex t ht m).trans (le_max_left _ _)
  · intro x hx z hz hGram f g ta tb hta htb hu hv h hh hh1 hfa hgb m
    have hsZ : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi := by
      rw [← hGram]
      exact hSpec x hx
    let U := ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω La u i))‖
    let W := ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω Lb v i))‖
    have hU : U ≤ (Ka * Ha) * h ^ α := by
      have hb := residualMomentPolynomial_parent_bound lo hi hlo hlt x Ω La hLa u
        z hz hGram hsZ f ta hta hu
      exact hb.trans ((mul_le_mul_of_nonneg_left hfa hKa).trans_eq (mul_assoc Ka Ha (h ^ α)).symm)
    have hW : W ≤ (Kb * Hb) * h ^ β := by
      have hb := residualMomentPolynomial_parent_bound lo hi hlo hlt x Ω Lb hLb v
        z hz hGram hsZ g tb htb hv
      exact hb.trans ((mul_le_mul_of_nonneg_left hgb hKb).trans_eq (mul_assoc Kb Hb (h ^ β)).symm)
    have hsum := residual_holder_scale hh hh1 hα hβ
      (mul_nonneg hKa hHa) (mul_nonneg hKb hHb) (norm_nonneg _) (norm_nonneg _) hU hW
    calc
      _ ≤ D * (U + W + U * W) := hgradient x hx m
      _ ≤ D * ((Ka * Ha + Kb * Hb + (Ka * Ha) * (Kb * Hb)) * h ^ min (min α β) 1) :=
        mul_le_mul_of_nonneg_left hsum hD
      _ = (D * (Ka * Ha + Kb * Hb + (Ka * Ha) * (Kb * Hb))) * h ^ min (min α β) 1 :=
        (mul_assoc _ _ _).symm
      _ ≤ C * h ^ min (min α β) 1 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hh.le _)

end RoughRegime.ProjectionIncrementComplex
