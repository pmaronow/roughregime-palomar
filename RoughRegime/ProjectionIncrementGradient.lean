module

public import RoughRegime.ProjectionIncrementComplex


@[expose] public section
/-! Actual Euclidean-gradient estimates for the source increment polynomial,
with smallness proved from genuine Hilbert parent approximation. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.ProjectionComplex
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ProjectionFrame
open RoughRegime.HilbertGram RoughRegime.ProjectionGram
open RoughRegime.ComplexDerivativeBridge RoughRegime.BilinearDerivative

 def polynomialGradient {p : ℕ} (P : MvPolynomial (Fin p) ℝ) (x : Fin p → ℝ) :=
  euclidean (fun j => fderiv ℝ (fun y => MvPolynomial.eval y P) x (Pi.single j 1))

/-- One derived complex bound yields one genuine gradient bound for every
truncation degree and every population point. -/
theorem uniform_incrementPolynomial_gradient {p n a b : ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℝ)) (hV : Bornology.IsBounded V)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (hΩ : ∀ x ∈ V, (Ω.map (MvPolynomial.eval x)).IsHermitian)
    (hSpec : ∀ x ∈ V, spectrum ℝ (Ω.map (MvPolynomial.eval x)) ⊆ Set.Icc lo hi)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (u v : Fin n → MvPolynomial (Fin p) ℝ) :
    ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ A ∧
      (∀ t : Fin p → ℂ, (∃ x ∈ V, ‖t - realParametersCLM p x‖ < ε) → ∀ m,
        ‖MvPolynomial.eval t (complexify (incrementPolynomial lo hi Ω La Lb u v m))‖ ≤
          (n : ℝ) ^ 2 * A ^ 3) ∧
      (∀ x ∈ V, ∀ m,
        ‖polynomialGradient (incrementPolynomial lo hi Ω La Lb u v m) x‖ ≤
          (Real.sqrt p * derivativeConstant n A ε) *
            (‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω La u i))‖ +
             ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω Lb v i))‖ +
             ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω La u i))‖ *
             ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω Lb v i))‖)) := by
  obtain ⟨ε, A, hε, hε1, hA, hb⟩ := uniform_incrementPolynomial_components
    lo hi hlo hlt V hV Ω hΩ hSpec La Lb hLa hLb u v
  refine ⟨ε, A, hε, hε1, hA, fun t ht => (hb t ht).2.2.2, ?_⟩
  intro x hx m
  apply bilinearPolynomial_gradient_norm_bound _ _ _ x ε A hε hA
  · intro i t ht
    exact (hb t ⟨x, hx, ht⟩).1 i
  · intro i t ht
    exact (hb t ⟨x, hx, ht⟩).2.1 i
  · intro i j t ht
    exact (hb t ⟨x, hx, ht⟩).2.2.1 m i j

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine polynomial residual is small because the approximating function
lies in the parent space; the residual smallness is not an input. -/
lemma residualMomentPolynomial_parent_bound {p n a : ℕ} (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (x : Fin p → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (L : Matrix (Fin n) (Fin a) ℝ) (hL : Lᵀ * L = 1)
    (u : Fin n → MvPolynomial (Fin p) ℝ)
    (z : Fin n → E) (hz : LinearIndependent ℝ z)
    (hΩ : Ω.map (MvPolynomial.eval x) = Matrix.gram ℝ z)
    (hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi)
    (f t : E) (ht : t ∈ basisSpan (parentBasis z L))
    (hu : (fun i => MvPolynomial.eval x (u i)) = moments z f) :
    ‖euclidean (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω L u i))‖ ≤
      2 * hi ^ a * Real.sqrt hi * ‖f - t‖ := by
  rw [residualMomentPolynomial_eval, hΩ, hu]
  simpa only [Fintype.card_fin] using
    polynomialResidual_moment_norm_le_of_spectrum lo hi hlo hlt z hz hSpec L hL f t ht

/-- Exact source `h^min(α,β,1)` arithmetic, including the bilinear residual term. -/
lemma residual_holder_scale {h α β A B U V : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hu : U ≤ A * h ^ α) (hv : V ≤ B * h ^ β) :
    U + V + U * V ≤ (A + B + A * B) * h ^ min (min α β) 1 := by
  let s := min (min α β) 1
  have hsα : s ≤ α := (min_le_left _ _).trans (min_le_left _ _)
  have hsβ : s ≤ β := (min_le_left _ _).trans (min_le_right _ _)
  have hpα : h ^ α ≤ h ^ s := Real.rpow_le_rpow_of_exponent_ge hh hh1 hsα
  have hpβ : h ^ β ≤ h ^ s := Real.rpow_le_rpow_of_exponent_ge hh hh1 hsβ
  have hpβ1 : h ^ β ≤ 1 := Real.rpow_le_one hh.le hh1 hβ.le
  have hu' := hu.trans (mul_le_mul_of_nonneg_left hpα hA)
  have hv' := hv.trans (mul_le_mul_of_nonneg_left hpβ hB)
  have hv1 : V ≤ B := hv.trans (mul_le_of_le_one_right hB hpβ1)
  have huv : U * V ≤ (A * B) * h ^ s := by
    convert mul_le_mul hu' hv1 hV (mul_nonneg hA (Real.rpow_nonneg hh.le s)) using 1 <;> ring
  have := add_le_add (add_le_add hu' hv') huv
  simpa only [← add_mul, s] using this

end RoughRegime.ProjectionIncrementComplex
