module

public import RoughRegime.ProjectionIncrementError


@[expose] public section
/-! Simultaneous source Lemma 6 conclusions for the actual finite Gram-residual
polynomial, ready for the genuine dyadic population-moment instantiation. -/
noncomputable section
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MvPolynomial
namespace RoughRegime.LocalProjectionApproximation
open RoughRegime.ProjectionIncrementComplex RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.KernelExpressions RoughRegime.ComplexDerivativeBridge
open RoughRegime.HilbertGram RoughRegime.Upper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The concrete `P_m` simultaneously has source degree, true Hilbert increment
error, a uniform complex neighborhood bound, and the small actual Euclidean
gradient. No inverse approximation, analytic bound, derivative bound or small
residual estimate is supplied as a hypothesis. -/
theorem local_projection_approximation {p n a b : ℕ} [Nonempty (Fin n)]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℝ)) (hV : Bornology.IsBounded V)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (hΩ : ∀ x ∈ V, (Ω.map (MvPolynomial.eval x)).IsHermitian)
    (hSpec : ∀ x ∈ V, spectrum ℝ (Ω.map (MvPolynomial.eval x)) ⊆ Set.Icc lo hi)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (hΩdeg : ∀ i j, (Ω i j).totalDegree ≤ 1)
    (hudeg : ∀ i, (u i).totalDegree ≤ 1) (hvdeg : ∀ i, (v i).totalDegree ≤ 1)
    (α β Ha Hb : ℝ) (hα : 0 < α) (hβ : 0 < β) (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧
      (∀ m, (incrementPolynomial lo hi Ω La Lb u v m).totalDegree ≤ m + a + b + 2) ∧
      (∀ t : Fin p → ℂ, (∃ x ∈ V, ‖t - realParametersCLM p x‖ < ε) → ∀ m,
        ‖MvPolynomial.eval t (complexify (incrementPolynomial lo hi Ω La Lb u v m))‖ ≤ C) ∧
      (∀ x ∈ V, ∀ (z : Fin n → E), LinearIndependent ℝ z →
        Ω.map (MvPolynomial.eval x) = Matrix.gram ℝ z →
        basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb) →
        ∀ f g ta tb : E,
        ta ∈ basisSpan (parentBasis z La) → tb ∈ basisSpan (parentBasis z Lb) →
        (fun i => MvPolynomial.eval x (u i)) = moments z f →
        (fun i => MvPolynomial.eval x (v i)) = moments z g →
        ∀ h : ℝ, 0 < h → h ≤ 1 →
        ‖f - ta‖ ≤ Ha * h ^ α → ‖g - tb‖ ≤ Hb * h ^ β → ∀ m,
        (‖(⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ -
          ⟪(basisSpan (parentBasis z Lb)).starProjection f,
            (basisSpan (parentBasis z Lb)).starProjection g⟫) -
          MvPolynomial.eval x (incrementPolynomial lo hi Ω La Lb u v m)‖ ≤
          C * h ^ (α + β) * ((m + 1 : ℕ) : ℝ) ^ (a + b) * intervalRho lo hi ^ m) ∧
        (‖polynomialGradient (incrementPolynomial lo hi Ω La Lb u v m) x‖ ≤
          C * h ^ min (min α β) 1)) := by
  obtain ⟨ε, C0, hε, hε1, hC0, hcomplex, hgradient⟩ :=
    uniform_incrementPolynomial_holder (E := E) lo hi hlo hlt V hV Ω hΩ hSpec
      La Lb hLa hLb u v α β Ha Hb hα hβ hHa hHb
  let K := incrementErrorConstant lo hi a b Ha Hb
  let C := max C0 K + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_left C0 K]
  have hC0C : C0 ≤ C := by dsimp [C]; linarith [le_max_left C0 K]
  have hKC : K ≤ C := by dsimp [C]; linarith [le_max_right C0 K]
  refine ⟨ε, C, hε, hε1, hC,
    fun m => incrementPolynomial_degree lo hi Ω La Lb u v m hΩdeg hudeg hvdeg,
    fun t ht m => (hcomplex t ht m).trans hC0C, ?_⟩
  intro x hx z hz hGram hsub f g ta tb hta htb hu hv h hh hh1 hfa hgb m
  have hsZ : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi := by
    rw [← hGram]
    exact hSpec x hx
  constructor
  · apply (incrementPolynomial_holder_error lo hi hlo hlt x Ω La Lb hLa hLb u v
      z hz hGram hsZ hsub f g ta tb hta htb hu hv h α β Ha Hb hh hHa hHb hfa hgb m).trans
    have hρ := (intervalRho_pos lo hi hlo hlt).le
    gcongr
  · exact (hgradient x hx z hz hGram f g ta tb hta htb hu hv h hh hh1 hfa hgb m).trans
      (mul_le_mul_of_nonneg_right hC0C (Real.rpow_nonneg hh.le _))

end RoughRegime.LocalProjectionApproximation
