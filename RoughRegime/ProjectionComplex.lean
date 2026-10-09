module

public import RoughRegime.ComplexPolynomialKernel
public import RoughRegime.UniformExpressionFamily
public import RoughRegime.ProjectionIncrementPolynomial
public import RoughRegime.ComplexDerivativeBridge


@[expose] public section
/-! Uniform complex bounds for the actual substituted projection polynomials. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionComplex
open RoughRegime.KernelExpressions RoughRegime.ComplexPolynomialKernel
open RoughRegime.CombinedPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.Upper RoughRegime.ComplexDerivativeBridge

 def complexEvaluation {σ : Type*} (t : σ → ℂ) : MvPolynomial σ ℝ →+* ℂ :=
  MvPolynomial.eval₂Hom Complex.ofRealHom t

lemma complexEvaluation_eq {p : ℕ} (t : Fin p → ℂ) (P : MvPolynomial (Fin p) ℝ) :
    complexEvaluation t P = MvPolynomial.eval t (complexify P) := by
  rw [complexify, MvPolynomial.eval_map]
  rfl

lemma complexEvaluation_continuous {p : ℕ} (P : MvPolynomial (Fin p) ℝ) :
    Continuous (fun t : Fin p → ℂ => complexEvaluation t P) := by
  simpa only [complexEvaluation_eq] using (complexify P).continuous_eval

def kernelFamilyDims {N : ℕ} (n : ℕ) (dims : Fin N → ℕ) : Option (Fin N) → ℕ
  | none => n
  | some i => dims i

def kernelFamily {p N n : ℕ} {dims : Fin N → ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ)) :
    (i : Option (Fin N)) → (Fin p → ℂ) →
      Matrix (Fin (kernelFamilyDims n dims i)) (Fin (kernelFamilyDims n dims i)) ℂ
  | none, t => Ω.map (complexEvaluation t)
  | some i, t => (M i).map (complexEvaluation t)

def entryExpression {p N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ) (a b : Fin n) :
    Expression p (kernelFamilyDims n dims) :=
  .mul (.polynomial (C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ : ℝ)))
    (.mul (.kernelEntry none a b)
      (indexedProd (fun i : Fin N => determinantExpression (some i))))

lemma entryExpression_series {p N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ))
    (t : Fin p → ℂ) (a b : Fin n) :
    (entryExpression dims lo hi a b).series lo hi (kernelFamily Ω M) t =
      PowerSeries.C (((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ : ℝ) : ℂ) *
        (kernelMatrixSeries lo hi (Ω.map (complexEvaluation t)) a b *
          ∏ i, (kernelMatrixSeries lo hi ((M i).map (complexEvaluation t))).det) := by
  simp [entryExpression, Expression.series, indexedProd_series,
    determinantExpression_series, kernelFamily, kernelMatrixSeries]
  exact Or.inl rfl

/-- Exact complex evaluation after substituting the actual affine Gram entries. -/
lemma truncationPolynomialMatrix_complex_eval {p N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ))
    (t : Fin p → ℂ) (m : ℕ) (a b : Fin n) :
    complexEvaluation t (truncationPolynomialMatrix lo hi Ω M m a b) =
      ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k
        ((entryExpression dims lo hi a b).series lo hi (kernelFamily Ω M) t) := by
  rw [entryExpression_series]
  simp only [PowerSeries.coeff_C_mul, ← Finset.mul_sum]
  unfold truncationPolynomialMatrix
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (complexEvaluation t).comp (C : ℝ →+* MvPolynomial (Fin p) ℝ) =
      Complex.ofRealHom := by ext r; simp [complexEvaluation]
  rw [hc]
  have hv : (fun i => complexEvaluation t (polynomialEntryValuation Ω M i)) =
      complexEntryValuation (Ω.map (complexEvaluation t))
        (fun i => (M i).map (complexEvaluation t)) := by
    funext i
    cases i <;> rfl
  rw [hv]
  exact truncationEntryPolynomial_eval_complex dims lo hi _ _ a b m

/-- One neighborhood and one bound for all entries and all truncation degrees.
The hypotheses are precisely the source real-base spectral conditions. -/
theorem uniform_truncationPolynomialMatrix {p N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℂ)) (hV : Bornology.IsBounded V)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ))
    (hHerm : ∀ i t, t ∈ V → (kernelFamily Ω M i t).IsHermitian)
    (hSpec : ∀ i t, t ∈ V → spectrum ℝ (kernelFamily Ω M i t) ⊆ Set.Icc lo hi) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) → ∀ m a b,
        ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix lo hi Ω M m a b))‖ ≤ C := by
  have hM : ∀ i, Continuous (kernelFamily Ω M i) := by
    intro i
    cases i <;> exact continuous_pi (fun a => continuous_pi (fun b => complexEvaluation_continuous _))
  obtain ⟨ε, C, hε, hε1, hC, hb⟩ := uniform_finite_expression_truncations
    lo hi hlo hlt V hV (kernelFamily Ω M) hM hHerm hSpec
      (fun ab : Fin n × Fin n => entryExpression dims lo hi ab.1 ab.2)
  refine ⟨ε, C, hε, hε1, hC, ?_⟩
  intro t ht m a b
  rw [← complexEvaluation_eq, truncationPolynomialMatrix_complex_eval]
  exact hb t ht (a, b) m

end RoughRegime.ProjectionComplex
