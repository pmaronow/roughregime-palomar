module

public import RoughRegime.ProjectionComplex
public import RoughRegime.ComplexGram


@[expose] public section
/-! Degree-independent complex bounds for the concrete bilinear approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionComplex
open RoughRegime.KernelExpressions RoughRegime.ProjectionApproximation
open RoughRegime.ComplexDerivativeBridge

lemma bilinearPolynomial_complex_eval {p n : ℕ} (t : Fin p → ℂ)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ)) :
    MvPolynomial.eval t (complexify (bilinearPolynomial u S v)) =
      ∑ i : Fin n, ∑ j : Fin n,
        MvPolynomial.eval t (complexify (u i)) *
          MvPolynomial.eval t (complexify (S i j)) *
          MvPolynomial.eval t (complexify (v j)) := by
  simp only [← complexEvaluation_eq, bilinearPolynomial, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.mul_sum, mul_assoc]

lemma bilinearPolynomial_complex_bound {p n : ℕ} (t : Fin p → ℂ)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ)) (A : ℝ) (hA : 0 ≤ A)
    (hu : ∀ i, ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A)
    (hv : ∀ i, ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A)
    (hS : ∀ i j, ‖MvPolynomial.eval t (complexify (S i j))‖ ≤ A) :
    ‖MvPolynomial.eval t (complexify (bilinearPolynomial u S v))‖ ≤ (n : ℝ) ^ 2 * A ^ 3 := by
  rw [bilinearPolynomial_complex_eval]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
      ‖MvPolynomial.eval t (complexify (u i))‖ *
        ‖MvPolynomial.eval t (complexify (S i j))‖ *
        ‖MvPolynomial.eval t (complexify (v j))‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul] using (norm_sum_le Finset.univ
        (fun j : Fin n => MvPolynomial.eval t (complexify (u i)) *
          MvPolynomial.eval t (complexify (S i j)) * MvPolynomial.eval t (complexify (v j))))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, A * A * A := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (mul_le_mul (hu i) (hS i j) (norm_nonneg _) hA)
        (hv j) (norm_nonneg _) (mul_nonneg hA hA)
    _ = _ := by simp; ring

/-- The fixed residual polynomials and every actual combined-index matrix
truncation have one common complex neighborhood and bound. Consequently the
actual scalar bilinear polynomial is uniformly bounded independently of `m`. -/
theorem uniform_bilinear_truncations {p N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℂ)) (hV : Bornology.IsBounded V)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ))
    (hHerm : ∀ i t, t ∈ V → (kernelFamily Ω M i t).IsHermitian)
    (hSpec : ∀ i t, t ∈ V → spectrum ℝ (kernelFamily Ω M i t) ⊆ Set.Icc lo hi)
    (u v : Fin n → MvPolynomial (Fin p) ℝ) :
    ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ A ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) →
        (∀ i, ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A) ∧
        (∀ i, ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A) ∧
        (∀ m i j, ‖MvPolynomial.eval t
          (complexify (truncationPolynomialMatrix lo hi Ω M m i j))‖ ≤ A) ∧
        (∀ m, ‖MvPolynomial.eval t (complexify
          (bilinearPolynomial u (truncationPolynomialMatrix lo hi Ω M m) v))‖ ≤
            (n : ℝ) ^ 2 * A ^ 3) := by
  let f : ((Fin n ⊕ Fin n) ⊕ (Fin n × Fin n)) → Expression p (kernelFamilyDims n dims)
    | Sum.inl (Sum.inl i) => .polynomial (complexify (u i))
    | Sum.inl (Sum.inr i) => .polynomial (complexify (v i))
    | Sum.inr ij => entryExpression dims lo hi ij.1 ij.2
  have hM : ∀ i, Continuous (kernelFamily Ω M i) := by
    intro i
    cases i <;> exact continuous_pi (fun a => continuous_pi (fun b => complexEvaluation_continuous _))
  obtain ⟨ε, A, hε, hε1, hA, hb⟩ := uniform_finite_expression_truncations
    lo hi hlo hlt V hV (kernelFamily Ω M) hM hHerm hSpec f
  refine ⟨ε, A, hε, hε1, hA, ?_⟩
  intro t ht
  have hu (i : Fin n) : ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A := by
    simpa [f, Expression.series] using hb t ht (Sum.inl (Sum.inl i)) 0
  have hv (i : Fin n) : ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A := by
    simpa [f, Expression.series] using hb t ht (Sum.inl (Sum.inr i)) 0
  have hS (m : ℕ) (i j : Fin n) :
      ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix lo hi Ω M m i j))‖ ≤ A := by
    rw [← complexEvaluation_eq, truncationPolynomialMatrix_complex_eval]
    exact hb t ht (Sum.inr (i, j)) m
  exact ⟨hu, hv, hS, fun m => bilinearPolynomial_complex_bound t u v _ A hA hu hv (hS m)⟩

end RoughRegime.ProjectionComplex
