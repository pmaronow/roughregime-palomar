module

public import RoughRegime.ProjectionApproximation
public import RoughRegime.ProjectionError


@[expose] public section
/-! The actual Gram-residual approximant is a polynomial of the precise source
combined degree. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionIncrementPolynomial
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionError RoughRegime.ProjectionGram

def twoGramPolynomials {σ : Type*} {n a b : ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ) :
    (i : Fin 2) → Matrix (Fin (twoDims a b i)) (Fin (twoDims a b i)) (MvPolynomial σ ℝ) :=
  Fin.cases (gramPolynomial Ω La) (fun _ => gramPolynomial Ω Lb)

def incrementPolynomial {σ : Type*} {n a b : ℕ} (lo hi : ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (u v : Fin n → MvPolynomial σ ℝ) (m : ℕ) : MvPolynomial σ ℝ :=
  bilinearPolynomial (residualMomentPolynomial Ω La u)
    (truncationPolynomialMatrix lo hi Ω (twoGramPolynomials Ω La Lb) m)
    (residualMomentPolynomial Ω Lb v)

/-- Source Lemma 6's concrete total-degree bound `m+ν_a+ν_b+2`. -/
theorem incrementPolynomial_degree {σ : Type*} {n a b : ℕ} (lo hi : ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (u v : Fin n → MvPolynomial σ ℝ) (m : ℕ)
    (hΩ : ∀ i j, (Ω i j).totalDegree ≤ 1)
    (hu : ∀ i, (u i).totalDegree ≤ 1) (hv : ∀ i, (v i).totalDegree ≤ 1) :
    (incrementPolynomial lo hi Ω La Lb u v m).totalDegree ≤ m + a + b + 2 := by
  have hM : ∀ i k l, (twoGramPolynomials Ω La Lb i k l).totalDegree ≤ 1 := by
    intro i
    fin_cases i
    · exact gramPolynomial_degree Ω La hΩ
    · exact gramPolynomial_degree Ω Lb hΩ
  exact (bilinearPolynomial_degree _ _ _ (a + 1) m (b + 1)
    (residualMomentPolynomial_degree Ω La u hΩ hu)
    (truncationPolynomialMatrix_degree lo hi Ω _ hΩ hM m)
    (residualMomentPolynomial_degree Ω Lb v hΩ hv)).trans_eq (by omega)

lemma twoGramPolynomials_eval {σ : Type*} {n a b : ℕ} (x : σ → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ) :
    (fun i => (twoGramPolynomials Ω La Lb i).map (MvPolynomial.eval x)) =
      twoGrams (Ω.map (MvPolynomial.eval x)) La Lb := by
  funext i
  fin_cases i
  · exact gramPolynomial_eval x Ω La
  · exact gramPolynomial_eval x Ω Lb

/-- Exact evaluation identifies the polynomial with the actual combined-index
matrix truncation applied to the genuine residual moment vectors. -/
theorem incrementPolynomial_eval {σ : Type*} {n a b : ℕ} (x : σ → ℝ) (lo hi : ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (u v : Fin n → MvPolynomial σ ℝ) (m : ℕ) :
    MvPolynomial.eval x (incrementPolynomial lo hi Ω La Lb u v m) =
      incrementApproximation lo hi (Ω.map (MvPolynomial.eval x)) La Lb
        (fun i => MvPolynomial.eval x (u i)) (fun i => MvPolynomial.eval x (v i)) m := by
  rw [incrementPolynomial, bilinearPolynomial_eval,
    truncationPolynomialMatrix_eval, twoGramPolynomials_eval,
    residualMomentPolynomial_eval, residualMomentPolynomial_eval]
  rfl

end RoughRegime.ProjectionIncrementPolynomial
