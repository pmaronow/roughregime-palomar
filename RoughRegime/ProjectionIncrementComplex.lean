module

public import RoughRegime.ProjectionComplexBounds
public import RoughRegime.BilinearDerivative


@[expose] public section
/-! The genuine source Gram-residual approximant: uniform complex bounds from
real population spectra, and its actual small Euclidean gradient. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.ProjectionComplex RoughRegime.ComplexGram
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ProjectionError
open RoughRegime.ProjectionGram RoughRegime.HilbertGram RoughRegime.ProjectionFrame
open RoughRegime.ComplexDerivativeBridge RoughRegime.BilinearDerivative

lemma complexEvaluation_real {p : ℕ} (x : Fin p → ℝ) (P : MvPolynomial (Fin p) ℝ) :
    complexEvaluation (realParametersCLM p x) P = (MvPolynomial.eval x P : ℂ) := by
  change MvPolynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ x) P = _
  rw [← MvPolynomial.eval₂_comp]
  rfl

lemma complexEvaluation_matrix_real {p n a : ℕ} (x : Fin p → ℝ)
    (P : Matrix (Fin n) (Fin a) (MvPolynomial (Fin p) ℝ)) :
    P.map (complexEvaluation (realParametersCLM p x)) =
      (P.map (MvPolynomial.eval x)).map Complex.ofReal := by
  ext i j
  exact complexEvaluation_real x (P i j)

def realGramFamily {n a b : ℕ} (Ω : Matrix (Fin n) (Fin n) ℝ)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ) :
    (i : Option (Fin 2)) → Matrix (Fin (kernelFamilyDims n (twoDims a b) i))
      (Fin (kernelFamilyDims n (twoDims a b) i)) ℝ
  | none => Ω
  | some i => twoGrams Ω La Lb i

lemma kernelFamily_real {p n a b : ℕ} (x : Fin p → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (i : Option (Fin 2)) :
    kernelFamily Ω (twoGramPolynomials Ω La Lb) i (realParametersCLM p x) =
      (realGramFamily (Ω.map (MvPolynomial.eval x)) La Lb i).map Complex.ofReal := by
  cases i with
  | none => exact complexEvaluation_matrix_real x Ω
  | some i =>
    rw [kernelFamily, complexEvaluation_matrix_real]
    exact congrArg (fun A => A.map Complex.ofReal)
      (congrFun (twoGramPolynomials_eval x Ω La Lb) i)

lemma realGramFamily_isHermitian {n a b : ℕ} (Ω : Matrix (Fin n) (Fin n) ℝ)
    (hΩ : Ω.IsHermitian) (La : Matrix (Fin n) (Fin a) ℝ)
    (Lb : Matrix (Fin n) (Fin b) ℝ) (i : Option (Fin 2)) :
    (realGramFamily Ω La Lb i).IsHermitian := by
  cases i with
  | none => exact hΩ
  | some i =>
    fin_cases i
    · change (Laᵀ * Ω * La).IsHermitian
      simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_mul La hΩ
    · change (Lbᵀ * Ω * Lb).IsHermitian
      simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_mul Lb hΩ

lemma realGramFamily_spectrum {n a b : ℕ} (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) ℝ)
    (hΩ : Ω.IsHermitian) (hSpec : spectrum ℝ Ω ⊆ Set.Icc lo hi)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1) (i : Option (Fin 2)) :
    spectrum ℝ (realGramFamily Ω La Lb i) ⊆ Set.Icc lo hi := by
  cases i with
  | none => exact hSpec
  | some i =>
    fin_cases i
    · exact ProjectionGram.gram_spectrum_subset lo hi Ω hΩ hSpec La hLa
    · exact ProjectionGram.gram_spectrum_subset lo hi Ω hΩ hSpec Lb hLb

/-- The actual polynomial of Lemma 6 is bounded on one complex neighborhood of
any bounded real population set, uniformly in `m`. Only the child Gram spectral
condition is supplied; both parent conditions are derived from real orthonormal
columns, including zero-dimensional parents. -/
theorem uniform_incrementPolynomial_components {p n a b : ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℝ)) (hV : Bornology.IsBounded V)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (hΩ : ∀ x ∈ V, (Ω.map (MvPolynomial.eval x)).IsHermitian)
    (hSpec : ∀ x ∈ V, spectrum ℝ (Ω.map (MvPolynomial.eval x)) ⊆ Set.Icc lo hi)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (u v : Fin n → MvPolynomial (Fin p) ℝ) :
    ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ A ∧
      ∀ t : Fin p → ℂ, (∃ x ∈ V, ‖t - realParametersCLM p x‖ < ε) →
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial Ω La u i))‖ ≤ A) ∧
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial Ω Lb v i))‖ ≤ A) ∧
        (∀ m i j, ‖MvPolynomial.eval t (complexify
          (truncationPolynomialMatrix lo hi Ω (twoGramPolynomials Ω La Lb) m i j))‖ ≤ A) ∧
        (∀ m, ‖MvPolynomial.eval t (complexify (incrementPolynomial lo hi Ω La Lb u v m))‖ ≤
          (n : ℝ) ^ 2 * A ^ 3) := by
  have hh : ∀ i t, t ∈ realParametersCLM p '' V →
      (kernelFamily Ω (twoGramPolynomials Ω La Lb) i t).IsHermitian := by
    intro i t ht
    obtain ⟨x, hx, rfl⟩ := ht
    rw [kernelFamily_real]
    exact map_ofReal_isHermitian _ (realGramFamily_isHermitian _ (hΩ x hx) La Lb i)
  have hs : ∀ i t, t ∈ realParametersCLM p '' V →
      spectrum ℝ (kernelFamily Ω (twoGramPolynomials Ω La Lb) i t) ⊆ Set.Icc lo hi := by
    intro i t ht
    obtain ⟨x, hx, rfl⟩ := ht
    rw [kernelFamily_real]
    exact map_ofReal_spectrum_subset lo hi _ (realGramFamily_isHermitian _ (hΩ x hx) La Lb i)
      (realGramFamily_spectrum lo hi _ (hΩ x hx) (hSpec x hx) La Lb hLa hLb i)
  obtain ⟨ε, A, hε, hε1, hA, hb⟩ := uniform_bilinear_truncations lo hi hlo hlt
    (realParametersCLM p '' V) (hV.image (realParametersCLM p)) Ω
    (twoGramPolynomials Ω La Lb) hh hs
    (residualMomentPolynomial Ω La u) (residualMomentPolynomial Ω Lb v)
  refine ⟨ε, A, hε, hε1, hA, ?_⟩
  intro t ht
  obtain ⟨x, hx, hnear⟩ := ht
  exact hb t ⟨realParametersCLM p x, ⟨x, hx, rfl⟩, hnear⟩

end RoughRegime.ProjectionIncrementComplex
