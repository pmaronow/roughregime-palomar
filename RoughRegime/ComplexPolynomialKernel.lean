module

public import RoughRegime.KernelExpressionFinite
public import RoughRegime.CombinedPolynomial


@[expose] public section
/-! Complex evaluation of the actual real coefficient polynomials of Lemma 5. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix Polynomial
namespace RoughRegime.ComplexPolynomialKernel
open RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant RoughRegime.CombinedPolynomial
open RoughRegime.KernelExpressions RoughRegime.ComplexKernel RoughRegime.Upper

lemma variableMatrix_power_eval_complex {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (k : ℕ) (a b : n) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun ij : n × n => M ij.1 ij.2)
      ((variableMatrix n ^ k) a b) = (M ^ k) a b := by
  let φ := MvPolynomial.eval₂Hom Complex.ofRealHom (fun ij : n × n => M ij.1 ij.2)
  have hb : φ.mapMatrix (variableMatrix n) = M := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, variableMatrix, φ]
  change (φ.mapMatrix (variableMatrix n ^ k)) a b = _
  rw [map_pow, hb]

lemma matrixEntryPolynomial_eval_complex {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (M : Matrix n n ℂ) (a b : n) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun ij : n × n => M ij.1 ij.2)
      (matrixEntryPolynomial q a b) = (Polynomial.aeval M q) a b := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    variableMatrix_power_eval_complex, Matrix.sum_apply, ← Algebra.smul_def,
    Matrix.smul_apply]
  rfl

lemma variableKernelSeries_eval_complex {n : ℕ} (lo hi : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom
      (fun ij : Fin n × Fin n => M ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi (n := Fin n)) = kernelMatrixSeries lo hi M := by
  ext a b k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, variableKernelSeries,
    kernelMatrixSeries, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact matrixEntryPolynomial_eval_complex _ M a b

def complexEntryValuation {N n : ℕ} {dims : Fin N → ℕ}
    (M0 : Matrix (Fin n) (Fin n) ℂ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ) : Variables n dims → ℂ
  | Sum.inl ab => M0 ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2

lemma eval_renamed_series_complex {V W : Type*} (f : V → W) (values : W → ℂ)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (values ∘ f)) P := by
  ext k
  simp only [PowerSeries.coeff_map]
  exact MvPolynomial.eval₂_rename Complex.ofRealHom f values _

lemma inverseVariableSeries_eval_complex {N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n) (Fin n) ℂ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ) (a b : Fin n) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexEntryValuation M0 M))
      (inverseVariableSeries n dims lo hi a b) = kernelMatrixSeries lo hi M0 a b := by
  rw [inverseVariableSeries, eval_renamed_series_complex]
  exact congrArg (fun A => A a b) (variableKernelSeries_eval_complex lo hi M0)

lemma determinantVariableSeries_eval_complex {N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n) (Fin n) ℂ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ) (i : Fin N) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexEntryValuation M0 M))
      (determinantVariableSeries n dims lo hi i) = (kernelMatrixSeries lo hi (M i)).det := by
  rw [determinantVariableSeries, eval_renamed_series_complex, RingHom.map_det]
  exact congrArg Matrix.det (variableKernelSeries_eval_complex lo hi (M i))

lemma combinedVariableSeries_eval_complex {N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n) (Fin n) ℂ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ) (a b : Fin n) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexEntryValuation M0 M))
      (combinedVariableSeries n dims lo hi a b) =
      kernelMatrixSeries lo hi M0 a b * ∏ i, (kernelMatrixSeries lo hi (M i)).det := by
  simp only [combinedVariableSeries, map_mul, map_prod,
    inverseVariableSeries_eval_complex, determinantVariableSeries_eval_complex]

lemma combinedCoefficientPolynomial_eval_complex {N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n) (Fin n) ℂ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ) (a b : Fin n) (k : ℕ) :
    MvPolynomial.eval₂ Complex.ofRealHom (complexEntryValuation M0 M)
      (combinedCoefficientPolynomial n dims lo hi a b k) =
      PowerSeries.coeff k (kernelMatrixSeries lo hi M0 a b *
        ∏ i, (kernelMatrixSeries lo hi (M i)).det) := by
  have he := congrArg (fun P : PowerSeries ℂ => PowerSeries.coeff k P)
    (combinedVariableSeries_eval_complex dims lo hi M0 M a b)
  rw [PowerSeries.coeff_map] at he
  exact he

lemma truncationEntryPolynomial_eval_complex {N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n) (Fin n) ℂ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ) (a b : Fin n) (m : ℕ) :
    MvPolynomial.eval₂ Complex.ofRealHom (complexEntryValuation M0 M)
      (truncationEntryPolynomial n dims lo hi a b m) =
      ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ : ℝ) *
        ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k
          (kernelMatrixSeries lo hi M0 a b * ∏ i, (kernelMatrixSeries lo hi (M i)).det) := by
  simp [truncationEntryPolynomial, combinedCoefficientPolynomial_eval_complex]

end RoughRegime.ComplexPolynomialKernel
