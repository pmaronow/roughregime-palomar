module

public import RoughRegime.ComplexKernel
public import RoughRegime.ScalarDenominator


@[expose] public section
/-! Actual complex reciprocal matrix denominator and its spectral invertibility. -/
noncomputable section
open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace RoughRegime.ComplexKernel
open RoughRegime.Upper

def denominator {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  1 + (2 * (intervalRho lo hi : ℂ) * z) • normalizedArgument lo hi M +
    ((intervalRho lo hi : ℂ) ^ 2 * z ^ 2) • 1

def rationalKernel {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (1 - (intervalRho lo hi : ℂ) ^ 2 * z ^ 2) • Ring.inverse (denominator lo hi M z)

lemma complex_aeval_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℂ[X]) (d : n → ℂ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom ℂ) d) q = _
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]
  rfl

theorem aeval_isUnit_of_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (q : ℂ[X])
    (hq : ∀ i, q.eval (hM.eigenvalues i : ℂ) ≠ 0) :
    IsUnit (Polynomial.aeval M q) := by
  have he := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) q
  rw [← hM.spectral_theorem, complex_aeval_diagonal] at he
  rw [he]
  apply IsUnit.map
  apply Matrix.isUnit_diagonal.mpr
  apply Pi.isUnit_iff.mpr
  intro i
  exact isUnit_iff_ne_zero.mpr (hq i)

def denominatorPolynomial (lo hi : ℝ) (z : ℂ) : ℂ[X] :=
  1 + C (2 * (intervalRho lo hi : ℂ) * z) *
    (C (((intervalHalfWidth lo hi)⁻¹ : ℝ) : ℂ) * (X - C (intervalCenter lo hi : ℂ))) +
    C ((intervalRho lo hi : ℂ) ^ 2 * z ^ 2)

lemma denominator_eq_aeval {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (z : ℂ) :
    denominator lo hi M z = Polynomial.aeval M (denominatorPolynomial lo hi z) := by
  simp [denominator, denominatorPolynomial, normalizedArgument, argumentPolynomial,
    Algebra.smul_def, mul_assoc, IsScalarTower.algebraMap_apply ℝ ℂ (Matrix n n ℂ)]

lemma denominatorPolynomial_eval (lo hi t : ℝ) (z : ℂ) :
    (denominatorPolynomial lo hi z).eval (t : ℂ) =
      1 + 2 * (intervalRho lo hi : ℂ) * z *
        (((t - intervalCenter lo hi) / intervalHalfWidth lo hi : ℝ) : ℂ) +
        (intervalRho lo hi : ℂ) ^ 2 * z ^ 2 := by
  simp only [denominatorPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  push_cast
  ring

/-- Every Hermitian base matrix has a zero-free denominator on the source disk. -/
theorem denominator_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (z : ℂ)
    (hz : intervalRho lo hi * ‖z‖ < 1) :
    IsUnit (denominator lo hi M z) := by
  rw [denominator_eq_aeval]
  apply aeval_isUnit_of_eigenvalues M hM
  intro i
  rw [denominatorPolynomial_eval]
  exact scalarDenominator_ne_zero _ _ _ (intervalRho_pos lo hi hlo hlt)
    (interval_argument_mem lo hi _ hlo hlt (hSpec (hM.eigenvalues_mem_spectrum_real i))) hz

def normalizedDenominator {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : ℝ) (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  1 + (2 * (ρ : ℂ) * z) • A + ((ρ : ℂ) ^ 2 * z ^ 2) • 1

/-- The zero-free statement also uses the closed Hermitian unit ball, making it
directly suitable for compact parameter closures. -/
theorem normalizedDenominator_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : ℝ) (hρ : 0 < ρ) (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hAnorm : ‖A‖ ≤ 1) (z : ℂ) (hz : ρ * ‖z‖ < 1) :
    IsUnit (normalizedDenominator ρ A z) := by
  let q : ℂ[X] := 1 + C (2 * (ρ : ℂ) * z) * X + C ((ρ : ℂ) ^ 2 * z ^ 2)
  have he : normalizedDenominator ρ A z = Polynomial.aeval A q := by
    simp [normalizedDenominator, q, Algebra.smul_def]
  rw [he]
  apply aeval_isUnit_of_eigenvalues A hA
  intro i
  have : Nonempty n := ⟨i⟩
  have hb : |hA.eigenvalues i| ≤ 1 := by
    exact (spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)).trans hAnorm
  have ht : hA.eigenvalues i ∈ Set.Icc (-1) 1 := abs_le.mp hb
  simpa [q] using scalarDenominator_ne_zero ρ z (hA.eigenvalues i) hρ ht hz

end RoughRegime.ComplexKernel
