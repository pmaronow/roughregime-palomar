module

public import RoughRegime.MatrixDeterminant
public import RoughRegime.PowerSeriesAnalytic


@[expose] public section
/-! The actual reciprocal-kernel generating identity for arbitrary complex matrices. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial
namespace RoughRegime.ComplexKernel
open RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant RoughRegime.Upper

/-- The normalized affine polynomial used before the matrix Chebyshev expansion. -/
def argumentPolynomial (lo hi : ℝ) : ℝ[X] :=
  C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi))

lemma normalizedChebyshev_recurrence (lo hi : ℝ) (k : ℕ) :
    normalizedChebyshev lo hi (k + 2) =
      2 * argumentPolynomial lo hi * normalizedChebyshev lo hi (k + 1) -
        normalizedChebyshev lo hi k := by
  unfold normalizedChebyshev argumentPolynomial
  have ht := Polynomial.Chebyshev.T_add_two ℝ (k : ℤ)
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.ofNat_comp, Polynomial.X_comp] using congrArg
      (fun q : ℝ[X] => q.comp (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi)))) ht

lemma kernelCoefficientPolynomial_zero (lo hi : ℝ) :
    kernelCoefficientPolynomial lo hi 0 = 1 := by simp [kernelCoefficientPolynomial, normalizedChebyshev]

lemma kernelCoefficientPolynomial_one (lo hi : ℝ) :
    kernelCoefficientPolynomial lo hi 1 = -(C (2 * intervalRho lo hi) * argumentPolynomial lo hi) := by
  simp [kernelCoefficientPolynomial, normalizedChebyshev, argumentPolynomial]

lemma kernelCoefficientPolynomial_two (lo hi : ℝ) :
    kernelCoefficientPolynomial lo hi 2 =
      (C (2 * intervalRho lo hi) * argumentPolynomial lo hi) ^ 2 -
        (C (intervalRho lo hi ^ 2) + C (intervalRho lo hi ^ 2)) := by
  simp only [kernelCoefficientPolynomial, OfNat.ofNat_ne_zero, ite_false,
    normalizedChebyshev, Nat.cast_ofNat, Polynomial.Chebyshev.T_two, Polynomial.sub_comp,
    Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.ofNat_comp, Polynomial.X_comp,
    Polynomial.one_comp]
  simp only [map_mul, map_pow, map_neg, map_ofNat]
  change 2 * (-C (intervalRho lo hi)) ^ 2 * (2 * argumentPolynomial lo hi ^ 2 - 1) = _
  ring

lemma kernelCoefficientPolynomial_recurrence (lo hi : ℝ) (k : ℕ) :
    kernelCoefficientPolynomial lo hi (k + 3) =
      -(C (2 * intervalRho lo hi) * argumentPolynomial lo hi) *
        kernelCoefficientPolynomial lo hi (k + 2) -
      C (intervalRho lo hi ^ 2) * kernelCoefficientPolynomial lo hi (k + 1) := by
  have ht := normalizedChebyshev_recurrence lo hi (k + 1)
  rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at ht
  simp only [kernelCoefficientPolynomial, Nat.add_one_ne_zero, ite_false]
  rw [ht]
  simp only [map_mul, map_pow, map_neg, map_ofNat]
  rw [show k + 3 = (k + 1) + 2 by omega, show k + 2 = (k + 1) + 1 by omega, pow_add, pow_add]
  ring

/-- The complex matrix kernel uses the same actual real coefficient polynomials. -/
def kernelCoefficient {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)

def normalizedArgument {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  Polynomial.aeval M (argumentPolynomial lo hi)

def kernelPowerSeries {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) : PowerSeries (Matrix n n ℂ) :=
  PowerSeries.mk (kernelCoefficient lo hi M)

/-- Quadratic denominator in the common generating variable. -/
def denominatorPowerSeries {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) : PowerSeries (Matrix n n ℂ) :=
  1 + PowerSeries.C (2 * intervalRho lo hi • normalizedArgument lo hi M) * PowerSeries.X ^ 1 +
    PowerSeries.C (intervalRho lo hi ^ 2 • (1 : Matrix n n ℂ)) * PowerSeries.X ^ 2

/-- The recurrence determines the exact formal rational generating identity. -/
theorem generating_identity_of_recurrence {R : Type*} [Ring R]
    (f : PowerSeries R) (a b : R)
    (h0 : PowerSeries.coeff 0 f = 1) (h1 : PowerSeries.coeff 1 f = -a)
    (h2 : PowerSeries.coeff 2 f = a * a - (b + b))
    (hr : ∀ k, PowerSeries.coeff (k + 3) f =
      -a * PowerSeries.coeff (k + 2) f - b * PowerSeries.coeff (k + 1) f) :
    (1 + PowerSeries.C a * PowerSeries.X ^ 1 + PowerSeries.C b * PowerSeries.X ^ 2) * f =
      1 - PowerSeries.C b * PowerSeries.X ^ 2 := by
  ext k
  simp only [add_mul, one_mul, mul_assoc, map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C]
  rcases k with _ | _ | _ | k
  · simp [h0]
  · simp [h1, h0]
  · simp only [show (1 : ℕ) ≤ 2 by omega, show (2 : ℕ) ≤ 2 by omega, ite_true,
      h2, h1, h0, show (2 : ℕ) ≠ 0 by omega, ite_false]
    noncomm_ring
  · have hk1 : 1 ≤ k + 1 + 1 + 1 := by omega
    have hk2 : 2 ≤ k + 1 + 1 + 1 := by omega
    simp only [hk1, hk2, ite_true, show k + 1 + 1 + 1 - 1 = k + 2 by omega,
      show k + 1 + 1 + 1 - 2 = k + 1 by omega,
      show k + 1 + 1 + 1 ≠ 0 by omega, ite_false]
    rw [show k + 1 + 1 + 1 = k + 3 by omega, hr]
    noncomm_ring

/-- For every complex matrix the actual formal kernel satisfies QK=(1-ρ²z²)I. -/
theorem kernelPowerSeries_generating_identity {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) :
    denominatorPowerSeries lo hi M * kernelPowerSeries lo hi M =
      1 - PowerSeries.C (intervalRho lo hi ^ 2 • (1 : Matrix n n ℂ)) * PowerSeries.X ^ 2 := by
  have harg : Polynomial.aeval M (C (2 * intervalRho lo hi) * argumentPolynomial lo hi) =
      2 * intervalRho lo hi • normalizedArgument lo hi M := by
    simp only [normalizedArgument, map_mul, Polynomial.aeval_C, Algebra.smul_def, map_ofNat, mul_assoc]
  have hconst : Polynomial.aeval M (C (intervalRho lo hi ^ 2)) =
      intervalRho lo hi ^ 2 • (1 : Matrix n n ℂ) := by simp [Algebra.smul_def]
  apply generating_identity_of_recurrence
  · simp [kernelPowerSeries, kernelCoefficient, kernelCoefficientPolynomial_zero]
  · simp only [kernelPowerSeries, PowerSeries.coeff_mk, kernelCoefficient]
    rw [kernelCoefficientPolynomial_one, map_neg, harg]
  · simp only [kernelPowerSeries, PowerSeries.coeff_mk, kernelCoefficient]
    rw [kernelCoefficientPolynomial_two, map_sub, map_pow, harg, map_add, hconst, pow_two]
  · intro k
    simp only [kernelPowerSeries, PowerSeries.coeff_mk, kernelCoefficient]
    rw [kernelCoefficientPolynomial_recurrence, map_sub, map_mul, map_neg, harg, map_mul, hconst]

/-- A coarse geometric growth estimate gives a genuine positive convergence radius
for Chebyshev series at every complex matrix, before the uniform spectral argument. -/
theorem chebyshev_aeval_norm_le {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [NormOneClass R] (A : R) (k : ℕ) :
    ‖Polynomial.aeval A (Polynomial.Chebyshev.T ℝ (k : ℤ))‖ ≤ (2 * ‖A‖ + 1) ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [Nat.cast_one, Polynomial.Chebyshev.T_one, Polynomial.aeval_X, pow_one]
    nlinarith [norm_nonneg A]
  | more k hk hk1 =>
    have he : Polynomial.aeval A (Polynomial.Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)) =
        (2 : ℝ) • (A * Polynomial.aeval A (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ))) -
          Polynomial.aeval A (Polynomial.Chebyshev.T ℝ (k : ℤ)) := by
      rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by omega, Polynomial.Chebyshev.T_add_two]
      simp only [map_sub, map_mul, map_ofNat, Polynomial.aeval_X,
        Algebra.smul_def, map_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc]
    rw [he]
    have hbase : 2 * ‖A‖ * (2 * ‖A‖ + 1) + 1 ≤ (2 * ‖A‖ + 1) ^ 2 := by
      nlinarith [norm_nonneg A]
    calc
      _ ≤ 2 * (‖A‖ * ‖Polynomial.aeval A (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ))‖) +
          ‖Polynomial.aeval A (Polynomial.Chebyshev.T ℝ (k : ℤ))‖ := by
        apply (norm_sub_le _ _).trans
        rw [norm_smul]
        norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le A _)
          (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ ≤ 2 * (‖A‖ * (2 * ‖A‖ + 1) ^ (k + 1)) + (2 * ‖A‖ + 1) ^ k := by gcongr
      _ = (2 * ‖A‖ * (2 * ‖A‖ + 1) + 1) * (2 * ‖A‖ + 1) ^ k := by rw [pow_succ]; ring
      _ ≤ (2 * ‖A‖ + 1) ^ 2 * (2 * ‖A‖ + 1) ^ k :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = (2 * ‖A‖ + 1) ^ (k + 2) := by rw [← pow_add]; congr 1; omega

/-- A coarse bound for the actual complex matrix kernel coefficients. -/
theorem kernelCoefficient_norm_le {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (k : ℕ) :
    ‖kernelCoefficient lo hi M k‖ ≤
      2 * (|intervalRho lo hi| * (2 * ‖normalizedArgument lo hi M‖ + 1)) ^ k := by
  have he : kernelCoefficient lo hi M k =
      (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) •
        Polynomial.aeval (normalizedArgument lo hi M) (Polynomial.Chebyshev.T ℝ (k : ℤ)) := by
    unfold kernelCoefficient kernelCoefficientPolynomial normalizedChebyshev
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_comp]
    rw [← Algebra.smul_def]
    rfl
  rw [he, norm_smul]
  by_cases hk : k = 0
  · subst k
    simp
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, abs_neg, mul_pow]
    exact (mul_le_mul_of_nonneg_left (chebyshev_aeval_norm_le _ k) (by positivity)).trans_eq
      (by ring)

/-- Every actual complex matrix kernel has a positive analytic radius at zero. -/
theorem kernelPowerSeries_radius_pos {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (lo hi : ℝ) (M : Matrix n n ℂ) :
    0 < (RoughRegime.AnalyticCoefficients.coefficientSeries
      (fun k => PowerSeries.coeff k (kernelPowerSeries lo hi M))).radius := by
  apply RoughRegime.AnalyticCoefficients.coefficientSeries_radius_pos _ 2
    (|intervalRho lo hi| * (2 * ‖normalizedArgument lo hi M‖ + 1))
    (by norm_num) (by positivity)
  intro k
  simpa only [kernelPowerSeries, PowerSeries.coeff_mk] using kernelCoefficient_norm_le lo hi M k

/-- The formal coefficients are the genuine analytic coefficients of the rational kernel. -/
theorem kernelPowerSeries_hasFPowerSeriesAt {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (lo hi : ℝ) (M : Matrix n n ℂ) :
    HasFPowerSeriesAt
      (fun z : ℂ => Ring.inverse (RoughRegime.PowerSeriesAnalytic.quadraticDenominator
        (2 * intervalRho lo hi • normalizedArgument lo hi M)
        (intervalRho lo hi ^ 2 • (1 : Matrix n n ℂ)) z) *
          (1 - z ^ 2 • (intervalRho lo hi ^ 2 • (1 : Matrix n n ℂ))))
      (RoughRegime.AnalyticCoefficients.coefficientSeries
        (fun k => PowerSeries.coeff k (kernelPowerSeries lo hi M))) 0 := by
  apply RoughRegime.PowerSeriesAnalytic.hasFPowerSeriesAt_of_quadratic_generating_identity
  · exact kernelPowerSeries_radius_pos lo hi M
  · exact kernelPowerSeries_generating_identity lo hi M

end RoughRegime.ComplexKernel
