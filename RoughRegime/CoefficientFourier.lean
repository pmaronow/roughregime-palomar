module

public import RoughRegime.GateExpectation
public import RoughRegime.LatticeFourier


@[expose] public section
/-! Exact Fourier averaging under the actual uniform angle and independent
sampled lattice laws used in the prior. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Set MeasureTheory
open RoughRegime.Lattice RoughRegime.LatticeFourier
open scoped BigOperators ENNReal

 def angleUniform : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ • volume.restrict (Icc (0 : ℝ) (2 * Real.pi))

 instance angleUniform_probability : IsProbabilityMeasure angleUniform where
  measure_univ := by
    simp only [angleUniform, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      Real.volume_Icc, sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0)]
    exact ENNReal.ofReal_one

 theorem angleUniform_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) : (∫ θ, f θ ∂angleUniform) =
      ((2 * Real.pi)⁻¹ : ℝ) • (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) := by
  unfold angleUniform
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← integral_Icc_eq_integral_Ioc]

 theorem integral_exp_integer_frequency (n : ℤ) :
    (∫ θ, Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) ∂angleUniform) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right hn, angleUniform_integral]
    have heq : (fun θ : ℝ => Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)) =
        fun θ : ℝ => Complex.exp (((n : ℂ) * Complex.I) * θ) := by
      ext θ
      push_cast
      congr 1
      ring
    rw [heq, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero)]
    have he : ((n : ℂ) * Complex.I) * (2 * Real.pi : ℝ) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I]
    simp

 theorem latticeLaw_characteristic_expectation (Q M : ℕ) (η lam w : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    (∫ z, ((gate Q (lam * η) (latticeStep M * z) ^ 2 : ℝ) : ℂ) *
      Complex.exp (((w * latticeStep M * z : ℝ) : ℂ) * Complex.I)
      ∂(latticeLaw Q M η hQ hM hη hband).toMeasure) = latticeCharacteristic Q M η lam w := by
  let f : ℤ → ℂ := fun z => ((gate Q (lam * η) (latticeStep M * z) ^ 2 : ℝ) : ℂ) *
    Complex.exp (((w * latticeStep M * z : ℝ) : ℂ) * Complex.I)
  have hf : Integrable f (latticeLaw Q M η hQ hM hη hband).toMeasure := by
    apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
      abs_of_nonneg (sq_nonneg _), mul_one]
    exact pow_le_one₀ (gate_nonneg _ _ _) (gate_le_one _ _ _)
  rw [PMF.integral_eq_tsum _ _ hf]
  unfold latticeCharacteristic
  apply tsum_congr
  intro z
  rw [latticeLaw_apply, ENNReal.toReal_ofReal (latticeWeight_nonneg Q M η hQ hM hη z)]
  simp only [f, Complex.real_smul]
  push_cast
  ring

variable {ι : Type*} [Fintype ι]

/-- Exact characteristic factorization of the random gate and random phase,
with the gate and phase allowed to share all coefficient randomness. -/
 theorem jointGate_phase_expectation (Q M : ℕ) (η lam w : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) :
    (∫ z, ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      Complex.exp (((∑ i, latticeStep M * z i * w i : ℝ) : ℂ) * Complex.I)
      ∂gatePrior Q M η hQ hM hη hband) =
      ∏ i, latticeCharacteristic Q M (η i) (lam i) (w i) := by
  have heq (z : ι → ℤ) : ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      Complex.exp (((∑ i, latticeStep M * z i * w i : ℝ) : ℂ) * Complex.I) =
      ∏ i, ((gate Q (lam i * η i) (latticeStep M * z i) ^ 2 : ℝ) : ℂ) *
        Complex.exp (((w i * latticeStep M * z i : ℝ) : ℂ) * Complex.I) := by
    unfold jointGate
    rw [← Finset.prod_pow, Complex.ofReal_prod, Complex.ofReal_sum, Finset.sum_mul,
      Complex.exp_sum, Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    push_cast
    ring
  simp_rw [heq]
  unfold gatePrior
  rw [integral_fintype_prod_eq_prod (fun i (z : ℤ) =>
    ((gate Q (lam i * η i) (latticeStep M * z) ^ 2 : ℝ) : ℂ) *
      Complex.exp (((w i * latticeStep M * z : ℝ) : ℂ) * Complex.I))]
  simp_rw [latticeLaw_characteristic_expectation]

/-- Full exact averaging of one Fourier pattern over angle and coefficients:
 the angle enforces zero total integer frequency, and every coefficient yields
 its concrete sampled gated characteristic function. -/
 theorem angle_gate_phase_expectation (Q M : ℕ) (η lam w : ι → ℝ) (n : ℤ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) :
    (∫ z, (∫ θ, ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      Complex.exp ((((n : ℝ) * θ + ∑ i, latticeStep M * z i * w i : ℝ) : ℂ) * Complex.I)
      ∂angleUniform) ∂gatePrior Q M η hQ hM hη hband) =
      if n = 0 then ∏ i, latticeCharacteristic Q M (η i) (lam i) (w i) else 0 := by
  have heq (z : ι → ℤ) : (∫ θ, ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      Complex.exp ((((n : ℝ) * θ + ∑ i, latticeStep M * z i * w i : ℝ) : ℂ) * Complex.I) ∂angleUniform) =
      ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
        Complex.exp (((∑ i, latticeStep M * z i * w i : ℝ) : ℂ) * Complex.I) *
        (if n = 0 then 1 else 0) := by
    simp_rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have hf (θ : ℝ) : ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
        (Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
          Complex.exp (((∑ i, latticeStep M * z i * w i : ℝ) : ℂ) * Complex.I)) =
        (((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
          Complex.exp (((∑ i, latticeStep M * z i * w i : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) := by ring
    simp_rw [hf]
    rw [integral_const_mul, integral_exp_integer_frequency]
  simp_rw [heq]
  by_cases hn : n = 0
  · simp only [hn, ite_true, mul_one]
    exact jointGate_phase_expectation Q M η lam w hQ hM hη hband
  · simp [hn]

end RoughRegime.LatticePriors
