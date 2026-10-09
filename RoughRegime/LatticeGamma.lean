module

public import RoughRegime.ModeExpansion
public import RoughRegime.PatternIntegrals
public import RoughRegime.LatticeScales


@[expose] public section
/-! Actual gated likelihood coefficients and their exact finite Fourier
pattern expansion. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.Lattice RoughRegime.LatticeFourier
open scoped BigOperators

 def modeAmplitude (c w : ℝ) (o : Fin 3) : ℝ := if o = 1 then c else w

 def phasedAngular (c w φ θ : ℝ) : ℝ := c + 2 * w * Real.cos (θ + φ)

 theorem phasedAngular_eq_affineAngular (c w φ θ : ℝ) :
    phasedAngular c w φ θ = affineAngular c (2 * w * Real.cos φ) (-(2 * w * Real.sin φ)) θ := by
  unfold phasedAngular affineAngular
  rw [Real.cos_add]
  ring

 theorem phased_modeCoefficient (c w φ : ℝ) (o : Fin 3) :
    modeCoefficient c (2 * w * Real.cos φ) (-(2 * w * Real.sin φ)) o =
      (modeAmplitude c w o : ℂ) *
        Complex.exp ((((modeFrequency o : ℤ) : ℝ) * φ : ℝ) * Complex.I) := by
  fin_cases o
  · norm_num [modeCoefficient, modeAmplitude, modeFrequency]
    rw [show -((φ : ℂ) * Complex.I) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  · simp [modeCoefficient, modeAmplitude, modeFrequency]
  · norm_num [modeCoefficient, modeAmplitude, modeFrequency]
    rw [Complex.exp_ofReal_mul_I]
    push_cast
    ring

variable {ι : Type*} [Fintype ι]

 def observationPhase (M : ℕ) (s : Fin j → ι → ℝ) (z : ι → ℤ) (k : Fin j) : ℝ :=
  ∑ i, latticeStep M * z i * s k i

 def observationPatternFrequency (s : Fin j → ι → ℝ) (o : Fin j → Fin 3) (i : ι) : ℝ :=
  ∑ k, (modeFrequency (o k) : ℝ) * s k i

 def observationModeProduct (c w : Fin j → ℝ) (o : Fin j → Fin 3) : ℂ :=
  ∏ k, (modeAmplitude (c k) (w k) (o k) : ℂ)

 theorem phased_modeProduct (M : ℕ) (s : Fin j → ι → ℝ) (c w : Fin j → ℝ)
    (o : Fin j → Fin 3) (z : ι → ℤ) :
    (∏ k, modeCoefficient (c k) (2 * w k * Real.cos (observationPhase M s z k))
      (-(2 * w k * Real.sin (observationPhase M s z k))) (o k)) =
      observationModeProduct c w o *
        Complex.exp (((∑ i, latticeStep M * z i * observationPatternFrequency s o i : ℝ) : ℂ) * Complex.I) := by
  simp_rw [phased_modeCoefficient]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  have hs : (∑ k, (modeFrequency (o k) : ℝ) * observationPhase M s z k) =
      ∑ i, latticeStep M * z i * observationPatternFrequency s o i := by
    unfold observationPhase observationPatternFrequency
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [← hs]
  push_cast
  rw [Finset.sum_mul]

 theorem gated_modeProduct_integrable (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) (o : Fin j → Fin 3) :
    Integrable (fun z => ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      (∏ k, modeCoefficient (c k) (2 * w k * Real.cos (observationPhase M s z k))
        (-(2 * w k * Real.sin (observationPhase M s z k))) (o k)))
      (gatePrior Q M η hQ hM hη hband) := by
  simp_rw [phased_modeProduct]
  have hi : Integrable (fun z => ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      Complex.exp (((∑ i, latticeStep M * z i * observationPatternFrequency s o i : ℝ) : ℂ) * Complex.I))
      (gatePrior Q M η hQ hM hη hband) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact pow_le_one₀ (jointGate_bounds Q M η lam z).1 (jointGate_bounds Q M η lam z).2
  convert hi.const_mul (observationModeProduct c w o) using 1
  ext z
  ring

 theorem gated_modeProduct_expectation (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) (o : Fin j → Fin 3) :
    (∫ z, ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      (∏ k, modeCoefficient (c k) (2 * w k * Real.cos (observationPhase M s z k))
        (-(2 * w k * Real.sin (observationPhase M s z k))) (o k))
      ∂gatePrior Q M η hQ hM hη hband) =
      observationModeProduct c w o * ∏ i, latticeCharacteristic Q M (η i) (lam i) (observationPatternFrequency s o i) := by
  simp_rw [phased_modeProduct]
  have heq (z : ι → ℤ) : ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      (observationModeProduct c w o *
        Complex.exp (((∑ i, latticeStep M * z i * observationPatternFrequency s o i : ℝ) : ℂ) * Complex.I)) =
      observationModeProduct c w o * (((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
        Complex.exp (((∑ i, latticeStep M * z i * observationPatternFrequency s o i : ℝ) : ℂ) * Complex.I)) := by ring
  simp_rw [heq]
  rw [integral_const_mul, jointGate_phase_expectation]

/-- The literal real likelihood coefficient after removing deterministic
amplitudes and the two bump factors. -/
 def latticeGamma (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) : ℝ :=
  2 * ∫ z, jointGate Q M η lam z ^ 2 *
    (∫ θ, Real.cos ((M : ℝ) * θ) *
      ∏ k, phasedAngular (c k) (w k) (observationPhase M s z k) θ ∂angleUniform)
    ∂gatePrior Q M η hQ hM hη hband

 theorem latticeGamma_zero (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) (hj : j < M) :
    latticeGamma Q M η lam hQ hM hη hband s c w = 0 := by
  unfold latticeGamma
  simp_rw [phasedAngular_eq_affineAngular]
  have hz (z : ι → ℤ) : (∫ θ, Real.cos ((M : ℝ) * θ) *
      ∏ k, affineAngular (c k) (2 * w k * Real.cos (observationPhase M s z k))
        (-(2 * w k * Real.sin (observationPhase M s z k))) θ ∂angleUniform) = 0 :=
    integral_cos_affine_product_zero j M _ _ _ hj
  simp_rw [hz]
  simp

 def patternTotalFrequency (M : ℕ) (ε : Bool) (o : Fin j → Fin 3) : ℤ :=
  (if ε then (M : ℤ) else -(M : ℤ)) + ∑ k, modeFrequency (o k)

 def latticeGammaTerm (Q M : ℕ) (η lam : ι → ℝ) (s : Fin j → ι → ℝ)
    (c w : Fin j → ℝ) (ε : Bool) (o : Fin j → Fin 3) : ℂ :=
  observationModeProduct c w o *
    (if patternTotalFrequency M ε o = 0 then
      ∏ i, latticeCharacteristic Q M (η i) (lam i) (observationPatternFrequency s o i) else 0)

/-- Exact expansion of the literal real coefficient, obtained by averaging
actual angle and coefficient probability laws. -/
 theorem latticeGamma_expansion (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) :
    (latticeGamma Q M η lam hQ hM hη hband s c w : ℂ) =
      ∑ ε : Bool, ∑ o : Fin j → Fin 3, latticeGammaTerm Q M η lam s c w ε o := by
  let C (z : ι → ℤ) (o : Fin j → Fin 3) : ℂ :=
    ∏ k, modeCoefficient (c k) (2 * w k * Real.cos (observationPhase M s z k))
      (-(2 * w k * Real.sin (observationPhase M s z k))) (o k)
  let delta (ε : Bool) (o : Fin j → Fin 3) : ℂ := if patternTotalFrequency M ε o = 0 then 1 else 0
  have hinner (z : ι → ℤ) : ((∫ θ, Real.cos ((M : ℝ) * θ) *
      ∏ k, phasedAngular (c k) (w k) (observationPhase M s z k) θ ∂angleUniform : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ∑ ε : Bool, ∑ o : Fin j → Fin 3, C z o * delta ε o := by
    rw [← integral_complex_ofReal]
    simp_rw [Complex.ofReal_mul, Complex.ofReal_prod, phasedAngular_eq_affineAngular]
    rw [integral_cos_affine_product_coefficient]
    rw [Fintype.sum_bool]
    rfl
  unfold latticeGamma
  rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul]
  simp_rw [Complex.ofReal_mul, hinner]
  simp only [Complex.ofReal_ofNat]
  have heq (z : ι → ℤ) : (2 : ℂ) * (((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
      ((1 / 2 : ℂ) * ∑ ε : Bool, ∑ o : Fin j → Fin 3, C z o * delta ε o)) =
      ∑ ε : Bool, ∑ o : Fin j → Fin 3, ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) * C z o * delta ε o := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ε hε
    apply Finset.sum_congr rfl
    intro o ho
    ring
  simp_rw [heq]
  have hi (ε : Bool) (o : Fin j → Fin 3) : Integrable (fun z =>
      ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) * C z o * delta ε o)
      (gatePrior Q M η hQ hM hη hband) :=
    (gated_modeProduct_integrable Q M η lam hQ hM hη hband s c w o).mul_const _
  rw [integral_finsetSum Finset.univ (fun ε _ => integrable_finsetSum _ (fun o _ => hi ε o))]
  apply Finset.sum_congr rfl
  intro ε hε
  rw [integral_finsetSum Finset.univ (fun o _ => hi ε o)]
  apply Finset.sum_congr rfl
  intro o ho
  rw [integral_mul_const]
  change (∫ z, ((jointGate Q M η lam z ^ 2 : ℝ) : ℂ) *
    (∏ k, modeCoefficient (c k) (2 * w k * Real.cos (observationPhase M s z k))
      (-(2 * w k * Real.sin (observationPhase M s z k))) (o k))
    ∂gatePrior Q M η hQ hM hη hband) * delta ε o = _
  rw [gated_modeProduct_expectation]
  unfold latticeGammaTerm delta
  split_ifs <;> simp_all

 theorem observationModeProduct_norm_bound (c w : Fin j → ℝ) (L : ℝ) (_hL : 0 ≤ L)
    (hc : ∀ k, |c k| ≤ L) (hw : ∀ k, |w k| ≤ L) (o : Fin j → Fin 3) :
    ‖observationModeProduct c w o‖ ≤ L ^ j := by
  unfold observationModeProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ _k : Fin j, L := by
      apply Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)
      intro k hk
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold modeAmplitude
      split_ifs <;> first | exact hc k | exact hw k
    _ = L ^ j := by simp

 theorem latticeGamma_abs_bound (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) (L : ℝ) (_hL : 0 ≤ L)
    (hb : ∀ z θ k, |phasedAngular (c k) (w k) (observationPhase M s z k) θ| ≤ L) :
    |latticeGamma Q M η lam hQ hM hη hband s c w| ≤ 2 * L ^ j := by
  have hinner (z : ι → ℤ) : |∫ θ, Real.cos ((M : ℝ) * θ) *
      ∏ k, phasedAngular (c k) (w k) (observationPhase M s z k) θ ∂angleUniform| ≤ L ^ j := by
    have hpoint (θ : ℝ) : ‖Real.cos ((M : ℝ) * θ) *
        ∏ k, phasedAngular (c k) (w k) (observationPhase M s z k) θ‖ ≤ L ^ j := by
      rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod]
      have hp : (∏ k, |phasedAngular (c k) (w k) (observationPhase M s z k) θ|) ≤ L ^ j := by
        calc
          _ ≤ ∏ _k : Fin j, L := Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) (fun k _ => hb z θ k)
          _ = L ^ j := by simp
      have hh := mul_le_mul (Real.abs_cos_le_one ((M : ℝ) * θ)) hp
        (Finset.prod_nonneg (fun k _ => abs_nonneg _)) zero_le_one
      simpa using hh
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := angleUniform) (Filter.Eventually.of_forall hpoint)
  have houter : |∫ z, jointGate Q M η lam z ^ 2 *
      (∫ θ, Real.cos ((M : ℝ) * θ) *
        ∏ k, phasedAngular (c k) (w k) (observationPhase M s z k) θ ∂angleUniform)
      ∂gatePrior Q M η hQ hM hη hband| ≤ L ^ j := by
    have hpoint (z : ι → ℤ) : ‖jointGate Q M η lam z ^ 2 *
        (∫ θ, Real.cos ((M : ℝ) * θ) *
          ∏ k, phasedAngular (c k) (w k) (observationPhase M s z k) θ ∂angleUniform)‖ ≤ L ^ j := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hg := pow_le_one₀ (n := 2) (jointGate_bounds Q M η lam z).1 (jointGate_bounds Q M η lam z).2
      have hh := mul_le_mul hg (hinner z) (abs_nonneg _) zero_le_one
      simpa using hh
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := gatePrior Q M η hQ hM hη hband) (Filter.Eventually.of_forall hpoint)
  unfold latticeGamma
  rw [abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left houter (by norm_num)

end RoughRegime.LatticePriors
