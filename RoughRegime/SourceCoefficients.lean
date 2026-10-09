module

public import RoughRegime.SourceGamma
public import RoughRegime.Lower


@[expose] public section
/-! Literal centered density Fourier coefficients and their uniform bounds. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.DyadicDigits

 variable {d : ℕ}

 def outerMean (outer : (Fin d → ℝ) → ℝ) : ℝ := ∫ x, outer x ∂cubeUniform d
 def blockMean (p0 r0 : ℝ) (outer : (Fin d → ℝ) → ℝ) : ℝ := p0 + outerMean outer * (r0 - p0)
 def centeredZero (p0 r0 : ℝ) (outer : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (outer x - outerMean outer) * (r0 - p0)
 def centeredWave (h : ℝ) (outer : (Fin d → ℝ) → ℝ) (label : Bool) (x : Fin d → ℝ) : ℝ :=
  RoughRegime.Lower.sign label * outer x * h / 2
 def cubeBlockDensity (p0 r0 h : ℝ) (outer : (Fin d → ℝ) → ℝ) (label : Bool)
    (x : Fin d → ℝ) (φ θ : ℝ) : ℝ :=
  p0 + outer x * (r0 + RoughRegime.Lower.sign label * h * Real.cos (θ + φ) - p0)

 theorem outerMean_bounds (outer : (Fin d → ℝ) → ℝ) (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1) :
    0 ≤ outerMean outer ∧ outerMean outer ≤ 1 := by
  constructor
  · exact integral_nonneg ho0
  · have hn : ‖outerMean outer‖ ≤ 1 := by
      simpa [outerMean] using norm_integral_le_of_norm_le_const (μ := cubeUniform d)
        (f := outer) (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (ho0 x)]
          exact ho1 x))
    rw [Real.norm_eq_abs] at hn
    exact (le_abs_self _).trans hn

 theorem convex_combination_range (p r lo hi t : ℝ) (hp : lo ≤ p ∧ p ≤ hi)
    (hr : lo ≤ r ∧ r ≤ hi) (ht : 0 ≤ t ∧ t ≤ 1) :
    lo ≤ p + t * (r - p) ∧ p + t * (r - p) ≤ hi := by
  have hl := add_le_add (mul_le_mul_of_nonneg_left hp.1 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hr.1 ht.1)
  have hh := add_le_add (mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hr.2 ht.1)
  constructor <;> nlinarith

 theorem cubeBlockDensity_bounds (p0 r0 h lo hi : ℝ) (outer : (Fin d → ℝ) → ℝ)
    (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : lo ≤ p0 ∧ p0 ≤ hi) (hh : 0 ≤ h) (hrlo : lo ≤ r0 - h) (hrhi : r0 + h ≤ hi)
    (label : Bool) (x : Fin d → ℝ) (φ θ : ℝ) :
    lo ≤ cubeBlockDensity p0 r0 h outer label x φ θ ∧ cubeBlockDensity p0 r0 h outer label x φ θ ≤ hi := by
  have hs : |RoughRegime.Lower.sign label| = 1 := by cases label <;> norm_num [RoughRegime.Lower.sign]
  have hcos : |RoughRegime.Lower.sign label * h * Real.cos (θ + φ)| ≤ h := by
    rw [abs_mul, abs_mul, hs, abs_of_nonneg hh, one_mul]
    exact mul_le_of_le_one_right hh (Real.abs_cos_le_one _)
  have hosc := abs_le.mp hcos
  apply convex_combination_range p0 _ lo hi _ hp (by constructor <;> linarith) ⟨ho0 x, ho1 x⟩

 theorem blockMean_bounds (p0 r0 lo hi : ℝ) (outer : (Fin d → ℝ) → ℝ)
    (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : lo ≤ p0 ∧ p0 ≤ hi) (hr : lo ≤ r0 ∧ r0 ≤ hi) :
    lo ≤ blockMean p0 r0 outer ∧ blockMean p0 r0 outer ≤ hi :=
  convex_combination_range p0 r0 lo hi _ hp hr (outerMean_bounds outer ho0 ho1)

 theorem centered_density_fourier (p0 r0 h : ℝ) (outer : (Fin d → ℝ) → ℝ)
    (label : Bool) (x : Fin d → ℝ) (φ θ : ℝ) :
    cubeBlockDensity p0 r0 h outer label x φ θ - blockMean p0 r0 outer =
      phasedAngular (centeredZero p0 r0 outer x) (centeredWave h outer label x) φ θ := by
  unfold cubeBlockDensity blockMean phasedAngular centeredZero centeredWave
  ring

 theorem centered_coefficients_bounds (p0 r0 h L : ℝ) (outer : (Fin d → ℝ) → ℝ)
    (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : 0 ≤ p0 ∧ p0 ≤ L) (hh : 0 ≤ h) (hrlo : 0 ≤ r0 - h) (hrhi : r0 + h ≤ L)
    (label : Bool) (x : Fin d → ℝ) :
    |centeredZero p0 r0 outer x| ≤ L ∧ |centeredWave h outer label x| ≤ L := by
  have hm := outerMean_bounds outer ho0 ho1
  have ho : |outer x - outerMean outer| ≤ 1 := abs_le.mpr ⟨by linarith [ho0 x, ho1 x], by linarith [ho0 x, ho1 x]⟩
  have hr : |r0 - p0| ≤ L := abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · unfold centeredZero
    rw [abs_mul]
    simpa using mul_le_mul ho hr (abs_nonneg _) zero_le_one
  · have hs : |RoughRegime.Lower.sign label| = 1 := by cases label <;> norm_num [RoughRegime.Lower.sign]
    unfold centeredWave
    rw [abs_div, abs_mul, abs_mul, hs, abs_of_nonneg (ho0 x), abs_of_nonneg hh]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmul := mul_le_of_le_one_left hh (ho1 x)
    linarith

 theorem centered_phasedAngular_bound (p0 r0 h L : ℝ) (outer : (Fin d → ℝ) → ℝ)
    (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : 0 ≤ p0 ∧ p0 ≤ L) (hh : 0 ≤ h) (hrlo : 0 ≤ r0 - h) (hrhi : r0 + h ≤ L)
    (label : Bool) (x : Fin d → ℝ) (φ θ : ℝ) :
    |phasedAngular (centeredZero p0 r0 outer x) (centeredWave h outer label x) φ θ| ≤ L := by
  rw [← centered_density_fourier]
  have hd := cubeBlockDensity_bounds p0 r0 h 0 L outer ho0 ho1 hp hh hrlo hrhi label x φ θ
  have hm := blockMean_bounds p0 r0 0 L outer ho0 ho1 hp (by constructor <;> linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

 theorem centeredZero_continuous (p0 r0 : ℝ) (outer : (Fin d → ℝ) → ℝ) (ho : Continuous outer) :
    Continuous (centeredZero p0 r0 outer) := (ho.sub continuous_const).mul continuous_const
 theorem centeredWave_continuous (h : ℝ) (outer : (Fin d → ℝ) → ℝ) (ho : Continuous outer) (label : Bool) :
    Continuous (centeredWave h outer label) := ((continuous_const.mul ho).mul continuous_const).div_const _

/-- Lemma14(c) for the construction's literal centered density coefficients.
The uniform constant depends only on fixed parameters; all angular coefficient
bounds are derived from the actual density range. -/
 theorem source_centered_density_coefficient_bound (U : SmoothStep) (d Q : ℕ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (gammaStar lambdaStar alpha0 s0 L p0 r0 h : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1 / 4)
    (hlam : 1 ≤ lambdaStar) (ha : 0 < alpha0) (hs0 : 0 < s0) (hL : 0 ≤ L)
    (outer : (Fin d → ℝ) → ℝ) (ho : Continuous outer)
    (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : 0 ≤ p0 ∧ p0 ≤ L) (hh : 0 ≤ h) (hrlo : 0 ≤ r0 - h) (hrhi : r0 + h ≤ L) :
    ∃ CE : ℝ, 0 ≤ CE ∧ 1 ≤ gammaConstant L ∧
      ∀ (J M j : ℕ) (hM : 0 < M)
      (hmM : sourceFineScale J s0 ≤ sourceCStar Q gammaStar lambdaStar alpha0 * M)
      (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbump : ∀ x, |bump x| ≤ 1),
      labeledGammaL2Squared (j := j) U Q M (sourceGammas J d gammaStar)
        (sourceEtas J d gammaStar lambdaStar alpha0 s0) (sourceLambdas J d lambdaStar)
        hQ hM (sourceEtas_pos J d gammaStar lambdaStar alpha0 s0 hγ hlam)
        (sourceEtas_band J d Q M gammaStar lambdaStar alpha0 s0 hQ hγ hγ1 hlam ha hmM)
        Au Av bump (fun (_ : Fin (j + 2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer)
        (fun (labels : Fin (j + 2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ)) ≤
        if M ≤ j then gammaConstant L ^ (j + 1) * Au ^ 2 * Av ^ 2 * Real.exp (CE * M) *
          gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j else 0 := by
  obtain ⟨CE, hCE, hC, hbound⟩ := source_lattice_coefficient_bound U d Q hd hQ
    gammaStar lambdaStar alpha0 s0 L hγ hγ1 hlam ha hs0 hL
  refine ⟨CE, hCE, hC, ?_⟩
  intro J M j hM hmM Au Av bump hbump
  exact hbound J M j hM hmM Au Av bump hbump
    (fun (_ : Fin (j + 2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer)
    (fun (labels : Fin (j + 2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ))
    (fun _ _ => centeredZero_continuous p0 r0 outer ho)
    (fun labels k => centeredWave_continuous h outer ho _)
    (fun labels k x => (centered_coefficients_bounds p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi false x).1)
    (fun labels k x => (centered_coefficients_bounds p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi (labels k.succ.succ) x).2)
    (fun labels k x φ θ => centered_phasedAngular_bound p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi (labels k.succ.succ) x φ θ)

end RoughRegime.LatticePriors
