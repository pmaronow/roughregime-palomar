module

public import RoughRegime.HermitianDenominator
public import RoughRegime.KernelNeighborhood


@[expose] public section
/-! Genuine uniform complex coefficient bounds for the reciprocal matrix kernels. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Set Metric Polynomial
namespace RoughRegime.ComplexKernel
open RoughRegime.Upper RoughRegime.AnalyticCoefficients

lemma quadraticDenominator_eq_denominator {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (z : ℂ) :
    RoughRegime.PowerSeriesAnalytic.quadraticDenominator
      (2 * intervalRho lo hi • normalizedArgument lo hi M)
      (intervalRho lo hi ^ 2 • (1 : Matrix n n ℂ)) z = denominator lo hi M z := by
  have ha : (2 : Matrix n n ℂ) * (intervalRho lo hi • normalizedArgument lo hi M) =
      (2 * intervalRho lo hi : ℝ) • normalizedArgument lo hi M := by
    rw [two_mul, ← add_smul]
    congr 1
    ring
  unfold RoughRegime.PowerSeriesAnalytic.quadraticDenominator denominator
  rw [ha, ← Complex.coe_smul (2 * intervalRho lo hi),
    ← Complex.coe_smul (intervalRho lo hi ^ 2)]
  simp only [smul_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
  module

/-- The formal Chebyshev coefficients are the coefficients of the actual closed rational kernel. -/
theorem rationalKernel_hasFPowerSeriesAt {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (lo hi : ℝ) (M : Matrix n n ℂ) :
    HasFPowerSeriesAt (rationalKernel lo hi M)
      (coefficientSeries (kernelCoefficient lo hi M)) 0 := by
  have h := kernelPowerSeries_hasFPowerSeriesAt lo hi M
  simp only [kernelPowerSeries, PowerSeries.coeff_mk] at h
  convert h using 1
  funext z
  rw [quadraticDenominator_eq_denominator]
  have hN : (1 : Matrix n n ℂ) - z ^ 2 • (intervalRho lo hi ^ 2 • (1 : Matrix n n ℂ)) =
      (1 - (intervalRho lo hi : ℂ) ^ 2 * z ^ 2) • (1 : Matrix n n ℂ) := by
    rw [← Complex.coe_smul (intervalRho lo hi ^ 2), smul_smul, Complex.ofReal_pow]
    module
  rw [hN, mul_smul_comm, mul_one]
  rfl

lemma normalizedArgument_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    (normalizedArgument lo hi M).IsHermitian := by
  have he : normalizedArgument lo hi M = (intervalHalfWidth lo hi)⁻¹ •
      (M - intervalCenter lo hi • (1 : Matrix n n ℂ)) := by
    simp [normalizedArgument, argumentPolynomial, Algebra.smul_def]
  rw [he]
  exact (hM.sub (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr rfl))).smul
    (isSelfAdjoint_iff.mpr rfl)

lemma normalizedArgument_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (hSpec : spectrum ℝ M ⊆ Icc lo hi) :
    ‖normalizedArgument lo hi M‖ ≤ 1 := by
  unfold normalizedArgument
  rw [← cfc_polynomial _ M (Matrix.isHermitian_iff_isSelfAdjoint.mp hM)]
  apply norm_cfc_le (by norm_num)
  intro x hx
  have ht := interval_argument_mem lo hi x hlo hlt (hSpec hx)
  have he : (argumentPolynomial lo hi).eval x = (x - intervalCenter lo hi) / intervalHalfWidth lo hi := by
    simp [argumentPolynomial, div_eq_mul_inv, mul_comm]
  rw [he, Real.norm_eq_abs]
  exact abs_le.mpr ht

lemma rationalKernel_differentiableOn {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (r : ℝ)
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r, IsUnit (denominator lo hi M z)) :
    DifferentiableOn ℂ (rationalKernel lo hi M) (closedBall 0 r) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold rationalKernel
  have hn : DifferentiableAt ℂ (fun z : ℂ => 1 - (intervalRho lo hi : ℂ) ^ 2 * z ^ 2) z := by fun_prop
  have hQ : DifferentiableAt ℂ (denominator lo hi M) z := by
    unfold denominator
    exact ((differentiableAt_const _).add
      ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 2 * (intervalRho lo hi : ℂ) * w) z).smul
        (differentiableAt_const _))).add
      ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (intervalRho lo hi : ℂ) ^ 2 * w ^ 2) z).smul
        (differentiableAt_const _))
  exact hn.smul ((differentiableAt_inverse (hunit z hz)).comp z hQ)

lemma rationalKernel_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (r B : ℝ) (_hr : 0 ≤ r) (_hB : 0 ≤ B)
    (z : ℂ) (hz : z ∈ closedBall 0 r) (hb : ‖Ring.inverse (denominator lo hi M z)‖ ≤ B) :
    ‖rationalKernel lo hi M z‖ ≤ (1 + intervalRho lo hi ^ 2 * r ^ 2) * B := by
  have hzn : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  rw [rationalKernel, norm_smul]
  have hscalar : ‖(1 : ℂ) - (intervalRho lo hi : ℂ) ^ 2 * z ^ 2‖ ≤
      1 + intervalRho lo hi ^ 2 * r ^ 2 := by
    apply (norm_sub_le _ _).trans
    simp only [norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [sq_abs]
    gcongr
  exact mul_le_mul hscalar hb (norm_nonneg _) (by positivity)

/-- One genuine parameter neighborhood controls all actual matrix coefficients geometrically. -/
theorem uniform_kernel_coefficients_of_normalized {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)] (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (S : Set E) (hS : IsCompact S) (M : E → Matrix (Fin n) (Fin n) ℂ) (hM : Continuous M)
    (hHerm : ∀ t ∈ S, (normalizedArgument lo hi (M t)).IsHermitian)
    (hNorm : ∀ t ∈ S, ‖normalizedArgument lo hi (M t)‖ ≤ 1) :
    ∃ ε B q : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ t, (∃ t0 ∈ S, ‖t - t0‖ < ε) →
        ∀ k, ‖kernelCoefficient lo hi (M t) k‖ ≤ B * q ^ k := by
  let ρ := intervalRho lo hi
  have hρ : 0 < ρ := intervalRho_pos lo hi hlo hlt
  have hρ1 : ρ < 1 := intervalRho_lt_one lo hi hlo hlt
  let r : ℝ := (1 + ρ⁻¹) / 2
  have hr1 : 1 < r := by
    have : 1 < ρ⁻¹ := (one_lt_inv₀ hρ).mpr hρ1
    dsimp [r]; linarith
  have hr : 0 < r := zero_lt_one.trans hr1
  have hρr : ρ * r < 1 := by
    dsimp [r]
    have hc := mul_inv_cancel₀ hρ.ne'
    nlinarith
  have hQ : Continuous (fun p : ℂ × E => denominator lo hi (M p.2) p.1) := by
    have hA : Continuous (fun t => normalizedArgument lo hi (M t)) :=
      (argumentPolynomial lo hi).continuous_aeval.comp hM
    unfold denominator
    exact (continuous_const.add
      ((continuous_const.mul continuous_fst).smul (hA.comp continuous_snd))).add
      ((continuous_const.mul (continuous_fst.pow 2)).smul continuous_const)
  obtain ⟨ε, B0, hε, hε1, hB0, hbound⟩ :=
    RoughRegime.KernelNeighborhood.uniform_inverse_tube S hS r
      (fun p => denominator lo hi (M p.2) p.1) hQ (by
        intro z hz t ht
        change IsUnit (normalizedDenominator ρ (normalizedArgument lo hi (M t)) z)
        apply normalizedDenominator_isUnit ρ hρ _ (hHerm t ht) (hNorm t ht)
        have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
        exact (mul_le_mul_of_nonneg_left hz' hρ.le).trans_lt hρr)
  let B := (1 + ρ ^ 2 * r ^ 2) * B0
  refine ⟨ε, B, r⁻¹, hε, hε1, by positivity, inv_nonneg.mpr hr.le,
    (inv_lt_one₀ hr).mpr hr1, ?_⟩
  intro t ht k
  apply coefficient_norm_le (rationalKernel lo hi (M t)) (kernelCoefficient lo hi (M t))
    (rationalKernel_hasFPowerSeriesAt lo hi (M t)) r B hr
    (rationalKernel_differentiableOn lo hi (M t) r (fun z hz => (hbound t ht z hz).1))
    (fun z hz => rationalKernel_norm_le lo hi (M t) r B0 hr.le hB0 z
      (sphere_subset_closedBall hz) (hbound t ht z (sphere_subset_closedBall hz)).2) k

/-- The source spectral assumptions supply the compact-center hypotheses. -/
theorem uniform_kernel_coefficients {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)] (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (S : Set E) (hS : IsCompact S) (M : E → Matrix (Fin n) (Fin n) ℂ) (hM : Continuous M)
    (hHerm : ∀ t ∈ S, (M t).IsHermitian)
    (hSpec : ∀ t ∈ S, spectrum ℝ (M t) ⊆ Icc lo hi) :
    ∃ ε B q : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ t, (∃ t0 ∈ S, ‖t - t0‖ < ε) →
        ∀ k, ‖kernelCoefficient lo hi (M t) k‖ ≤ B * q ^ k := by
  exact uniform_kernel_coefficients_of_normalized lo hi hlo hlt S hS M hM
    (fun t ht => normalizedArgument_hermitian lo hi (M t) (hHerm t ht))
    (fun t ht => normalizedArgument_norm_le_one lo hi hlo hlt (M t) (hHerm t ht) (hSpec t ht))

/-- Bounded center sets need not be closed: the normalized Hermitian unit-ball
conditions extend to their closure by continuity. -/
theorem bounded_uniform_kernel_coefficients {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)] (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set E) (hV : Bornology.IsBounded V)
    (M : E → Matrix (Fin n) (Fin n) ℂ) (hM : Continuous M)
    (hHerm : ∀ t ∈ V, (M t).IsHermitian)
    (hSpec : ∀ t ∈ V, spectrum ℝ (M t) ⊆ Icc lo hi) :
    ∃ ε B q : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) →
        ∀ k, ‖kernelCoefficient lo hi (M t) k‖ ≤ B * q ^ k := by
  let A := fun t => normalizedArgument lo hi (M t)
  have hA : Continuous A := (argumentPolynomial lo hi).continuous_aeval.comp hM
  let T := {t | star (A t) = A t} ∩ {t | ‖A t‖ ≤ 1}
  have hT : IsClosed T := (isClosed_eq (continuous_star.comp hA) hA).inter
    (isClosed_le hA.norm continuous_const)
  have hVT : V ⊆ T := by
    intro t ht
    exact ⟨isSelfAdjoint_iff.mp (Matrix.isHermitian_iff_isSelfAdjoint.mp
      (normalizedArgument_hermitian lo hi (M t) (hHerm t ht))),
      normalizedArgument_norm_le_one lo hi hlo hlt (M t) (hHerm t ht) (hSpec t ht)⟩
  have hclose := closure_minimal hVT hT
  obtain ⟨ε, B, q, hε, hε1, hB, hq, hq1, hb⟩ :=
    uniform_kernel_coefficients_of_normalized lo hi hlo hlt (closure V) hV.isCompact_closure M hM
      (fun t ht => Matrix.isHermitian_iff_isSelfAdjoint.mpr (isSelfAdjoint_iff.mpr (hclose ht).1))
      (fun t ht => (hclose ht).2)
  refine ⟨ε, B, q, hε, hε1, hB, hq, hq1, ?_⟩
  intro t ht
  apply hb t
  obtain ⟨t0, ht0, hnear⟩ := ht
  exact ⟨t0, subset_closure ht0, hnear⟩

end RoughRegime.ComplexKernel
