module

public import RoughRegime.SincSupport
public import RoughRegime.PoissonSampling
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace


@[expose] public section
namespace RoughRegime.LatticeFourier

open MeasureTheory Set Real Complex Filter Asymptotics
open scoped FourierTransform

noncomputable def sincNormalizer (Q : ℕ) : ℝ := ∫ x : ℝ, Real.sinc x ^ (2 * Q)

noncomputable def latticeDensity (Q : ℕ) (η x : ℝ) : ℝ :=
  (η * sincNormalizer Q)⁻¹ * RoughRegime.Lattice.gate Q η x

noncomputable def gatedDensity (Q : ℕ) (η lam : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  ((latticeDensity Q η x * RoughRegime.Lattice.gate Q (lam * η) x ^ k : ℝ) : ℂ)

theorem sincNormalizer_pos (Q : ℕ) (hQ : 1 ≤ Q) : 0 < sincNormalizer Q :=
  integral_sinc_even_power_pos Q hQ

theorem latticeDensity_nonneg (Q : ℕ) (η x : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    0 ≤ latticeDensity Q η x :=
  mul_nonneg (inv_nonneg.mpr (mul_nonneg hη.le (sincNormalizer_pos Q hQ).le))
    (RoughRegime.Lattice.gate_nonneg Q η x)

theorem latticeDensity_integrable (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    Integrable (latticeDensity Q η) :=
  (scaledSincPower_real_integrable Q η hQ hη).const_mul _

theorem latticeDensity_integral (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    (∫ x : ℝ, latticeDensity Q η x) = 1 := by
  have hs : (∫ x : ℝ, RoughRegime.Lattice.gate Q η x) = η * sincNormalizer Q := by
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (fun x : ℝ => Real.sinc x ^ (2 * Q)) η⁻¹
    simp only [inv_inv, abs_of_pos hη, smul_eq_mul] at h
    convert h using 1
    · congr 1
      ext x
      unfold RoughRegime.Lattice.gate
      rw [div_eq_mul_inv, mul_comm x]
    · rfl
  unfold latticeDensity
  rw [integral_const_mul, hs]
  exact inv_mul_cancel₀ (mul_ne_zero hη.ne' (sincNormalizer_pos Q hQ).ne')

theorem gatedDensity_as_gatedSinc (Q : ℕ) (η lam : ℝ) (k : ℕ) :
    gatedDensity Q η lam k = fun x =>
      (((η * sincNormalizer Q)⁻¹ : ℝ) : ℂ) * gatedSinc Q η lam k x := by
  ext x
  unfold gatedDensity latticeDensity gatedSinc scaledSincPower RoughRegime.Lattice.gate
  push_cast
  ring

theorem fourier_const_mul (f : ℝ → ℂ) (c : ℂ) (w : ℝ) :
    𝓕 (fun x => c * f x) w = c * 𝓕 f w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

theorem gatedDensity_continuous (Q : ℕ) (η lam : ℝ) (k : ℕ) :
    Continuous (gatedDensity Q η lam k) := by
  rw [gatedDensity_as_gatedSinc]
  exact continuous_const.mul (gatedSinc_continuous Q η lam k)

theorem gatedDensity_integrable (Q : ℕ) (η lam : ℝ) (k : ℕ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    Integrable (gatedDensity Q η lam k) := by
  rw [gatedDensity_as_gatedSinc]
  exact (gatedSinc_integrable Q η lam k hQ hη).const_mul _

theorem gatedDensity_isBigO (Q : ℕ) (η lam : ℝ) (k : ℕ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    IsBigO (cocompact ℝ) (gatedDensity Q η lam k) (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  rw [gatedDensity_as_gatedSinc]
  exact (gatedSinc_isBigO Q η lam k hQ hη).const_mul_left _

theorem gatedDensity_fourier_eq_zero (Q : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2)
    (w : ℝ) (hw : 3 * Q / (Real.pi * η) < |w|) :
    𝓕 (gatedDensity Q η lam k) w = 0 := by
  rw [gatedDensity_as_gatedSinc, fourier_const_mul,
    gatedSinc_fourier_eq_zero Q η lam k hQ hη hlam hk w hw, mul_zero]

/-- The Fourier convention used in the source paper. -/
noncomputable def paperFourier (f : ℝ → ℂ) (w : ℝ) : ℂ := 𝓕 f (-w / (2 * Real.pi))

theorem paperFourier_eq_integral (f : ℝ → ℂ) (w : ℝ) :
    paperFourier f w = ∫ x : ℝ, f x * Complex.exp (((w * x : ℝ) : ℂ) * Complex.I) := by
  unfold paperFourier
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  refine ae_of_all _ (fun x => ?_)
  change Complex.exp ((-2 * Real.pi * x * (-w / (2 * Real.pi)) : ℝ) * Complex.I) • f x =
    f x * Complex.exp (((w * x : ℝ) : ℂ) * Complex.I)
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/-- Actual compact support for all three gated lattice density transforms. -/
theorem gatedDensity_paperFourier_eq_zero (Q : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2)
    (w : ℝ) (hw : 6 * Q / η < |w|) :
    paperFourier (gatedDensity Q η lam k) w = 0 := by
  unfold paperFourier
  apply gatedDensity_fourier_eq_zero Q η lam k hQ hη hlam hk
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
  convert hw using 1
  field_simp
  norm_num

/-- The continuous sinc density's second moment, denoted mu_2 in the paper. -/
noncomputable def sincSecondMoment (Q : ℕ) : ℝ :=
  (sincNormalizer Q)⁻¹ * ∫ x : ℝ, x ^ 2 * Real.sinc x ^ (2 * Q)

theorem sincSecondMoment_nonneg (Q : ℕ) (hQ : 1 ≤ Q) : 0 ≤ sincSecondMoment Q := by
  apply mul_nonneg (inv_nonneg.mpr (sincNormalizer_pos Q hQ).le)
  apply integral_nonneg
  intro x
  have hg0 : 0 ≤ Real.sinc x ^ (2 * Q) := by
    simpa [RoughRegime.Lattice.gate] using (RoughRegime.Lattice.gate_nonneg Q 1 x)
  exact mul_nonneg (sq_nonneg _) hg0

theorem latticeDensity_second_moment_integrable (Q : ℕ) (η : ℝ)
    (hQ : 2 ≤ Q) (hη : 0 < η) :
    Integrable (fun x : ℝ => x ^ 2 * latticeDensity Q η x) := by
  have h := (scaledSincPower_second_moment_integrable Q η hQ hη).const_mul
    ((η * sincNormalizer Q)⁻¹)
  convert h using 1
  ext x
  unfold latticeDensity RoughRegime.Lattice.gate
  ring

theorem latticeDensity_second_moment (Q : ℕ) (η : ℝ) (hη : 0 < η) :
    (∫ x : ℝ, x ^ 2 * latticeDensity Q η x) = η ^ 2 * sincSecondMoment Q := by
  have hs : (∫ x : ℝ, x ^ 2 * RoughRegime.Lattice.gate Q η x) =
      η ^ 3 * ∫ x : ℝ, x ^ 2 * Real.sinc x ^ (2 * Q) := by
    have heq : (fun x : ℝ => x ^ 2 * RoughRegime.Lattice.gate Q η x) =
        fun x => η ^ 2 * ((η⁻¹ * x) ^ 2 * Real.sinc (η⁻¹ * x) ^ (2 * Q)) := by
      ext x
      unfold RoughRegime.Lattice.gate
      simp only [div_eq_mul_inv]
      field_simp
    have hscale : (∫ x : ℝ, (η⁻¹ * x) ^ 2 * Real.sinc (η⁻¹ * x) ^ (2 * Q)) =
        η * ∫ x : ℝ, x ^ 2 * Real.sinc x ^ (2 * Q) := by
      simpa only [inv_inv, abs_of_pos hη, smul_eq_mul] using
        (MeasureTheory.Measure.integral_comp_mul_left
          (fun y : ℝ => y ^ 2 * Real.sinc y ^ (2 * Q)) η⁻¹)
    rw [heq, integral_const_mul, hscale]
    ring
  have heq : (fun x : ℝ => x ^ 2 * latticeDensity Q η x) =
      fun x => (η * sincNormalizer Q)⁻¹ * (x ^ 2 * RoughRegime.Lattice.gate Q η x) := by
    ext x
    unfold latticeDensity
    ring
  rw [heq, integral_const_mul, hs]
  unfold sincSecondMoment
  simp only [mul_inv_rev]
  field_simp

/-- The continuous integral bound transferred to the sampled gate expectation
by the sampling theorem. -/
theorem latticeDensity_gate_deficit (Q : ℕ) (η lam : ℝ)
    (hQ : 2 ≤ Q) (hη : 0 < η) (hlam : 1 ≤ lam) :
    1 - (∫ x : ℝ, RoughRegime.Lattice.gate Q (lam * η) x * latticeDensity Q η x) ≤
      (Q : ℝ) * sincSecondMoment Q / (3 * lam ^ 2) := by
  have hQ1 : 1 ≤ Q := by omega
  have hi := latticeDensity_integrable Q η hQ1 hη
  have hgm : AEStronglyMeasurable (fun x : ℝ => RoughRegime.Lattice.gate Q (lam * η) x) volume := by
    apply Continuous.aestronglyMeasurable
    unfold RoughRegime.Lattice.gate
    fun_prop
  have hg : Integrable (fun x : ℝ => RoughRegime.Lattice.gate Q (lam * η) x * latticeDensity Q η x) :=
    hi.bdd_mul hgm (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (RoughRegime.Lattice.gate_nonneg _ _ _)]
      exact RoughRegime.Lattice.gate_le_one _ _ _)
  have hm := latticeDensity_second_moment_integrable Q η hQ hη
  have hleft : Integrable (fun x : ℝ => latticeDensity Q η x -
      RoughRegime.Lattice.gate Q (lam * η) x * latticeDensity Q η x) := hi.sub hg
  have h := integral_mono hleft (hm.const_mul ((Q : ℝ) / (3 * (lam * η) ^ 2)))
    (fun x : ℝ => show latticeDensity Q η x -
      RoughRegime.Lattice.gate Q (lam * η) x * latticeDensity Q η x ≤
        (Q : ℝ) / (3 * (lam * η) ^ 2) * (x ^ 2 * latticeDensity Q η x) from by
      have hp := mul_le_mul_of_nonneg_right (RoughRegime.Lattice.gate_deficit Q (lam * η) x)
        (latticeDensity_nonneg Q η x hQ1 hη)
      convert hp using 1 <;> field_simp)
  change (∫ x : ℝ, latticeDensity Q η x -
    RoughRegime.Lattice.gate Q (lam * η) x * latticeDensity Q η x) ≤
    (∫ x : ℝ, (Q : ℝ) / (3 * (lam * η) ^ 2) * (x ^ 2 * latticeDensity Q η x)) at h
  rw [integral_sub hi hg, integral_const_mul, latticeDensity_integral Q η hQ1 hη,
    latticeDensity_second_moment Q η hη] at h
  convert h using 1
  field_simp

theorem gatedDensity_fourier_hasCompactSupport (Q : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2) :
    HasCompactSupport (𝓕 (gatedDensity Q η lam k)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-(3 * Q / (Real.pi * η))) (3 * Q / (Real.pi * η))) isCompact_Icc
  intro w hw
  apply abs_le.mp
  by_contra hn
  have hlarge : 3 * Q / (Real.pi * η) < |w| := lt_of_not_ge hn
  exact hw (gatedDensity_fourier_eq_zero Q η lam k hQ hη hlam hk w hlarge)

noncomputable def latticeStep (M : ℕ) : ℝ := 2 * Real.pi / M

theorem latticeStep_pos (M : ℕ) (hM : 0 < M) : 0 < latticeStep M := by
  unfold latticeStep
  positivity

/-- The complete sampling identity for the actual gated sinc densities. -/
theorem gatedDensity_sampling (Q M : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2) (w : ℝ) :
    ((latticeStep M : ℝ) : ℂ) *
      (∑' z : ℤ, gatedDensity Q η lam k (latticeStep M * z) *
        Complex.exp (((w * latticeStep M * z : ℝ) : ℂ) * Complex.I)) =
      ∑' l : ℤ, paperFourier (gatedDensity Q η lam k) (w - l * M) := by
  have h := poisson_sampling (gatedDensity Q η lam k) (latticeStep M) w
    (latticeStep_pos M hM) (gatedDensity_continuous Q η lam k)
    (gatedDensity_isBigO Q η lam k hQ hη)
    (gatedDensity_fourier_hasCompactSupport Q η lam k hQ hη hlam hk)
  rw [h]
  apply tsum_congr
  intro l
  unfold paperFourier latticeStep
  apply congrArg (𝓕 (gatedDensity Q η lam k))
  field_simp
  ring

theorem gatedDensity_sampling_summable (Q M : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2) (w : ℝ) :
    Summable (fun z : ℤ => gatedDensity Q η lam k (latticeStep M * z) *
      Complex.exp (((w * latticeStep M * z : ℝ) : ℂ) * Complex.I)) :=
  (poisson_sampling_summable (gatedDensity Q η lam k) (latticeStep M) w
    (latticeStep_pos M hM)
    (gatedDensity_isBigO Q η lam k hQ hη)
    (gatedDensity_fourier_hasCompactSupport Q η lam k hQ hη hlam hk)).1

theorem gated_lattice_integral_complex (Q M : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2)
    (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    ((latticeStep M : ℝ) : ℂ) * (∑' z : ℤ, gatedDensity Q η lam k (latticeStep M * z)) =
      ∫ x : ℝ, gatedDensity Q η lam k x := by
  have hs := gatedDensity_sampling Q M η lam k hQ hM hη hlam hk 0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hcut : 6 * Q / η < (M : ℝ) := by have := div_pos (by positivity : 0 < 6 * (Q : ℝ)) hη; linarith
  have hz : ∀ l : ℤ, l ≠ 0 → paperFourier (gatedDensity Q η lam k) (0 - l * M) = 0 := by
    intro l hl
    apply gatedDensity_paperFourier_eq_zero Q η lam k hQ hη hlam hk
    have hli : (1 : ℤ) ≤ |l| := by have := abs_pos.mpr hl; omega
    have hlr : (1 : ℝ) ≤ |(l : ℝ)| := by exact_mod_cast hli
    rw [zero_sub, abs_neg, abs_mul, abs_of_pos hMr]
    have hmul := mul_le_mul_of_nonneg_right hlr hMr.le
    simp only [one_mul] at hmul
    exact hcut.trans_le hmul
  rw [tsum_eq_single (0 : ℤ) hz] at hs
  rw [paperFourier_eq_integral] at hs
  simpa using hs

/-- The discrete lattice average equals its continuous integral for k=0,1,2. -/
theorem gated_lattice_integral (Q M : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2)
    (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    latticeStep M * (∑' z : ℤ, latticeDensity Q η (latticeStep M * z) *
      RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z) ^ k) =
      ∫ x : ℝ, latticeDensity Q η x * RoughRegime.Lattice.gate Q (lam * η) x ^ k := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_tsum,
    ← integral_complex_ofReal (f := fun x : ℝ => latticeDensity Q η x *
      RoughRegime.Lattice.gate Q (lam * η) x ^ k)]
  exact gated_lattice_integral_complex Q M η lam k hQ hM hη hlam hk hband

noncomputable def latticeWeight (Q M : ℕ) (η : ℝ) (z : ℤ) : ℝ :=
  latticeStep M * latticeDensity Q η (latticeStep M * z)

theorem latticeWeight_nonneg (Q M : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (z : ℤ) :
    0 ≤ latticeWeight Q M η z :=
  mul_nonneg (latticeStep_pos M hM).le (latticeDensity_nonneg Q η _ hQ hη)

/-- Exact normalization of the actual sampled law, without a normalization axiom. -/
theorem latticeWeight_sum_one (Q M : ℕ) (η : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    (∑' z : ℤ, latticeWeight Q M η z) = 1 := by
  have h := gated_lattice_integral Q M η 1 0 hQ hM hη (by norm_num) (by omega) hband
  simp only [pow_zero, mul_one, latticeDensity_integral Q η hQ hη] at h
  simpa only [latticeWeight, tsum_mul_left] using h

theorem latticeWeight_summable (Q M : ℕ) (η : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (_hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    Summable (latticeWeight Q M η) := by
  have h := gatedDensity_sampling_summable Q M η 1 0 hQ hM hη (by norm_num) (by omega) 0
  have hr := Complex.reCLM.summable h
  simp only [gatedDensity, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one,
    pow_zero, Complex.reCLM_apply, Complex.ofReal_re] at hr
  exact Summable.mul_left (latticeStep M) hr

theorem sampled_gate_deficit (Q M : ℕ) (η lam : ℝ)
    (hQ : 2 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hlam : 1 ≤ lam)
    (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    1 - (∑' z : ℤ, latticeWeight Q M η z *
      RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z)) ≤
      (Q : ℝ) * sincSecondMoment Q / (3 * lam ^ 2) := by
  have h := gated_lattice_integral Q M η lam 1 (by omega) hM hη hlam (by omega) hband
  simp only [pow_one] at h
  have heq : (∑' z : ℤ, latticeWeight Q M η z *
      RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z)) =
      latticeStep M * (∑' z : ℤ, latticeDensity Q η (latticeStep M * z) *
        RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z)) := by
    unfold latticeWeight
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
  rw [heq, h]
  simpa only [mul_comm] using latticeDensity_gate_deficit Q η lam hQ hη hlam

/-- The actual countable probability mass function on the lattice index. -/
noncomputable def latticeLaw (Q M : ℕ) (η : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) : PMF ℤ :=
  ⟨fun z => ENNReal.ofReal (latticeWeight Q M η z), ENNReal.summable.hasSum_iff.2 (by
    rw [← ENNReal.ofReal_tsum_of_nonneg (latticeWeight_nonneg Q M η hQ hM hη)
      (latticeWeight_summable Q M η hQ hM hη hband), latticeWeight_sum_one Q M η hQ hM hη hband]
    simp)⟩

@[simp] theorem latticeLaw_apply (Q M : ℕ) (η : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) (z : ℤ) :
    latticeLaw Q M η hQ hM hη hband z = ENNReal.ofReal (latticeWeight Q M η z) := rfl

/-- The gated characteristic function under the actual sampled law. -/
noncomputable def latticeCharacteristic (Q M : ℕ) (η lam w : ℝ) : ℂ :=
  ∑' z : ℤ, ((latticeWeight Q M η z *
    RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z) ^ 2 : ℝ) : ℂ) *
    Complex.exp (((w * latticeStep M * z : ℝ) : ℂ) * Complex.I)

theorem latticeCharacteristic_as_sampling (Q M : ℕ) (η lam w : ℝ) :
    latticeCharacteristic Q M η lam w = ((latticeStep M : ℝ) : ℂ) *
      (∑' z : ℤ, gatedDensity Q η lam 2 (latticeStep M * z) *
        Complex.exp (((w * latticeStep M * z : ℝ) : ℂ) * Complex.I)) := by
  rw [← tsum_mul_left]
  unfold latticeCharacteristic
  apply tsum_congr
  intro z
  unfold latticeWeight gatedDensity
  push_cast
  ring

/-- The exact alias-band vanishing statement in Lemma 13. -/
theorem latticeCharacteristic_eq_zero (Q M : ℕ) (η lam w : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hlam : 1 ≤ lam)
    (houtside : ¬ ∃ l : ℤ, |w - (l : ℝ) * M| ≤ 6 * Q / η) :
    latticeCharacteristic Q M η lam w = 0 := by
  rw [latticeCharacteristic_as_sampling,
    gatedDensity_sampling Q M η lam 2 hQ hM hη hlam (by omega)]
  have hz : ∀ l : ℤ, paperFourier (gatedDensity Q η lam 2) (w - (l : ℝ) * M) = 0 := by
    intro l
    apply gatedDensity_paperFourier_eq_zero Q η lam 2 hQ hη hlam (by omega)
    exact lt_of_not_ge (fun h => houtside ⟨l, h⟩)
  simp only [hz, tsum_zero]

/-- Characteristic functions remain norm-bounded by one despite the gate. -/
theorem latticeCharacteristic_norm_le_one (Q M : ℕ) (η lam w : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    ‖latticeCharacteristic Q M η lam w‖ ≤ 1 := by
  let f : ℤ → ℂ := fun z => ((latticeWeight Q M η z *
    RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z) ^ 2 : ℝ) : ℂ) *
    Complex.exp (((w * latticeStep M * z : ℝ) : ℂ) * Complex.I)
  have hw := latticeWeight_summable Q M η hQ hM hη hband
  have hb : ∀ z : ℤ, ‖f z‖ ≤ latticeWeight Q M η z := by
    intro z
    have hnonneg := latticeWeight_nonneg Q M η hQ hM hη z
    have hg0 := RoughRegime.Lattice.gate_nonneg Q (lam * η) (latticeStep M * z)
    have hg1 := RoughRegime.Lattice.gate_le_one Q (lam * η) (latticeStep M * z)
    unfold f
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
      abs_of_nonneg (mul_nonneg hnonneg (sq_nonneg _)), mul_one]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 2) hg0 hg1) hnonneg
  have hn : Summable (fun z => ‖f z‖) := Summable.of_nonneg_of_le (fun z => norm_nonneg _) hb hw
  calc
    ‖latticeCharacteristic Q M η lam w‖ ≤ ∑' z, ‖f z‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' z, latticeWeight Q M η z := hn.tsum_le_tsum hb hw
    _ = 1 := latticeWeight_sum_one Q M η hQ hM hη hband

/-- Lemma 13 of the paper, for the paper's actual sinc density and countable
lattice law. This includes arbitrary real coefficient powers. -/
theorem gated_lattice_laws (Q M : ℕ) (η lam : ℝ)
    (hQ : 2 ≤ Q) (hM : 2 ≤ M) (hη : 0 < η) (hlam : 1 ≤ lam)
    (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    (∑' z : ℤ, latticeWeight Q M η z) = 1 ∧
    (∀ x : ℝ, 0 ≤ RoughRegime.Lattice.gate Q (lam * η) x ∧
      RoughRegime.Lattice.gate Q (lam * η) x ≤ 1) ∧
    (1 - (∑' z : ℤ, latticeWeight Q M η z *
      RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z)) ≤
        (Q : ℝ) * sincSecondMoment Q / (3 * lam ^ 2)) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ (2 * Q : ℕ) - 2 → ∀ x : ℝ,
      RoughRegime.Lattice.gate Q (lam * η) x * |x| ^ r ≤ (lam * η) ^ r) ∧
    (∀ w : ℝ, ‖latticeCharacteristic Q M η lam w‖ ≤ 1 ∧
      ((¬ ∃ l : ℤ, |w - (l : ℝ) * M| ≤ 6 * Q / η) →
        latticeCharacteristic Q M η lam w = 0)) := by
  have hQ1 : 1 ≤ Q := by omega
  have hMpos : 0 < M := by omega
  refine ⟨latticeWeight_sum_one Q M η hQ1 hMpos hη hband, ?_,
    sampled_gate_deficit Q M η lam hQ hMpos hη hlam hband, ?_, ?_⟩
  · intro x
    exact ⟨RoughRegime.Lattice.gate_nonneg _ _ _, RoughRegime.Lattice.gate_le_one _ _ _⟩
  · intro r hr0 hrQ x
    apply gate_weighted_rpow Q r (lam * η) x hr0 (by linarith)
    exact mul_pos (by linarith) hη
  · intro w
    exact ⟨latticeCharacteristic_norm_le_one Q M η lam w hQ1 hMpos hη hband,
      latticeCharacteristic_eq_zero Q M η lam w hQ1 hMpos hη hlam⟩

end RoughRegime.LatticeFourier
