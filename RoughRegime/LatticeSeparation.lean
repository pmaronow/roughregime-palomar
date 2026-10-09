module

public import RoughRegime.GateExpectation
public import RoughRegime.LatticeConstruction
public import RoughRegime.SignPrior


@[expose] public section
/-! The actual dependent gate and spatial phase expectation in Lemma14(d).
The gate and phase use the same sampled lattice coefficients. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.DyadicDigits RoughRegime.Lattice
variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The concrete Euclidean phase in cube coordinates. -/
def cubePhase (U : SmoothStep) (M : ℕ) (a : ι → ℕ) (q : ι → Fin d)
    (γ : ι → ℝ) (z : ι → ℤ) (x : Fin d → ℝ) : ℝ :=
  blockPhase U M a q γ z (WithLp.toLp 2 x)

theorem cubePhase_measurable (U : SmoothStep) (M : ℕ) (a : ι → ℕ)
    (q : ι → Fin d) (γ : ι → ℝ) (z : ι → ℤ)
    (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4) :
    Measurable (cubePhase U M a q γ z) := by
  unfold cubePhase blockPhase coordinateSoftDigit
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (((softDigit_smooth U (γ i) (hγ i) (hγ1 i)).continuous.measurable).comp
    (measurable_const.mul (measurable_pi_apply (q i))))

theorem cubePhase_coherence (U : SmoothStep) (M : ℕ) (a : ι → ℕ)
    (q : ι → Fin d) (γ : ι → ℝ) (z : ι → ℤ)
    (hM : 0 < M) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4)
    (x : Fin d → ℝ) (hx : x ∉ cubeCollar d a q γ) :
    Real.cos ((M : ℝ) * cubePhase U M a q γ z x) = 1 := by
  apply blockPhase_coherence U M a q γ z hM hγ hγ1
  intro i k
  apply le_of_not_gt
  intro hh
  exact hx ⟨i, k, hh⟩

/-- The weighted spatial phase is uniformly positive under the actual collar budget. -/
theorem spatial_phase_half (U : SmoothStep) (M : ℕ) (a : ι → ℕ)
    (q : ι → Fin d) (γ : ι → ℝ) (z : ι → ℤ) (w : (Fin d → ℝ) → ℝ)
    (hM : 0 < M) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hbudget : 2 * (∑ i, γ i) ≤ (∫ x, w x ∂cubeUniform d) / 4) :
    (∫ x, w x ∂cubeUniform d) / 2 ≤
      ∫ x, w x * Real.cos ((M : ℝ) * cubePhase U M a q γ z x) ∂cubeUniform d := by
  have hi : Integrable w (cubeUniform d) := by
    apply Integrable.of_bound hw.aestronglyMeasurable 1
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 x)] using hw1 x
  apply weighted_coherence_half (cubeUniform d) (cubeCollar d a q γ)
    (cubeCollar_measurable d a q γ) w _ hi
    ((cubePhase_measurable U M a q γ z hγ hγ1).const_mul (M : ℝ)).cos.aestronglyMeasurable
    hw0 hw1 (fun x => Real.abs_cos_le_one _) (fun x hx => cubePhase_coherence U M a q γ z hM hγ hγ1 x hx)
  exact (cubeCollar_measureReal_le d a q γ (fun i => le_of_lt (hγ i))).trans hbudget

/-- A bounded weight gives an integrable coefficient-dependent spatial expectation. -/
theorem spatial_phase_norm_le_one (U : SmoothStep) (M : ℕ) (a : ι → ℕ)
    (q : ι → Fin d) (γ : ι → ℝ) (z : ι → ℤ) (w : (Fin d → ℝ) → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    ‖∫ x, w x * Real.cos ((M : ℝ) * cubePhase U M a q γ z x) ∂cubeUniform d‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := cubeUniform d) (C := (1 : ℝ))
    (f := fun x => w x * Real.cos ((M : ℝ) * cubePhase U M a q γ z x))
    (by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x)]
      exact (mul_le_mul (hw1 x) (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (by ring))
  simpa using h

/-- The full actual sampled-coefficient and cube expectation has the source9I/32 lower bound. -/
theorem sampled_spatial_gate_separation (U : SmoothStep) (Q M J d : ℕ)
    (a : Fin J × Fin d → ℕ) (q : Fin J × Fin d → Fin d)
    (η : Fin J × Fin d → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hQ : 2 ≤ Q) (hM : 0 < M) (hd : 0 < d) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (γstar lamstar : ℝ) (hγ : 0 < γstar) (hγ1 : γstar ≤ 1 / 4)
    (hlam : 1 ≤ lamstar)
    (hlamBudget : 8 * Q * d * sincSecondMoment Q / 3 ≤ lamstar ^ 2)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hγbudget : γstar ≤ (∫ x, w x ∂cubeUniform d) / (16 * d)) :
    9 * (∫ x, w x ∂cubeUniform d) / 32 ≤
      ∫ z, jointGate Q M η (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) z ^ 2 *
        (∫ x, w x * Real.cos ((M : ℝ) * cubePhase U M a q
          (fun i : Fin J × Fin d => γstar / ((i.1 : ℝ) + 1) ^ 2) z x) ∂cubeUniform d)
        ∂gatePrior Q M η (by omega) hM hη hband := by
  let γ (i : Fin J × Fin d) : ℝ := γstar / ((i.1 : ℝ) + 1) ^ 2
  let lam (i : Fin J × Fin d) : ℝ := lamstar * ((i.1 : ℝ) + 1)
  let S := jointGate Q M η lam
  let H (z : Fin J × Fin d → ℤ) := ∫ x, w x *
    Real.cos ((M : ℝ) * cubePhase U M a q γ z x) ∂cubeUniform d
  let μ := gatePrior Q M η (by omega : 1 ≤ Q) hM hη hband
  have hγpos (i : Fin J × Fin d) : 0 < γ i := by dsimp [γ]; positivity
  have hγsmall (i : Fin J × Fin d) : γ i ≤ 1 / 4 := by
    have hb : 1 ≤ ((i.1 : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg i.1.val : (0 : ℝ) ≤ i.1.val)]
    have ht : γ i ≤ γstar := by
      dsimp [γ]
      exact div_le_self (le_of_lt hγ) hb
    exact ht.trans hγ1
  have hH (z : Fin J × Fin d → ℤ) : (∫ x, w x ∂cubeUniform d) / 2 ≤ H z := by
    apply weighted_coherence_half (cubeUniform d) (cubeCollar d a q γ)
      (cubeCollar_measurable d a q γ) w _
    · apply Integrable.of_bound hw.aestronglyMeasurable 1
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 x)] using hw1 x
    · exact ((cubePhase_measurable U M a q γ z hγpos hγsmall).const_mul (M : ℝ)).cos.aestronglyMeasurable
    · exact hw0
    · exact hw1
    · exact fun x => Real.abs_cos_le_one _
    · exact fun x hx => cubePhase_coherence U M a q γ z hM hγpos hγsmall x hx
    · exact cubeCollar_level_budget_le_quarter J d hd a q γstar _ (le_of_lt hγ) hγbudget
  have hS2 : Integrable (fun z => S z ^ 2) μ := by
    apply Integrable.of_bound ((jointGate_measurable Q M η lam).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := jointGate_bounds Q M η lam z
    change (jointGate Q M η lam z) ^ 2 ≤ 1
    nlinarith
  have hprod : Integrable (fun z => S z ^ 2 * H z) μ := by
    apply hS2.mul_bdd (measurable_of_countable H).aestronglyMeasurable
    filter_upwards [] with z
    exact spatial_phase_norm_le_one U M a q γ z w hw0 hw1
  exact dependent_gate_separation μ S H _ (integral_nonneg hw0) hS2 hprod hH
    (levelGate_second_moment_nine_sixteenths Q M J d η hQ hM hη hband lamstar hlam hlamBudget)

/-- The geometric mean in the angular coefficient is bounded by the source r0. -/
theorem geometricMean_le_center (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    RoughRegime.Upper.intervalGeometricMean lo hi ≤ RoughRegime.Upper.intervalCenter lo hi := by
  have hhi : 0 < hi := hlo.trans hlt
  have hg : 0 ≤ Real.sqrt (lo * hi) := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt (mul_nonneg hlo.le hhi.le)
  unfold RoughRegime.Upper.intervalGeometricMean RoughRegime.Upper.intervalCenter
  nlinarith [sq_nonneg (hi - lo)]

/-- Actual iterated expectation of the target under the two paired sign laws. -/
def pairedBlockDifference (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (μ : Measure (ι → ℤ)) (w : (Fin d → ℝ) → ℝ)
    (lo hi Au Av : ℝ) (b : ℕ) : ℝ :=
  ∫ z, ∫ x,
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      ((∫ st, RoughRegime.Lower.sign st.1 * RoughRegime.Lower.sign st.2 *
          (Au * Av * jointGate Q M η lam z ^ 2 * w x) /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + cubePhase U M a q γ z x + (b : ℝ) * Real.pi))
            ∂(angularSignLaw M θ true).toMeasure) -
        (∫ st, RoughRegime.Lower.sign st.1 * RoughRegime.Lower.sign st.2 *
          (Au * Av * jointGate Q M η lam z ^ 2 * w x) /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + cubePhase U M a q γ z x + (b : ℝ) * Real.pi))
            ∂(angularSignLaw M θ false).toMeasure))) / (2 * Real.pi)
      ∂cubeUniform d ∂μ

/-- Actual conditional sign-law and uniform-angle expectations, followed by the
spatial and sampled-coefficient expectations, recover the source coefficient. -/
theorem paired_block_difference_exact (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (μ : Measure (ι → ℤ)) (w : (Fin d → ℝ) → ℝ)
    (lo hi Au Av : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (b : ℕ) (hM : 0 < M) (heven : Even M) :
    (∫ z, ∫ x,
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        ((∫ st, RoughRegime.Lower.sign st.1 * RoughRegime.Lower.sign st.2 *
            (Au * Av * jointGate Q M η lam z ^ 2 * w x) /
            (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
              Real.cos (θ + cubePhase U M a q γ z x + (b : ℝ) * Real.pi))
              ∂(angularSignLaw M θ true).toMeasure) -
          (∫ st, RoughRegime.Lower.sign st.1 * RoughRegime.Lower.sign st.2 *
            (Au * Av * jointGate Q M η lam z ^ 2 * w x) /
            (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
              Real.cos (θ + cubePhase U M a q γ z x + (b : ℝ) * Real.pi))
              ∂(angularSignLaw M θ false).toMeasure))) / (2 * Real.pi)
        ∂cubeUniform d ∂μ) =
      (2 * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M /
        RoughRegime.Upper.intervalGeometricMean lo hi) *
      ∫ z, jointGate Q M η lam z ^ 2 *
        (∫ x, w x * Real.cos ((M : ℝ) * cubePhase U M a q γ z x) ∂cubeUniform d) ∂μ := by
  simp_rw [angular_sign_reciprocal_difference lo hi _ _ hlo hlt M b hM heven]
  have he (z : ι → ℤ) :
      (∫ x, 2 * (Au * Av * jointGate Q M η lam z ^ 2 * w x) *
        RoughRegime.Upper.intervalRho lo hi ^ M * Real.cos ((M : ℝ) * cubePhase U M a q γ z x) /
        RoughRegime.Upper.intervalGeometricMean lo hi ∂cubeUniform d) =
        (2 * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M /
          RoughRegime.Upper.intervalGeometricMean lo hi) *
          (jointGate Q M η lam z ^ 2 *
            ∫ x, w x * Real.cos ((M : ℝ) * cubePhase U M a q γ z x) ∂cubeUniform d) := by
    calc
      _ = ∫ x, ((2 * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M /
          RoughRegime.Upper.intervalGeometricMean lo hi) * jointGate Q M η lam z ^ 2) *
          (w x * Real.cos ((M : ℝ) * cubePhase U M a q γ z x)) ∂cubeUniform d := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by rw [integral_const_mul]; ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- The paper's exact constant for one normalized block, including its volume.
No independent-phase assumption is needed: the same coefficients determine S and phi. -/
theorem paired_block_difference_lower (U : SmoothStep) (Q M J d : ℕ)
    (a : Fin J × Fin d → ℕ) (q : Fin J × Fin d → Fin d)
    (η : Fin J × Fin d → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hQ : 2 ≤ Q) (hM : 0 < M) (heven : Even M) (hd : 0 < d)
    (hη : ∀ i, 0 < η i) (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (γstar lamstar : ℝ) (hγ : 0 < γstar) (hγ1 : γstar ≤ 1 / 4) (hlam : 1 ≤ lamstar)
    (hlamBudget : 8 * Q * d * sincSecondMoment Q / 3 ≤ lamstar ^ 2)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hγbudget : γstar ≤ (∫ x, w x ∂cubeUniform d) / (16 * d))
    (lo hi Au Av v0 : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hv0 : 0 ≤ v0) (b : ℕ) :
    (9 * v0 * (∫ x, w x ∂cubeUniform d) /
      (16 * RoughRegime.Upper.intervalCenter lo hi)) *
        Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M ≤
      v0 * pairedBlockDifference U Q M a q
        (fun i : Fin J × Fin d => γstar / ((i.1 : ℝ) + 1) ^ 2) η
        (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1))
        (gatePrior Q M η (by omega) hM hη hband) w lo hi Au Av b := by
  let I : ℝ := ∫ x, w x ∂cubeUniform d
  let H : ℝ := ∫ z, jointGate Q M η
    (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) z ^ 2 *
      (∫ x, w x * Real.cos ((M : ℝ) * cubePhase U M a q
        (fun i : Fin J × Fin d => γstar / ((i.1 : ℝ) + 1) ^ 2) z x) ∂cubeUniform d)
      ∂gatePrior Q M η (by omega) hM hη hband
  have hsep : 9 * I / 32 ≤ H := sampled_spatial_gate_separation U Q M J d a q η w
    hQ hM hd hη hband γstar lamstar hγ hγ1 hlam hlamBudget hw hw0 hw1 hγbudget
  have hI : 0 ≤ I := integral_nonneg hw0
  have hrho : 0 ≤ RoughRegime.Upper.intervalRho lo hi ^ M :=
    pow_nonneg (RoughRegime.Upper.intervalRho_pos lo hi hlo hlt).le _
  have hg : 0 < RoughRegime.Upper.intervalGeometricMean lo hi :=
    Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt))
  have hgc := geometricMean_le_center lo hi hlo hlt
  have hn : 0 ≤ 9 * I * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M / 16 := by positivity
  have hden := div_le_div_of_nonneg_left hn hg hgc
  have hmul := mul_le_mul_of_nonneg_left hsep
    (show 0 ≤ 2 * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M /
      RoughRegime.Upper.intervalGeometricMean lo hi by positivity)
  have hmain : (9 * I / (16 * RoughRegime.Upper.intervalCenter lo hi)) *
      Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M ≤
      (2 * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M /
        RoughRegime.Upper.intervalGeometricMean lo hi) * H := by
    calc
      _ = (9 * I * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M / 16) /
          RoughRegime.Upper.intervalCenter lo hi := by ring
      _ ≤ (9 * I * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M / 16) /
          RoughRegime.Upper.intervalGeometricMean lo hi := hden
      _ = (2 * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M /
          RoughRegime.Upper.intervalGeometricMean lo hi) * (9 * I / 32) := by ring
      _ ≤ _ := hmul
  have hx := paired_block_difference_exact U Q M a q
    (fun i : Fin J × Fin d => γstar / ((i.1 : ℝ) + 1) ^ 2) η
    (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1))
    (gatePrior Q M η (by omega) hM hη hband) w lo hi Au Av hlo hlt b hM heven
  change pairedBlockDifference U Q M a q _ η _ _ w lo hi Au Av b =
    (2 * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M /
      RoughRegime.Upper.intervalGeometricMean lo hi) * H at hx
  rw [hx]
  convert mul_le_mul_of_nonneg_left hmain hv0 using 1
  dsimp [I]
  ring

end RoughRegime.LatticePriors
