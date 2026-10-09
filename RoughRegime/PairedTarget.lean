module

public import RoughRegime.LatticeSeparation
public import RoughRegime.AngularLaw


@[expose] public section
/-! Target expectations under the genuine independent coefficient / angle-sign
prior. These identities justify moving the spatial integral inside prior expectation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.DyadicDigits
variable {d : ℕ} {ι : Type*} [Fintype ι]

def blockTarget (U : SmoothStep) (Q M : ℕ) (a : ι → ℕ) (q : ι → Fin d)
    (γ η lam : ι → ℝ) (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (z : ι → ℤ) (ts : ℝ × (Bool × Bool)) (x : Fin d → ℝ) : ℝ :=
  RoughRegime.Lower.sign ts.2.1 * RoughRegime.Lower.sign ts.2.2 *
    (Au * Av * jointGate Q M η lam z ^ 2 * w x) /
    (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
      Real.cos (ts.1 + cubePhase U M a q γ z x + (b : ℝ) * Real.pi))

theorem cubePhase_joint_measurable (U : SmoothStep) (M : ℕ) (a : ι → ℕ)
    (q : ι → Fin d) (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4) :
    Measurable (fun zx : (ι → ℤ) × (Fin d → ℝ) => cubePhase U M a q γ zx.1 zx.2) := by
  unfold cubePhase blockPhase coordinateSoftDigit
  apply Finset.measurable_sum
  intro i _
  apply Measurable.mul
  · exact measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp ((measurable_pi_apply i).comp measurable_fst))
  · exact ((softDigit_smooth U (γ i) (hγ i) (hγ1 i)).continuous.measurable).comp
      (measurable_const.mul ((measurable_pi_apply (q i)).comp measurable_snd))

theorem blockTarget_measurable (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4) (hw : Measurable w) :
    Measurable (fun p : ((ι → ℤ) × (ℝ × (Bool × Bool))) × (Fin d → ℝ) =>
      blockTarget U Q M a q γ η lam w lo hi Au Av b p.1.1 p.1.2 p.2) := by
  let X := ((ι → ℤ) × (ℝ × (Bool × Bool))) × (Fin d → ℝ)
  have hz : Measurable (fun p : X => p.1.1) := measurable_fst.fst
  have hx : Measurable (fun p : X => p.2) := measurable_snd
  have ht : Measurable (fun p : X => p.1.2.1) := measurable_fst.snd.fst
  have hu : Measurable (fun p : X => p.1.2.2.1) := measurable_fst.snd.snd.fst
  have hv : Measurable (fun p : X => p.1.2.2.2) := measurable_fst.snd.snd.snd
  have hs := (measurable_of_countable RoughRegime.Lower.sign).comp hu
  have hs' := (measurable_of_countable RoughRegime.Lower.sign).comp hv
  have hgate := ((jointGate_measurable Q M η lam).comp hz).pow_const 2
  have hphase := (cubePhase_joint_measurable U M a q γ hγ hγ1).comp (hz.prodMk hx)
  exact ((hs.mul hs').mul ((measurable_const.mul hgate).mul (hw.comp hx))).div
    (measurable_const.add (measurable_const.mul ((ht.add hphase).add measurable_const).cos))

theorem blockTarget_norm_le (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (hlo : 0 < lo) (hlt : lo < hi) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (z : ι → ℤ) (ts : ℝ × (Bool × Bool)) (x : Fin d → ℝ) :
    ‖blockTarget U Q M a q γ η lam w lo hi Au Av b z ts x‖ ≤ |Au * Av| / lo := by
  let r : ℝ := RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
      Real.cos (ts.1 + cubePhase U M a q γ z x + (b : ℝ) * Real.pi)
  have hhalf : 0 < RoughRegime.Upper.intervalHalfWidth lo hi := by
    unfold RoughRegime.Upper.intervalHalfWidth; positivity
  have hr : lo ≤ r := by
    have hc := mul_le_mul_of_nonneg_left
      (Real.neg_one_le_cos (ts.1 + cubePhase U M a q γ z x + (b : ℝ) * Real.pi)) hhalf.le
    dsimp [r]
    unfold RoughRegime.Upper.intervalCenter RoughRegime.Upper.intervalHalfWidth at *
    linarith
  have hr0 : 0 < r := hlo.trans_le hr
  have hs := jointGate_bounds Q M η lam z
  have hs2 : jointGate Q M η lam z ^ 2 ≤ 1 := by nlinarith
  have hsign (v : Bool) : |RoughRegime.Lower.sign v| = 1 := by cases v <;> norm_num [RoughRegime.Lower.sign]
  have hnum : |RoughRegime.Lower.sign ts.2.1 * RoughRegime.Lower.sign ts.2.2 *
      (Au * Av * jointGate Q M η lam z ^ 2 * w x)| ≤ |Au * Av| := by
    calc
      _ = |Au * Av| * jointGate Q M η lam z ^ 2 * w x := by
        simp only [abs_mul, hsign, abs_of_nonneg (sq_nonneg (jointGate Q M η lam z)), abs_of_nonneg (hw0 x), one_mul]
      _ ≤ |Au * Av| * 1 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hs2 (abs_nonneg _)) (hw1 x) (hw0 x) (by positivity)
      _ = _ := by ring
  unfold blockTarget
  rw [Real.norm_eq_abs, abs_div]
  change _ / |r| ≤ _
  rw [abs_of_pos hr0]
  exact div_le_div₀ (abs_nonneg _) hnum hlo hr

/-- The actual conditional sign expectation is an elementary measurable function of theta. -/
theorem conditionalTarget_mean (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (z : ι → ℤ) (x : Fin d → ℝ) (positive : Bool) (θ : ℝ) :
    (∫ st, blockTarget U Q M a q γ η lam w lo hi Au Av b z (θ, st) x
      ∂(angularSignLaw M θ positive).toMeasure) =
    ((if positive then 1 else -1) * Real.cos ((M : ℝ) * θ)) *
      (Au * Av * jointGate Q M η lam z ^ 2 * w x /
        (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
          Real.cos (θ + cubePhase U M a q γ z x + (b : ℝ) * Real.pi))) := by
  have he : (fun st : Bool × Bool => blockTarget U Q M a q γ η lam w lo hi Au Av b z (θ, st) x) =
      (fun st => RoughRegime.Lower.sign st.1 * RoughRegime.Lower.sign st.2 *
        (Au * Av * jointGate Q M η lam z ^ 2 * w x /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + cubePhase U M a q γ z x + (b : ℝ) * Real.pi)))) := by
    funext st
    unfold blockTarget
    ring
  rw [he]
  exact signLaw_product_mean _ _ _

theorem conditionalTarget_integrable_angle (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (hlo : 0 < lo) (hlt : lo < hi) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (z : ι → ℤ) (x : Fin d → ℝ) (positive : Bool) :
    Integrable (fun θ => ∫ st, blockTarget U Q M a q γ η lam w lo hi Au Av b z (θ, st) x
      ∂(angularSignLaw M θ positive).toMeasure) angleUniform := by
  have hm : Measurable (fun θ => ∫ st, blockTarget U Q M a q γ η lam w lo hi Au Av b z (θ, st) x
      ∂(angularSignLaw M θ positive).toMeasure) := by
    simp_rw [conditionalTarget_mean]
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (|Au * Av| / lo)
  filter_upwards [] with θ
  have h := norm_integral_le_of_norm_le_const (μ := (angularSignLaw M θ positive).toMeasure)
    (C := |Au * Av| / lo) (f := fun st => blockTarget U Q M a q γ η lam w lo hi Au Av b z (θ, st) x)
    (ae_of_all _ (fun st => blockTarget_norm_le U Q M a q γ η lam w lo hi Au Av b hlo hlt hw0 hw1 z (θ, st) x))
  simpa using h

/-- Independent coefficient and conditional-angle/sign laws are genuine product priors. -/
def blockPrior (μ : Measure (ι → ℤ)) (M : ℕ) (positive : Bool) :
    Measure ((ι → ℤ) × (ℝ × (Bool × Bool))) := μ.prod (angleSignLaw M positive)

instance blockPrior_probability (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ]
    (M : ℕ) (positive : Bool) : IsProbabilityMeasure (blockPrior μ M positive) := by
  unfold blockPrior
  infer_instance

/-- The block target is its actual spatial integral, with prior parameters fixed. -/
def blockSpatialTarget (U : SmoothStep) (Q M : ℕ) (a : ι → ℕ) (q : ι → Fin d)
    (γ η lam : ι → ℝ) (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (zt : (ι → ℤ) × (ℝ × (Bool × Bool))) : ℝ :=
  ∫ x, blockTarget U Q M a q γ η lam w lo hi Au Av b zt.1 zt.2 x ∂cubeUniform d

theorem blockTarget_integrable (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4) (hw : Measurable w)
    (hlo : 0 < lo) (hlt : lo < hi) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (positive : Bool) :
    Integrable (fun p => blockTarget U Q M a q γ η lam w lo hi Au Av b p.1.1 p.1.2 p.2)
      ((blockPrior μ M positive).prod (cubeUniform d)) := by
  apply Integrable.of_bound
    (blockTarget_measurable U Q M a q γ η lam w lo hi Au Av b hγ hγ1 hw).aestronglyMeasurable (|Au * Av| / lo)
  filter_upwards [] with p
  exact blockTarget_norm_le U Q M a q γ η lam w lo hi Au Av b hlo hlt hw0 hw1 p.1.1 p.1.2 p.2

/-- The actual joint-prior difference equals the spatially reordered expectation.
This is a Fubini theorem for the concrete bounded target, not an assumed identity. -/
theorem actual_block_prior_difference (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (w : (Fin d → ℝ) → ℝ) (lo hi Au Av : ℝ) (b : ℕ)
    (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4) (hw : Measurable w)
    (hlo : 0 < lo) (hlt : lo < hi) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] :
    (∫ zt, blockSpatialTarget U Q M a q γ η lam w lo hi Au Av b zt ∂blockPrior μ M true) -
      (∫ zt, blockSpatialTarget U Q M a q γ η lam w lo hi Au Av b zt ∂blockPrior μ M false) =
        pairedBlockDifference U Q M a q γ η lam μ w lo hi Au Av b := by
  have hwhole (p : Bool) := blockTarget_integrable U Q M a q γ η lam w lo hi Au Av b
    hγ hγ1 hw hlo hlt hw0 hw1 μ p
  have hspatial (p : Bool) : Integrable (blockSpatialTarget U Q M a q γ η lam w lo hi Au Av b)
      (blockPrior μ M p) := (hwhole p).integral_prod_left
  rw [blockPrior, blockPrior, integral_prod _ (hspatial true), integral_prod _ (hspatial false)]
  rw [← integral_sub ((hspatial true).integral_prod_left) ((hspatial false).integral_prod_left)]
  apply integral_congr_ae
  filter_upwards [] with z
  have hm : Measurable (fun tx : (ℝ × (Bool × Bool)) × (Fin d → ℝ) =>
      blockTarget U Q M a q γ η lam w lo hi Au Av b z tx.1 tx.2) :=
    (blockTarget_measurable U Q M a q γ η lam w lo hi Au Av b hγ hγ1 hw).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hpair (p : Bool) : Integrable (fun tx : (ℝ × (Bool × Bool)) × (Fin d → ℝ) =>
      blockTarget U Q M a q γ η lam w lo hi Au Av b z tx.1 tx.2)
        ((angleSignLaw M p).prod (cubeUniform d)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (|Au * Av| / lo)
    filter_upwards [] with tx
    exact blockTarget_norm_le U Q M a q γ η lam w lo hi Au Av b hlo hlt hw0 hw1 z tx.1 tx.2
  have hswap (p : Bool) :
      (∫ ts, ∫ x, blockTarget U Q M a q γ η lam w lo hi Au Av b z ts x
        ∂cubeUniform d ∂angleSignLaw M p) =
      ∫ x, ∫ ts, blockTarget U Q M a q γ η lam w lo hi Au Av b z ts x
        ∂angleSignLaw M p ∂cubeUniform d := integral_integral_swap (hpair p)
  unfold blockSpatialTarget
  rw [hswap true, hswap false,
    ← integral_sub ((hpair true).integral_prod_right) ((hpair false).integral_prod_right)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hiθ (p : Bool) : Integrable (fun ts => blockTarget U Q M a q γ η lam w lo hi Au Av b z ts x)
      (angleSignLaw M p) := by
    apply Integrable.of_bound (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable (|Au * Av| / lo)
    filter_upwards [] with ts
    exact blockTarget_norm_le U Q M a q γ η lam w lo hi Au Av b hlo hlt hw0 hw1 z ts x
  rw [integral_angleSignLaw _ _ _ (hiθ true), integral_angleSignLaw _ _ _ (hiθ false)]
  have hlin := integral_sub
    (conditionalTarget_integrable_angle U Q M a q γ η lam w lo hi Au Av b hlo hlt hw0 hw1 z x true)
    (conditionalTarget_integrable_angle U Q M a q γ η lam w lo hi Au Av b hlo hlt hw0 hw1 z x false)
  rw [integral_angleUniform, integral_angleUniform, integral_angleUniform] at hlin
  exact hlin.symm

/-- The source separation constant holds under the genuine product priors. -/
theorem actual_block_prior_separation (U : SmoothStep) (Q M J d : ℕ)
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
      (16 * RoughRegime.Upper.intervalCenter lo hi)) * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M ≤
      v0 * ((∫ zt, blockSpatialTarget U Q M a q
        (fun i : Fin J × Fin d => γstar / ((i.1 : ℝ) + 1) ^ 2) η
        (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) w lo hi Au Av b zt
        ∂blockPrior (gatePrior Q M η (by omega) hM hη hband) M true) -
      (∫ zt, blockSpatialTarget U Q M a q
        (fun i : Fin J × Fin d => γstar / ((i.1 : ℝ) + 1) ^ 2) η
        (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) w lo hi Au Av b zt
        ∂blockPrior (gatePrior Q M η (by omega) hM hη hband) M false)) := by
  have hγpos (i : Fin J × Fin d) : 0 < γstar / ((i.1 : ℝ) + 1) ^ 2 := by positivity
  have hγsmall (i : Fin J × Fin d) : γstar / ((i.1 : ℝ) + 1) ^ 2 ≤ 1 / 4 := by
    have hb : 1 ≤ ((i.1 : ℝ) + 1) ^ 2 := by
      nlinarith [(Nat.cast_nonneg i.1.val : (0 : ℝ) ≤ i.1.val)]
    exact (div_le_self hγ.le hb).trans hγ1
  rw [actual_block_prior_difference U Q M a q _ η _ w lo hi Au Av b
    hγpos hγsmall hw hlo hlt hw0 hw1]
  exact paired_block_difference_lower U Q M J d a q η w hQ hM heven hd hη hband
    γstar lamstar hγ hγ1 hlam hlamBudget hw hw0 hw1 hγbudget lo hi Au Av v0 hlo hlt hAu hAv hv0 b

/-- The displayed reciprocal target is exactly p times the two actual smooth
profiles. The outer cutoff is only required to equal1 wherever the inner cutoff is nonzero. -/
theorem blockTarget_profile_identity (U : SmoothStep) (Q M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ η lam : ι → ℝ)
    (iotaIn iotaOut : Model.Covariate d → ℝ) (lo hi Au Av p0 : ℝ) (b : ℕ)
    (hlo : 0 < lo) (hlt : lo < hi)
    (hiota : ∀ x, iotaIn x ≠ 0 → iotaOut x = 1)
    (z : ι → ℤ) (ts : ℝ × (Bool × Bool)) (x : Fin d → ℝ) :
    blockTarget U Q M a q γ η lam (fun y => iotaIn (WithLp.toLp 2 y) ^ 2)
      lo hi Au Av b z ts x =
    let p := blockDensity p0 (RoughRegime.Upper.intervalCenter lo hi)
      (RoughRegime.Upper.intervalHalfWidth lo hi) ts.1 (blockPhase U M a q γ z) iotaOut ((-1 : ℝ) ^ b)
    p (WithLp.toLp 2 x) *
      blockProfile Au (RoughRegime.Lower.sign ts.2.1) (jointGate Q M η lam z) iotaIn p (WithLp.toLp 2 x) *
      blockProfile Av (RoughRegime.Lower.sign ts.2.2) (jointGate Q M η lam z) iotaIn p (WithLp.toLp 2 x) := by
  let p := blockDensity p0 (RoughRegime.Upper.intervalCenter lo hi)
    (RoughRegime.Upper.intervalHalfWidth lo hi) ts.1 (blockPhase U M a q γ z) iotaOut ((-1 : ℝ) ^ b)
  by_cases hx : iotaIn (WithLp.toLp 2 x) = 0
  · simp [blockTarget, blockProfile, hx]
  · have hp : p (WithLp.toLp 2 x) = RoughRegime.Upper.intervalCenter lo hi +
        RoughRegime.Upper.intervalHalfWidth lo hi *
          Real.cos (ts.1 + cubePhase U M a q γ z x + (b : ℝ) * Real.pi) := by
      dsimp [p, blockDensity, blockOscillatingDensity, cubePhase]
      rw [hiota _ hx, one_mul, Real.cos_add_nat_mul_pi]
      ring
    have hp0 : p (WithLp.toLp 2 x) ≠ 0 := by
      rw [hp]
      exact ne_of_gt (RoughRegime.Upper.interval_angular_pos lo hi _ hlo hlt)
    change _ = p (WithLp.toLp 2 x) *
      blockProfile Au (RoughRegime.Lower.sign ts.2.1) (jointGate Q M η lam z) iotaIn p (WithLp.toLp 2 x) *
      blockProfile Av (RoughRegime.Lower.sign ts.2.2) (jointGate Q M η lam z) iotaIn p (WithLp.toLp 2 x)
    unfold blockTarget blockProfile
    rw [← hp]
    field_simp

end RoughRegime.LatticePriors
