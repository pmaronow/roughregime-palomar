module

public import RoughRegime.GlobalPriorTarget


@[expose] public section
/-! Literal prior states produce the globally glued density and profiles.
Their actual integral target equals the block-prior target used for separation. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open RoughRegime.LatticeFourier
open scoped BigOperators ContDiff

 variable {D N : ℕ} {ι : Type*} [Fintype ι]
 abbrev PairState (ι : Type*) := (ι → ℤ) × (ℝ × (Bool × Bool))
 def stateAngles (z : GridPair D N → PairState ι) (k : GridPair D N) : ℝ := (z k).2.1
 def statePhases (U : SmoothStep) (M : ℕ) (a : ι → ℕ) (q : ι → Fin (D + 1)) (γ : ι → ℝ)
    (z : GridPair D N → PairState ι) (k : GridPair D N) : Model.Covariate (D + 1) → ℝ :=
  blockPhase U M a q γ (z k).1
 def stateGates (Q M : ℕ) (η lam : ι → ℝ) (z : GridPair D N → PairState ι) (k : GridPair D N) : ℝ :=
  jointGate Q M η lam (z k).1
 def stateSignU (z : GridPair D N → PairState ι) (k : GridPair D N) : ℝ := RoughRegime.Lower.sign (z k).2.2.1
 def stateSignV (z : GridPair D N → PairState ι) (k : GridPair D N) : ℝ := RoughRegime.Lower.sign (z k).2.2.2

 def canonicalProductTarget (U : SmoothStep) (Q M : ℕ) (a : ι → ℕ) (q : ι → Fin (D + 1))
    (γ η lam : ι → ℝ) (offset ell p0 lo hi Au Av : ℝ)
    (inner outer : Model.Covariate (D + 1) → ℝ) (z : GridPair D N → PairState ι) : ℝ :=
  globalProductTarget offset ell p0 (RoughRegime.Upper.intervalCenter lo hi) (RoughRegime.Upper.intervalHalfWidth lo hi) Au Av inner outer
    (stateAngles z) (statePhases U M a q γ z) (stateSignU z) (stateSignV z) (stateGates Q M η lam z)

 theorem canonicalProductTarget_eq (U : SmoothStep) (Q M : ℕ) (a : ι → ℕ) (q : ι → Fin (D + 1))
    (γ η lam : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4)
    (offset ell p0 lo hi Au Av : ℝ) (hell : 0 < ell) (hoff : 0 ≤ offset)
    (hsize : offset + ell * (2 * N : ℕ) ≤ 1) (hlo : 0 < lo) (hlt : lo < hi) (hp0 : lo ≤ p0 ∧ p0 ≤ hi)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hinner : ContDiff ℝ ∞ inner) (houter : ContDiff ℝ ∞ outer)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (hout01 : ∀ y, 0 ≤ outer y ∧ outer y ≤ 1)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1) (z : GridPair D N → PairState ι) :
    canonicalProductTarget (N := N) U Q M a q γ η lam offset ell p0 lo hi Au Av inner outer z =
      independentPairTarget ell
        (fun label => blockSpatialTarget U Q M a q γ η lam (fun y => inner (WithLp.toLp 2 y) ^ 2)
          lo hi Au Av (blockLabelIndex label)) z := by
  have hh : 0 < RoughRegime.Upper.intervalHalfWidth lo hi := by
    unfold RoughRegime.Upper.intervalHalfWidth
    linarith
  have hr : lo ≤ RoughRegime.Upper.intervalCenter lo hi - |RoughRegime.Upper.intervalHalfWidth lo hi| ∧
      RoughRegime.Upper.intervalCenter lo hi + |RoughRegime.Upper.intervalHalfWidth lo hi| ≤ hi := by
    rw [abs_of_pos hh]
    unfold RoughRegime.Upper.intervalCenter RoughRegime.Upper.intervalHalfWidth
    constructor <;> linarith
  have hp (k : GridPair D N) : ContDiff ℝ ∞ (statePhases U M a q γ z k) := blockPhase_smooth U M a q γ _ hγ hγ1
  have hne (b : GridBlock D N) (y : Model.Covariate (D + 1)) :
      blockDensity p0 (RoughRegime.Upper.intervalCenter lo hi) (RoughRegime.Upper.intervalHalfWidth lo hi)
        (stateAngles z b.1) (statePhases U M a q γ z b.1) outer (RoughRegime.Lower.sign b.2) y ≠ 0 := by
    have hs : |RoughRegime.Lower.sign b.2| ≤ 1 := by cases b.2 <;> norm_num [RoughRegime.Lower.sign]
    exact ne_of_gt (hlo.trans_le (blockDensity_bounds p0 _ _ _ _ lo hi _ _ hs hp0 hr hout01 y).1)
  unfold canonicalProductTarget independentPairTarget
  rw [globalProductTarget_integral offset ell p0 _ _ Au Av hell hoff hsize inner outer hin hout hinner houter
    (stateAngles z) (statePhases U M a q γ z) hp (stateSignU z) (stateSignV z) (stateGates Q M η lam z) hne]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  rw [cubeVolume_integral_transport]
  unfold blockSpatialTarget
  apply integral_congr_ae
  filter_upwards [] with y
  have hi := blockTarget_profile_identity U Q M a q γ η lam inner outer lo hi Au Av p0
    (blockLabelIndex b.2) hlo hlt hiota (z b.1).1 (z b.1).2 y
  rw [← sign_eq_blockLabelIndex b.2] at hi
  exact hi.symm

/-- Lemma14(d) for the literal globally glued density/profile target under
actual independent paired lattice/sign priors. -/
 theorem canonical_global_separation (U : SmoothStep) (Q M J : ℕ)
    (a : Fin J × Fin (D + 1) → ℕ) (q : Fin J × Fin (D + 1) → Fin (D + 1))
    (η : Fin J × Fin (D + 1) → ℝ) (hQ : 2 ≤ Q) (hM : 0 < M) (heven : Even M)
    (hη : ∀ i, 0 < η i) (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (γstar lamstar : ℝ) (hγ : 0 < γstar) (hγ1 : γstar ≤ 1 / 4) (hlam : 1 ≤ lamstar)
    (hlamBudget : 8 * Q * (D + 1) * sincSecondMoment Q / 3 ≤ lamstar ^ 2)
    (offset ell p0 lo hi Au Av : ℝ) (hell : 0 < ell) (hoff : 0 ≤ offset)
    (hsize : offset + ell * (2 * N : ℕ) ≤ 1) (hlo : 0 < lo) (hlt : lo < hi) (hp0 : lo ≤ p0 ∧ p0 ≤ hi)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hinner : ContDiff ℝ ∞ inner) (houter : ContDiff ℝ ∞ outer)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (hout01 : ∀ y, 0 ≤ outer y ∧ outer y ≤ 1)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1) (hinner1 : ∀ y, |inner y| ≤ 1)
    (hγbudget : γstar ≤ (∫ y, inner y ^ 2 ∂Model.cubeVolume (D + 1)) / (16 * (D + 1)))
    (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) :
    let μ := gatePrior Q M η (by omega) hM hη hband
    let γ := fun i : Fin J × Fin (D + 1) => γstar / ((i.1 : ℝ) + 1) ^ 2
    let lam := fun i : Fin J × Fin (D + 1) => lamstar * ((i.1 : ℝ) + 1)
    (9 * (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, inner y ^ 2 ∂Model.cubeVolume (D + 1)) /
      (16 * RoughRegime.Upper.intervalCenter lo hi)) * Au * Av * RoughRegime.Upper.intervalRho lo hi ^ M ≤
      (∫ z, canonicalProductTarget (N := N) U Q M a q γ η lam offset ell p0 lo hi Au Av inner outer z
        ∂globalBlockPrior (N := N) μ M true) -
      (∫ z, canonicalProductTarget (N := N) U Q M a q γ η lam offset ell p0 lo hi Au Av inner outer z
        ∂globalBlockPrior (N := N) μ M false) := by
  dsimp only
  let γ := fun i : Fin J × Fin (D + 1) => γstar / ((i.1 : ℝ) + 1) ^ 2
  let lam := fun i : Fin J × Fin (D + 1) => lamstar * ((i.1 : ℝ) + 1)
  let w := fun y : Fin (D + 1) → ℝ => inner (WithLp.toLp 2 y) ^ 2
  have hγpos (i : Fin J × Fin (D + 1)) : 0 < γ i := by dsimp [γ]; positivity
  have hγsmall (i : Fin J × Fin (D + 1)) : γ i ≤ 1 / 4 := sourceGamma_le_quarter γstar i.1.val hγ hγ1
  have heq : canonicalProductTarget (D := D) (N := N) U Q M a q γ η lam offset ell p0 lo hi Au Av inner outer =
      independentPairTarget ell (fun label => blockSpatialTarget U Q M a q γ η lam w lo hi Au Av (blockLabelIndex label)) := by
    funext z
    exact canonicalProductTarget_eq U Q M a q γ η lam hγpos hγsmall offset ell p0 lo hi Au Av hell hoff hsize hlo hlt hp0
      inner outer hinner houter hin hout hout01 hiota z
  change _ ≤ (∫ z, canonicalProductTarget (N := N) U Q M a q γ η lam offset ell p0 lo hi Au Av inner outer z ∂_) -
    (∫ z, canonicalProductTarget (N := N) U Q M a q γ η lam offset ell p0 lo hi Au Av inner outer z ∂_)
  rw [heq]
  have hw : Measurable w := ((hinner.continuous.measurable).comp (PiLp.volume_preserving_toLp (Fin (D + 1))).measurable).pow_const 2
  have hw1 (y : Fin (D + 1) → ℝ) : w y ≤ 1 := by
    have h := hinner1 (WithLp.toLp 2 y)
    have hh := mul_le_mul h h (abs_nonneg _) zero_le_one
    dsimp [w]
    nlinarith [sq_abs (inner (WithLp.toLp 2 y))]
  rw [cubeVolume_integral_transport (D + 1)]
  exact global_block_prior_separation (N := N) U Q M J a q η w hQ hM heven hη hband γstar lamstar hγ hγ1 hlam hlamBudget
    hw (fun y => sq_nonneg _) hw1 (by simpa only [cubeVolume_integral_transport (D + 1)] using hγbudget)
    lo hi Au Av ell hlo hlt hAu hAv hell.le

end RoughRegime.LatticePriors
