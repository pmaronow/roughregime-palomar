module

public import RoughRegime.GridIntegral
public import RoughRegime.HolderGeometry
public import RoughRegime.GeneralTesting


@[expose] public section
/-! Exact cancellation and normalization of every globally glued density. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open scoped BigOperators ContDiff

 variable {D N : ℕ}

 theorem continuous_cube_integrable (f : Model.Covariate (D + 1) → ℝ) (hf : Continuous f) :
    Integrable f (Model.cubeVolume (D + 1)) :=
  hf.continuousOn.integrableOn_compact (Model.isCompact_cube _)

 def localDensityDelta (p0 r0 h θ : ℝ) (outer phase : Model.Covariate (D + 1) → ℝ)
    (label : Bool) (y : Model.Covariate (D + 1)) : ℝ :=
  outer y * (blockOscillatingDensity r0 h θ phase (RoughRegime.Lower.sign label) y - p0)

 theorem localDensityDelta_continuous (p0 r0 h θ : ℝ) (outer phase : Model.Covariate (D + 1) → ℝ)
    (ho : Continuous outer) (hp : Continuous phase) (label : Bool) :
    Continuous (localDensityDelta p0 r0 h θ outer phase label) := by
  unfold localDensityDelta blockOscillatingDensity
  fun_prop

 theorem localDensityDelta_pair (p0 r0 h θ : ℝ) (outer phase : Model.Covariate (D + 1) → ℝ)
    (y : Model.Covariate (D + 1)) :
    localDensityDelta p0 r0 h θ outer phase false y + localDensityDelta p0 r0 h θ outer phase true y =
      2 * (r0 - p0) * outer y := by
  unfold localDensityDelta blockOscillatingDensity
  norm_num [RoughRegime.Lower.sign]
  ring

 theorem globalDensity_integral (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1)
    (outer : Model.Covariate (D + 1) → ℝ) (ho : Continuous outer)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hphase : ∀ k, Continuous (phase k)) :
    (∫ x, globalDensity offset ell p0 r0 h outer θ phase x ∂Model.cubeVolume (D + 1)) =
      p0 + (ell * (2 * N : ℕ)) ^ (D + 1) *
        (∫ y, outer y ∂Model.cubeVolume (D + 1)) * (r0 - p0) := by
  let μ := Model.cubeVolume (D + 1)
  let δ (b : GridBlock D N) := localDensityDelta p0 r0 h (θ b.1) outer (phase b.1) b.2
  have hδ (b : GridBlock D N) : Continuous (δ b) := localDensityDelta_continuous _ _ _ _ _ _ ho (hphase b.1) b.2
  have hi (b : GridBlock D N) : Integrable (fun x => δ b (gridCoords offset ell b x)) μ :=
    continuous_cube_integrable _ ((hδ b).comp (gridCoords_smooth offset ell b).continuous)
  have heq : globalDensity offset ell p0 r0 h outer θ phase = fun x => p0 + ∑ b : GridBlock D N, δ b (gridCoords offset ell b x) := rfl
  rw [heq, integral_add (integrable_const p0) (integrable_finsetSum Finset.univ (fun b _ => hi b)),
    integral_finsetSum Finset.univ (fun b _ => hi b)]
  have hμ : μ.real univ = 1 := by simp [μ]
  simp only [integral_const, hμ, one_smul]
  have hchange (b : GridBlock D N) : (∫ x, δ b (gridCoords offset ell b x) ∂μ) = ell ^ (D + 1) * ∫ y, δ b y ∂μ := by
    apply grid_pull_integral_cube offset ell hell b hoff hsize
    intro y hy
    dsimp [δ, localDensityDelta]
    rw [hout y hy, zero_mul]
  simp_rw [hchange]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have hpairs (k : GridPair D N) : (∑ label : Bool, ∫ y, δ (k, label) y ∂μ) =
      2 * (r0 - p0) * ∫ y, outer y ∂μ := by
    rw [Fintype.sum_bool, ← integral_add
      (continuous_cube_integrable _ (hδ (k, true))) (continuous_cube_integrable _ (hδ (k, false)))]
    have heq' : (fun y => δ (k, true) y + δ (k, false) y) = fun y => 2 * (r0 - p0) * outer y := by
      funext y
      rw [add_comm]
      exact localDensityDelta_pair p0 r0 h (θ k) outer (phase k) y
    rw [heq', integral_const_mul]
  simp_rw [hpairs]
  simp only [Finset.sum_const, Finset.card_univ, gridPair_card, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  simp only [mul_pow, pow_succ]
  dsimp only [μ]
  ring

 theorem globalDensity_integral_one (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1)
    (outer : Model.Covariate (D + 1) → ℝ) (ho : Continuous outer)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hphase : ∀ k, Continuous (phase k))
    (hden : 1 - (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, outer y ∂Model.cubeVolume (D + 1)) ≠ 0)
    (hp0 : p0 = (1 - (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, outer y ∂Model.cubeVolume (D + 1)) * r0) /
      (1 - (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, outer y ∂Model.cubeVolume (D + 1)))) :
    (∫ x, globalDensity offset ell p0 r0 h outer θ phase x ∂Model.cubeVolume (D + 1)) = 1 := by
  rw [globalDensity_integral offset ell p0 r0 h hell hoff hsize outer ho hout θ phase hphase]
  have hh := total_density_mass p0 r0 ((ell * (2 * N : ℕ)) ^ (D + 1))
    (∫ y, outer y ∂Model.cubeVolume (D + 1)) hden hp0
  nlinarith

/-- Every realization defines a genuine probability density relative to the
actual Lebesgue unit-cube design. -/
 def globalDensityLaw (offset ell p0 r0 h lo hi : ℝ) (hell : 0 < ell)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1)
    (outer : Model.Covariate (D + 1) → ℝ) (ho : Continuous outer)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (hout01 : ∀ y, 0 ≤ outer y ∧ outer y ≤ 1)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hphase : ∀ k, Continuous (phase k)) (hlo : 0 ≤ lo)
    (hp0 : lo ≤ p0 ∧ p0 ≤ hi) (hr : lo ≤ r0 - |h| ∧ r0 + |h| ≤ hi)
    (hden : 1 - (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, outer y ∂Model.cubeVolume (D + 1)) ≠ 0)
    (hbase : p0 = (1 - (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, outer y ∂Model.cubeVolume (D + 1)) * r0) /
      (1 - (ell * (2 * N : ℕ)) ^ (D + 1) * (∫ y, outer y ∂Model.cubeVolume (D + 1)))) :
    GeneralTesting.DensityLaw (Model.cubeVolume (D + 1)) where
  density := globalDensity offset ell p0 r0 h outer θ phase
  measurable := by
    apply Continuous.measurable
    unfold globalDensity pulledCutoff gridCoords blockOscillatingDensity
    fun_prop
  integrable := by
    apply continuous_cube_integrable
    unfold globalDensity pulledCutoff gridCoords blockOscillatingDensity
    fun_prop
  nonneg := Filter.Eventually.of_forall (fun x => hlo.trans
    (globalDensity_bounds offset ell p0 r0 h lo hi hell outer hout hout01 θ phase hp0 hr x).1)
  integral_one := globalDensity_integral_one offset ell p0 r0 h hell hoff hsize outer ho hout θ phase hphase hden hbase

 theorem globalDensity_block_mass (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (outer : Model.Covariate (D + 1) → ℝ)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ) (b : GridBlock D N) :
    (∫ x in gridBlockClosed offset ell b, globalDensity offset ell p0 r0 h outer θ phase x) =
      ell ^ (D + 1) * ∫ y, blockDensity p0 r0 h (θ b.1) (phase b.1) outer (RoughRegime.Lower.sign b.2) y
        ∂Model.cubeVolume (D + 1) := by
  rw [setIntegral_congr_fun (gridBlockClosed_measurable offset ell b)
    (fun x hx => globalDensity_eq_local_closed offset ell p0 r0 h hell outer hout θ phase b x hx)]
  exact grid_block_integral offset ell hell b _

/-- Exact sourcepairmass2*(v0/B)*barp, independent of every realization's angle and coefficient state. -/
 theorem globalDensity_pair_mass (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (outer : Model.Covariate (D + 1) → ℝ) (ho : ContDiff ℝ ∞ outer)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (phase k)) (k : GridPair D N) :
    (∑ label : Bool, ∫ x in gridBlockClosed offset ell (k, label), globalDensity offset ell p0 r0 h outer θ phase x) =
      2 * ell ^ (D + 1) * (p0 + (∫ y, outer y ∂Model.cubeVolume (D + 1)) * (r0 - p0)) := by
  simp_rw [globalDensity_block_mass offset ell p0 r0 h hell outer hout θ phase]
  rw [← Finset.mul_sum, Fintype.sum_bool]
  have hi (label : Bool) := continuous_cube_integrable _
    (blockDensity_smooth p0 r0 h (θ k) (RoughRegime.Lower.sign label) (phase k) outer (hp k) ho).continuous
  rw [← integral_add (hi true) (hi false)]
  have heq : (fun y => blockDensity p0 r0 h (θ k) (phase k) outer (RoughRegime.Lower.sign true) y +
      blockDensity p0 r0 h (θ k) (phase k) outer (RoughRegime.Lower.sign false) y) =
      fun y => 2 * (p0 + outer y * (r0 - p0)) := by
    funext y
    exact blockDensity_pair_cancellation p0 r0 h (θ k) (phase k) outer y
  rw [heq, integral_const_mul, integral_add (integrable_const _) ((continuous_cube_integrable outer ho.continuous).mul_const _), integral_mul_const]
  simp only [integral_const]
  have hμ : (Model.cubeVolume (D + 1)).real univ = 1 := by simp
  rw [hμ, one_smul]
  ring

end RoughRegime.LatticePriors
