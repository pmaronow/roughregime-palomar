module

public import RoughRegime.CanonicalAdmissibility
public import RoughRegime.GridPairMass


@[expose] public section
/-! Exact (A4) density and signed numerator identities on the actual global
paired grid, including its cell boundaries. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open scoped BigOperators

 variable {D N : ℕ}

 theorem globalNumerator_eq_local_closed (offset ell A : ℝ) (hell : 0 < ell)
    (inner : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (σ S : GridPair D N → ℝ)
    (b : GridBlock D N) (x : Model.Covariate (D + 1)) (hx : x ∈ gridBlockClosed offset ell b) :
    globalNumerator offset ell A inner σ S x =
      A * σ b.1 * S b.1 * inner (gridCoords offset ell b x) := by
  unfold globalNumerator
  rw [Finset.sum_eq_single b]
  · rfl
  · intro a _ hab
    have hxa : x ∉ gridBlockOpen offset ell a := by
      intro hxa
      exact hab (gridClosedOpen_unique offset ell hell b a x hx hxa).symm
    rw [pulledCutoff_zero offset ell a inner hin x hxa, mul_zero]
  · simp

 theorem globalDensity_local_affine (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (outer : Model.Covariate (D + 1) → ℝ)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (b : GridBlock D N) (x : Model.Covariate (D + 1)) (hx : x ∈ gridBlockClosed offset ell b) :
    let y := gridCoords offset ell b x
    globalDensity offset ell p0 r0 h outer θ phase x =
      (p0 + outer y * (r0 - p0)) +
      (RoughRegime.Lower.sign b.2 * h * outer y * Real.cos (phase b.1 y)) * Real.cos (θ b.1) +
      (-(RoughRegime.Lower.sign b.2 * h * outer y * Real.sin (phase b.1 y))) * Real.sin (θ b.1) := by
  dsimp only
  rw [globalDensity_eq_local_closed offset ell p0 r0 h hell outer hout θ phase b x hx]
  exact blockDensity_theta_decomposition p0 r0 h (θ b.1) (RoughRegime.Lower.sign b.2) (phase b.1) outer _

 theorem globalProfile_local_density_product (offset ell p0 r0 h A : ℝ) (hell : 0 < ell)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (b : GridBlock D N) (x : Model.Covariate (D + 1))
    (hx : x ∈ gridBlockClosed offset ell b)
    (hp : globalDensity offset ell p0 r0 h outer θ phase x ≠ 0) :
    globalDensity offset ell p0 r0 h outer θ phase x *
      globalProfile offset ell p0 r0 h A inner outer θ phase σ S x =
      A * σ b.1 * S b.1 * inner (gridCoords offset ell b x) := by
  unfold globalProfile
  rw [mul_div_cancel₀ _ hp]
  exact globalNumerator_eq_local_closed offset ell A hell inner hin σ S b x hx

end RoughRegime.LatticePriors
