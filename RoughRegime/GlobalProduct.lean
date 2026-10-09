module

public import RoughRegime.GlobalLatticeMass
public import RoughRegime.CubeTransport


@[expose] public section
/-! The literal global integral of p*u*v is the scaled sum of its local block integrals. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open scoped BigOperators ContDiff

 variable {D N : ℕ}

 def localPairProduct (p0 r0 h Au Av : ℝ) (inner outer : Model.Covariate (D + 1) → ℝ)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σu σv S : GridPair D N → ℝ) (b : GridBlock D N) (y : Model.Covariate (D + 1)) : ℝ :=
  let p := blockDensity p0 r0 h (θ b.1) (phase b.1) outer (RoughRegime.Lower.sign b.2)
  p y * blockProfile Au (σu b.1) (S b.1) inner p y * blockProfile Av (σv b.1) (S b.1) inner p y

 def globalProductTarget (offset ell p0 r0 h Au Av : ℝ)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σu σv S : GridPair D N → ℝ) : ℝ :=
  ∫ x, globalDensity offset ell p0 r0 h outer θ phase x *
    globalProfile offset ell p0 r0 h Au inner outer θ phase σu S x *
    globalProfile offset ell p0 r0 h Av inner outer θ phase σv S x ∂Model.cubeVolume (D + 1)

 theorem localPairProduct_zero (p0 r0 h Au Av : ℝ) (inner outer : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σu σv S : GridPair D N → ℝ) (b : GridBlock D N) (y : Model.Covariate (D + 1))
    (hy : y ∉ unitCubeOpen (D + 1)) : localPairProduct p0 r0 h Au Av inner outer θ phase σu σv S b y = 0 := by
  simp [localPairProduct, blockProfile, hin y hy]

 theorem globalProduct_eq_sum (offset ell p0 r0 h Au Av : ℝ) (hell : 0 < ell)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σu σv S : GridPair D N → ℝ) (x : Model.Covariate (D + 1)) :
    globalDensity offset ell p0 r0 h outer θ phase x *
      globalProfile offset ell p0 r0 h Au inner outer θ phase σu S x *
      globalProfile offset ell p0 r0 h Av inner outer θ phase σv S x =
    ∑ b : GridBlock D N, localPairProduct p0 r0 h Au Av inner outer θ phase σu σv S b
      (gridCoords offset ell b x) := by
  by_cases hx : ∃ b : GridBlock D N, x ∈ gridBlockOpen offset ell b
  · obtain ⟨b, hb⟩ := hx
    rw [globalDensity_eq_local offset ell p0 r0 h hell outer hout θ phase b x hb,
      globalProfile_eq_local offset ell p0 r0 h Au hell inner outer hin hout θ phase σu S b x hb,
      globalProfile_eq_local offset ell p0 r0 h Av hell inner outer hin hout θ phase σv S b x hb]
    rw [Finset.sum_eq_single b]
    · rfl
    · intro a ha hab
      apply localPairProduct_zero p0 r0 h Au Av inner outer hin θ phase σu σv S a
      intro hxa
      exact Set.disjoint_left.mp (gridBlockOpen_pairwiseDisjoint D N offset ell hell (Ne.symm hab)) hb hxa
    · simp
  · rw [globalProfile_outside offset ell p0 r0 h Au inner outer hin θ phase σu S x (not_exists.mp hx)]
    simp only [mul_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    exact localPairProduct_zero p0 r0 h Au Av inner outer hin θ phase σu σv S b _ (not_exists.mp hx b)

 theorem localPairProduct_smooth (p0 r0 h Au Av : ℝ) (inner outer : Model.Covariate (D + 1) → ℝ)
    (hi : ContDiff ℝ ∞ inner) (ho : ContDiff ℝ ∞ outer)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (phase k)) (σu σv S : GridPair D N → ℝ) (b : GridBlock D N)
    (hne : ∀ y, blockDensity p0 r0 h (θ b.1) (phase b.1) outer (RoughRegime.Lower.sign b.2) y ≠ 0) :
    ContDiff ℝ ∞ (localPairProduct p0 r0 h Au Av inner outer θ phase σu σv S b) := by
  have hd := blockDensity_smooth p0 r0 h (θ b.1) (RoughRegime.Lower.sign b.2) (phase b.1) outer (hp b.1) ho
  exact (hd.mul (blockProfile_smooth Au _ _ inner _ hi hd hne)).mul
    (blockProfile_smooth Av _ _ inner _ hi hd hne)

 theorem globalProductTarget_integral (offset ell p0 r0 h Au Av : ℝ) (hell : 0 < ell)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (hi : ContDiff ℝ ∞ inner) (ho : ContDiff ℝ ∞ outer)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (phase k)) (σu σv S : GridPair D N → ℝ)
    (hne : ∀ b : GridBlock D N, ∀ y,
      blockDensity p0 r0 h (θ b.1) (phase b.1) outer (RoughRegime.Lower.sign b.2) y ≠ 0) :
    globalProductTarget offset ell p0 r0 h Au Av inner outer θ phase σu σv S =
      ell ^ (D + 1) * ∑ b : GridBlock D N,
        ∫ y, localPairProduct p0 r0 h Au Av inner outer θ phase σu σv S b y ∂Model.cubeVolume (D + 1) := by
  have heq : (fun x => globalDensity offset ell p0 r0 h outer θ phase x *
      globalProfile offset ell p0 r0 h Au inner outer θ phase σu S x *
      globalProfile offset ell p0 r0 h Av inner outer θ phase σv S x) =
      fun x => ∑ b : GridBlock D N, localPairProduct p0 r0 h Au Av inner outer θ phase σu σv S b
        (gridCoords offset ell b x) := funext (globalProduct_eq_sum offset ell p0 r0 h Au Av hell inner outer hin hout θ phase σu σv S)
  unfold globalProductTarget
  rw [heq, integral_finsetSum Finset.univ
    (f := fun b x => localPairProduct p0 r0 h Au Av inner outer θ phase σu σv S b (gridCoords offset ell b x)) (fun b _ =>
    continuous_cube_integrable _ ((localPairProduct_smooth p0 r0 h Au Av inner outer hi ho θ phase hp σu σv S b (hne b)).continuous.comp
      (gridCoords_smooth offset ell b).continuous))]
  simp_rw [grid_pull_integral_cube offset ell hell _ hoff hsize _
    (localPairProduct_zero p0 r0 h Au Av inner outer hin θ phase σu σv S _)]
  exact (Finset.mul_sum _ _ _).symm

end RoughRegime.LatticePriors
