module

public import RoughRegime.PairedGrid
public import RoughRegime.UniformCube
public import RoughRegime.PairedTarget


@[expose] public section
/-! Actual globally glued lattice densities and profiles on the even grid. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open scoped BigOperators ContDiff

 variable {D N : ℕ}

 def unitCubeOpen (d : ℕ) : Set (Model.Covariate d) := {x | ∀ q, 0 < x q ∧ x q < 1}
 def pulledCutoff (offset ell : ℝ) (b : GridBlock D N) (cutoff : Model.Covariate (D + 1) → ℝ) :
    Model.Covariate (D + 1) → ℝ := cutoff ∘ gridCoords offset ell b

 theorem pulledCutoff_zero (offset ell : ℝ) (b : GridBlock D N)
    (cutoff : Model.Covariate (D + 1) → ℝ)
    (hc : ∀ y, y ∉ unitCubeOpen (D + 1) → cutoff y = 0)
    (x : Model.Covariate (D + 1)) (hx : x ∉ gridBlockOpen offset ell b) :
    pulledCutoff offset ell b cutoff x = 0 := hc _ hx

 theorem pulledCutoff_zero_of_other (offset ell : ℝ) (hell : 0 < ell) (a b : GridBlock D N)
    (hab : a ≠ b) (cutoff : Model.Covariate (D + 1) → ℝ)
    (hc : ∀ y, y ∉ unitCubeOpen (D + 1) → cutoff y = 0)
    (x : Model.Covariate (D + 1)) (hx : x ∈ gridBlockOpen offset ell a) :
    pulledCutoff offset ell b cutoff x = 0 := by
  apply pulledCutoff_zero offset ell b cutoff hc x
  intro hxb
  exact Set.disjoint_left.mp (gridBlockOpen_pairwiseDisjoint D N offset ell hell hab) hx hxb

 def globalDensity (offset ell p0 r0 h : ℝ)
    (outer : Model.Covariate (D + 1) → ℝ)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (x : Model.Covariate (D + 1)) : ℝ :=
  p0 + ∑ b : GridBlock D N,
    pulledCutoff offset ell b outer x *
      (blockOscillatingDensity r0 h (θ b.1) (phase b.1) (RoughRegime.Lower.sign b.2)
        (gridCoords offset ell b x) - p0)

 def globalNumerator (offset ell A : ℝ) (inner : Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (x : Model.Covariate (D + 1)) : ℝ :=
  ∑ b : GridBlock D N, A * σ b.1 * S b.1 * pulledCutoff offset ell b inner x

 def globalProfile (offset ell p0 r0 h A : ℝ)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (x : Model.Covariate (D + 1)) : ℝ :=
  globalNumerator offset ell A inner σ S x / globalDensity offset ell p0 r0 h outer θ phase x

 theorem globalDensity_eq_local (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (outer : Model.Covariate (D + 1) → ℝ)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (b : GridBlock D N) (x : Model.Covariate (D + 1)) (hx : x ∈ gridBlockOpen offset ell b) :
    globalDensity offset ell p0 r0 h outer θ phase x =
      blockDensity p0 r0 h (θ b.1) (phase b.1) outer (RoughRegime.Lower.sign b.2)
        (gridCoords offset ell b x) := by
  unfold globalDensity blockDensity
  congr 1
  rw [Finset.sum_eq_single b]
  · rfl
  · intro a ha hab
    rw [pulledCutoff_zero_of_other offset ell hell b a (Ne.symm hab) outer hout x hx, zero_mul]
  · simp

 theorem globalNumerator_eq_local (offset ell A : ℝ) (hell : 0 < ell)
    (inner : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (σ S : GridPair D N → ℝ) (b : GridBlock D N) (x : Model.Covariate (D + 1))
    (hx : x ∈ gridBlockOpen offset ell b) :
    globalNumerator offset ell A inner σ S x = A * σ b.1 * S b.1 * inner (gridCoords offset ell b x) := by
  unfold globalNumerator
  rw [Finset.sum_eq_single b]
  · rfl
  · intro a ha hab
    rw [pulledCutoff_zero_of_other offset ell hell b a (Ne.symm hab) inner hin x hx, mul_zero]
  · simp

 theorem globalDensity_outside (offset ell p0 r0 h : ℝ)
    (outer : Model.Covariate (D + 1) → ℝ)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (x : Model.Covariate (D + 1)) (hx : ∀ b : GridBlock D N, x ∉ gridBlockOpen offset ell b) :
    globalDensity offset ell p0 r0 h outer θ phase x = p0 := by
  unfold globalDensity
  have hz : ∀ b : GridBlock D N, pulledCutoff offset ell b outer x = 0 := fun b => pulledCutoff_zero offset ell b outer hout x (hx b)
  simp [hz]

 theorem globalNumerator_outside (offset ell A : ℝ)
    (inner : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (σ S : GridPair D N → ℝ) (x : Model.Covariate (D + 1)) (hx : ∀ b : GridBlock D N, x ∉ gridBlockOpen offset ell b) :
    globalNumerator offset ell A inner σ S x = 0 := by
  unfold globalNumerator
  have hz : ∀ b : GridBlock D N, pulledCutoff offset ell b inner x = 0 := fun b => pulledCutoff_zero offset ell b inner hin x (hx b)
  simp [hz]

 theorem globalDensity_bounds (offset ell p0 r0 h lo hi : ℝ) (hell : 0 < ell)
    (outer : Model.Covariate (D + 1) → ℝ)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (hout01 : ∀ y, 0 ≤ outer y ∧ outer y ≤ 1)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hp0 : lo ≤ p0 ∧ p0 ≤ hi) (hr : lo ≤ r0 - |h| ∧ r0 + |h| ≤ hi)
    (x : Model.Covariate (D + 1)) :
    lo ≤ globalDensity offset ell p0 r0 h outer θ phase x ∧
      globalDensity offset ell p0 r0 h outer θ phase x ≤ hi := by
  by_cases hx : ∃ b : GridBlock D N, x ∈ gridBlockOpen offset ell b
  · obtain ⟨b, hb⟩ := hx
    rw [globalDensity_eq_local offset ell p0 r0 h hell outer hout θ phase b x hb]
    apply blockDensity_bounds p0 r0 h _ _ lo hi _ _ _ hp0 hr hout01
    cases b.2 <;> norm_num [RoughRegime.Lower.sign]
  · rw [globalDensity_outside offset ell p0 r0 h outer hout θ phase x (not_exists.mp hx)]
    exact hp0

 theorem globalDensity_smooth (offset ell p0 r0 h : ℝ)
    (outer : Model.Covariate (D + 1) → ℝ) (ho : ContDiff ℝ ∞ outer)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hphase : ∀ k, ContDiff ℝ ∞ (phase k)) :
    ContDiff ℝ ∞ (globalDensity offset ell p0 r0 h outer θ phase) := by
  unfold globalDensity
  apply contDiff_const.add
  apply ContDiff.sum
  intro b hb
  apply (ho.comp (gridCoords_smooth offset ell b)).mul
  apply ContDiff.sub _ contDiff_const
  have hc := blockDensity_smooth (0 : ℝ) r0 h (θ b.1) (RoughRegime.Lower.sign b.2)
    (phase b.1) (fun _ => (1 : ℝ)) (hphase b.1) contDiff_const
  have heq : blockDensity 0 r0 h (θ b.1) (phase b.1) (fun _ => 1) (RoughRegime.Lower.sign b.2) =
      blockOscillatingDensity r0 h (θ b.1) (phase b.1) (RoughRegime.Lower.sign b.2) := by
    funext y
    simp [blockDensity]
  rw [heq] at hc
  exact hc.comp (gridCoords_smooth offset ell b)

 theorem globalNumerator_smooth (offset ell A : ℝ)
    (inner : Model.Covariate (D + 1) → ℝ) (hi : ContDiff ℝ ∞ inner) (σ S : GridPair D N → ℝ) :
    ContDiff ℝ ∞ (globalNumerator offset ell A inner σ S) := by
  unfold globalNumerator
  apply ContDiff.sum
  intro b hb
  exact contDiff_const.mul (hi.comp (gridCoords_smooth offset ell b))

 theorem globalProfile_smooth (offset ell p0 r0 h A : ℝ)
    (inner outer : Model.Covariate (D + 1) → ℝ) (hi : ContDiff ℝ ∞ inner) (ho : ContDiff ℝ ∞ outer)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hphase : ∀ k, ContDiff ℝ ∞ (phase k)) (σ S : GridPair D N → ℝ)
    (hp : ∀ x, globalDensity offset ell p0 r0 h outer θ phase x ≠ 0) :
    ContDiff ℝ ∞ (globalProfile offset ell p0 r0 h A inner outer θ phase σ S) :=
  (globalNumerator_smooth offset ell A inner hi σ S).div
    (globalDensity_smooth offset ell p0 r0 h outer ho θ phase hphase) hp

 theorem globalProfile_eq_local (offset ell p0 r0 h A : ℝ) (hell : 0 < ell)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (b : GridBlock D N) (x : Model.Covariate (D + 1))
    (hx : x ∈ gridBlockOpen offset ell b) :
    globalProfile offset ell p0 r0 h A inner outer θ phase σ S x =
      blockProfile A (σ b.1) (S b.1) inner
        (blockDensity p0 r0 h (θ b.1) (phase b.1) outer (RoughRegime.Lower.sign b.2))
        (gridCoords offset ell b x) := by
  unfold globalProfile blockProfile
  rw [globalNumerator_eq_local offset ell A hell inner hin σ S b x hx,
    globalDensity_eq_local offset ell p0 r0 h hell outer hout θ phase b x hx]

 theorem globalNumerator_abs_bound (offset ell A : ℝ) (hell : 0 < ell)
    (inner : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hi : ∀ y, |inner y| ≤ 1) (σ S : GridPair D N → ℝ)
    (hσ : ∀ k, |σ k| ≤ 1) (hS : ∀ k, |S k| ≤ 1) (x : Model.Covariate (D + 1)) :
    |globalNumerator offset ell A inner σ S x| ≤ |A| := by
  by_cases hx : ∃ b : GridBlock D N, x ∈ gridBlockOpen offset ell b
  · obtain ⟨b, hb⟩ := hx
    rw [globalNumerator_eq_local offset ell A hell inner hin σ S b x hb, abs_mul, abs_mul, abs_mul]
    have hprod := mul_le_mul (mul_le_mul (hσ b.1) (hS b.1) (abs_nonneg _) zero_le_one)
      (hi (gridCoords offset ell b x)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
    have hm := mul_le_mul_of_nonneg_left hprod (abs_nonneg A)
    convert hm using 1 <;> ring
  · rw [globalNumerator_outside offset ell A inner hin σ S x (not_exists.mp hx), abs_zero]
    exact abs_nonneg A

 theorem globalProfile_abs_bound (offset ell p0 r0 h A lo : ℝ) (hell : 0 < ell) (hlo : 0 < lo)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hi : ∀ y, |inner y| ≤ 1) (θ : GridPair D N → ℝ)
    (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (hσ : ∀ k, |σ k| ≤ 1) (hS : ∀ k, |S k| ≤ 1)
    (hp : ∀ x, lo ≤ globalDensity offset ell p0 r0 h outer θ phase x) (x : Model.Covariate (D + 1)) :
    |globalProfile offset ell p0 r0 h A inner outer θ phase σ S x| ≤ |A| / lo := by
  unfold globalProfile
  rw [abs_div, abs_of_pos (hlo.trans_le (hp x))]
  exact div_le_div₀ (abs_nonneg _) (globalNumerator_abs_bound offset ell A hell inner hin hi σ S hσ hS x) hlo (hp x)

 theorem globalProfile_outside (offset ell p0 r0 h A : ℝ)
    (inner outer : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (x : Model.Covariate (D + 1))
    (hx : ∀ b : GridBlock D N, x ∉ gridBlockOpen offset ell b) :
    globalProfile offset ell p0 r0 h A inner outer θ phase σ S x = 0 := by
  unfold globalProfile
  rw [globalNumerator_outside offset ell A inner hin σ S x hx, zero_div]

 def globalBlockPrior {ι : Type*} [Fintype ι] (μ : Measure (ι → ℤ)) (M : ℕ) (positive : Bool) :
    Measure (GridPair D N → ((ι → ℤ) × (ℝ × (Bool × Bool)))) :=
  Measure.pi (fun _ : GridPair D N => blockPrior μ M positive)

 instance globalBlockPrior_probability {ι : Type*} [Fintype ι] (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ]
    (M : ℕ) (positive : Bool) : IsProbabilityMeasure (globalBlockPrior (D := D) (N := N) μ M positive) := by
  unfold globalBlockPrior
  infer_instance

 theorem globalBlockPrior_independent {ι : Type*} [Fintype ι] (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ]
    (M : ℕ) (positive : Bool) :
    ProbabilityTheory.iIndepFun (fun k : GridPair D N => fun z => z k) (globalBlockPrior μ M positive) := by
  exact ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

 theorem globalDensity_eq_local_closed (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (outer : Model.Covariate (D + 1) → ℝ)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (b : GridBlock D N) (x : Model.Covariate (D + 1)) (hx : x ∈ gridBlockClosed offset ell b) :
    globalDensity offset ell p0 r0 h outer θ phase x =
      blockDensity p0 r0 h (θ b.1) (phase b.1) outer (RoughRegime.Lower.sign b.2)
        (gridCoords offset ell b x) := by
  by_cases hxb : x ∈ gridBlockOpen offset ell b
  · exact globalDensity_eq_local offset ell p0 r0 h hell outer hout θ phase b x hxb
  · have houtside : ∀ a : GridBlock D N, x ∉ gridBlockOpen offset ell a := by
      intro a ha
      have he := gridClosedOpen_unique offset ell hell b a x hx ha
      subst a
      exact hxb ha
    rw [globalDensity_outside offset ell p0 r0 h outer hout θ phase x houtside]
    symm
    apply blockDensity_outside
    exact hout _ hxb

end RoughRegime.LatticePriors
