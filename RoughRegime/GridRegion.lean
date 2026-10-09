module

public import RoughRegime.GridIntegral


@[expose] public section
/-! The actual global cube containing all B paired blocks has the expected
Lebesgue volume, independent of the block subdivision count. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set

 def gridRegion (d N : ℕ) (offset ell : ℝ) : Set (Model.Covariate d) :=
  {x | ∀ q, offset ≤ x q ∧ x q ≤ offset + ell * (2 * N : ℕ)}

 theorem gridRegion_volume (d N : ℕ) (offset ell : ℝ) (hell : 0 ≤ ell) :
    volume (gridRegion d N offset ell) = ENNReal.ofReal ((ell * (2 * N : ℕ)) ^ d) := by
  have heq : gridRegion d N offset ell = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹'
      pi univ (fun _ => Icc offset (offset + ell * (2 * N : ℕ))) := by
    ext x
    simp only [gridRegion, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, true_implies, mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet]
  rw [volume_pi_pi]
  simp only [Real.volume_Icc]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

 theorem gridRegion_subset_cube (d N : ℕ) (offset ell : ℝ)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1) :
    gridRegion d N offset ell ⊆ Model.cube d := by
  intro x hx q
  exact ⟨hoff.trans (hx q).1, (hx q).2.trans hsize⟩

 theorem gridBlockOpen_subset_region {D N : ℕ} (offset ell : ℝ) (hell : 0 < ell) (b : GridBlock D N) :
    gridBlockOpen offset ell b ⊆ gridRegion (D + 1) N offset ell := by
  intro x hx q
  have hh := (gridBlockOpen_iff offset ell b hell x).mp hx q
  have hc : (gridCell b q : ℝ) + 1 ≤ (2 * N : ℕ) := by exact_mod_cast gridCell_lt b q
  constructor
  · nlinarith [(Nat.cast_nonneg (gridCell b q) : (0 : ℝ) ≤ gridCell b q)]
  · nlinarith

 theorem globalDensity_outside_region {D N : ℕ} (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (outer : Model.Covariate (D + 1) → ℝ) (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (x : Model.Covariate (D + 1)) (hx : x ∉ gridRegion (D + 1) N offset ell) :
    globalDensity offset ell p0 r0 h outer θ phase x = p0 := by
  apply globalDensity_outside offset ell p0 r0 h outer hout θ phase x
  intro b hb
  exact hx (gridBlockOpen_subset_region offset ell hell b hb)

 theorem globalProfile_outside_region {D N : ℕ} (offset ell p0 r0 h A : ℝ) (hell : 0 < ell)
    (inner outer : Model.Covariate (D + 1) → ℝ) (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (x : Model.Covariate (D + 1)) (hx : x ∉ gridRegion (D + 1) N offset ell) :
    globalProfile offset ell p0 r0 h A inner outer θ phase σ S x = 0 := by
  apply globalProfile_outside offset ell p0 r0 h A inner outer hin θ phase σ S x
  intro b hb
  exact hx (gridBlockOpen_subset_region offset ell hell b hb)

end RoughRegime.LatticePriors
