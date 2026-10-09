module

public import RoughRegime.GlobalLatticeMass
public import RoughRegime.CubeTransport


@[expose] public section
/-! The closed geometric pair has exactly the same deterministic probability
mass as the sum of its two adjacent closed cells; their shared face is null. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open scoped ContDiff

 variable {D N : ℕ}

 theorem volume_coordinate_fiber_zero (d : ℕ) (q : Fin d) (c : ℝ) :
    (volume : Measure (Model.Covariate d)) {x | x q = c} = 0 := by
  have hnull := Measure.pi_eval_preimage_null (fun _ : Fin d => (volume : Measure ℝ))
    (i := q) (s := {c}) (by simp)
  have he := (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (((measurableSet_singleton c).preimage (measurable_pi_apply q)).nullMeasurableSet)
  simpa only [Set.preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff] using he.trans hnull

 theorem grid_pair_closed_aedisjoint (offset ell : ℝ) (hell : 0 < ell) (k : GridPair D N) :
    AEDisjoint volume (gridBlockClosed offset ell (k, false)) (gridBlockClosed offset ell (k, true)) := by
  change volume (gridBlockClosed offset ell (k, false) ∩ gridBlockClosed offset ell (k, true)) = 0
  apply measure_mono_null (t := {x : Model.Covariate (D + 1) |
    x 0 = offset + ell * (2 * k.1.val + 1 : ℕ)}) _
    (volume_coordinate_fiber_zero (D + 1) 0 _)
  intro x hx
  have ha := gridBlockClosed_coordinate_bounds offset ell (k, false) hell x hx.1 0
  have hb := gridBlockClosed_coordinate_bounds offset ell (k, true) hell x hx.2 0
  simp only [gridCell, Fin.cons_zero, Bool.toNat_false, Bool.toNat_true, add_zero,
    Nat.cast_add, Nat.cast_one, Set.mem_ofPred_eq] at ha hb ⊢
  linarith

 theorem gridBlockClosed_subset_cube (offset ell : ℝ) (b : GridBlock D N) (hell : 0 < ell)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1) :
    gridBlockClosed offset ell b ⊆ Model.cube (D + 1) := by
  intro x hx q
  have hb := gridBlockClosed_coordinate_bounds offset ell b hell x hx q
  have hc : (gridCell b q : ℝ) + 1 ≤ (2 * N : ℕ) := by exact_mod_cast gridCell_lt b q
  have hnonneg : 0 ≤ (gridCell b q : ℝ) := Nat.cast_nonneg _
  constructor <;> nlinarith

 theorem globalDensity_geometric_pair_mass (offset ell p0 r0 h : ℝ) (hell : 0 < ell)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1)
    (outer : Model.Covariate (D + 1) → ℝ) (ho : ContDiff ℝ ∞ outer)
    (hout : ∀ y, y ∉ unitCubeOpen (D + 1) → outer y = 0)
    (θ : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D + 1) → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (phase k)) (k : GridPair D N) :
    (∫ x in gridBlockClosed offset ell (k, false) ∪ gridBlockClosed offset ell (k, true),
      globalDensity offset ell p0 r0 h outer θ phase x) =
      2 * ell ^ (D + 1) * (p0 + (∫ y, outer y ∂Model.cubeVolume (D + 1)) * (r0 - p0)) := by
  have hi := continuous_cube_integrable (globalDensity offset ell p0 r0 h outer θ phase)
    (globalDensity_smooth offset ell p0 r0 h outer ho θ phase hp).continuous
  have hib (label : Bool) : IntegrableOn (globalDensity offset ell p0 r0 h outer θ phase)
      (gridBlockClosed offset ell (k, label)) volume :=
    (show IntegrableOn _ (Model.cube (D + 1)) volume from hi).mono_set (gridBlockClosed_subset_cube offset ell (k, label) hell hoff hsize)
  rw [setIntegral_union₀ (grid_pair_closed_aedisjoint offset ell hell k)
    (gridBlockClosed_measurable offset ell (k, true)).nullMeasurableSet (hib false) (hib true)]
  have he := globalDensity_pair_mass offset ell p0 r0 h hell outer ho hout θ phase hp k
  simpa only [Fintype.sum_bool, add_comm] using he

end RoughRegime.LatticePriors
