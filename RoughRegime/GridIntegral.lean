module

public import RoughRegime.GlobalLattice


@[expose] public section
/-! Actual Lebesgue Jacobians of the block coordinate maps. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set

 variable {D N : ℕ}

 theorem integral_inverse_smul (ell : ℝ) (hell : 0 < ell)
    (f : Model.Covariate (D + 1) → ℝ) :
    (∫ x, f (ell⁻¹ • x)) = ell ^ (D + 1) * ∫ y, f y := by
  let u : ℝˣ := Units.mk0 (ell⁻¹) (inv_ne_zero hell.ne')
  have he : MeasurableEmbedding (fun x : Model.Covariate (D + 1) => ell⁻¹ • x) := by
    change MeasurableEmbedding ((Homeomorph.smul (α := Model.Covariate (D + 1)) u).toMeasurableEquiv : _ → _)
    exact (Homeomorph.smul (α := Model.Covariate (D + 1)) u).toMeasurableEquiv.measurableEmbedding
  have hi := he.integral_map (μ := (volume : Measure (Model.Covariate (D + 1)))) f
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hell.ne'), integral_smul_measure] at hi
  have hconst : (ENNReal.ofReal |((ell⁻¹) ^ Module.finrank ℝ (Model.Covariate (D + 1)))⁻¹|).toReal = ell ^ (D + 1) := by
    simp [Model.Covariate, inv_pow, abs_of_pos (pow_pos hell _), ENNReal.toReal_ofReal (pow_nonneg hell.le _)]
  rw [hconst, smul_eq_mul] at hi
  exact hi.symm

 theorem gridCoords_integral (offset ell : ℝ) (hell : 0 < ell) (b : GridBlock D N)
    (f : Model.Covariate (D + 1) → ℝ) :
    (∫ x, f (gridCoords offset ell b x)) = ell ^ (D + 1) * ∫ y, f y := by
  unfold gridCoords
  rw [integral_sub_right_eq_self (fun x => f (ell⁻¹ • x)) (gridOrigin offset ell b)]
  exact integral_inverse_smul ell hell f

 theorem grid_pull_integral_cube (offset ell : ℝ) (hell : 0 < ell) (b : GridBlock D N)
    (hoff : 0 ≤ offset) (hsize : offset + ell * (2 * N : ℕ) ≤ 1)
    (f : Model.Covariate (D + 1) → ℝ)
    (hf : ∀ y, y ∉ unitCubeOpen (D + 1) → f y = 0) :
    (∫ x, f (gridCoords offset ell b x) ∂Model.cubeVolume (D + 1)) =
      ell ^ (D + 1) * ∫ y, f y ∂Model.cubeVolume (D + 1) := by
  have hlocal : ∀ y, y ∉ Model.cube (D + 1) → f y = 0 := by
    intro y hy
    apply hf y
    intro hh
    apply hy
    intro q
    exact ⟨(hh q).1.le, (hh q).2.le⟩
  have hglobal : ∀ x, x ∉ Model.cube (D + 1) → f (gridCoords offset ell b x) = 0 := by
    intro x hx
    apply hf _
    intro hh
    apply hx
    exact gridBlockOpen_subset_cube offset ell b hell hoff hsize hh
  unfold Model.cubeVolume
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hglobal,
    setIntegral_eq_integral_of_forall_compl_eq_zero hlocal]
  exact gridCoords_integral offset ell hell b f

 theorem gridBlockClosed_measurable (offset ell : ℝ) (b : GridBlock D N) :
    MeasurableSet (gridBlockClosed offset ell b) :=
  (Model.measurableSet_cube (D + 1)).preimage (gridCoords_smooth offset ell b).continuous.measurable

 theorem grid_block_integral (offset ell : ℝ) (hell : 0 < ell) (b : GridBlock D N)
    (f : Model.Covariate (D + 1) → ℝ) :
    (∫ x in gridBlockClosed offset ell b, f (gridCoords offset ell b x)) =
      ell ^ (D + 1) * ∫ y, f y ∂Model.cubeVolume (D + 1) := by
  have heq : (gridBlockClosed offset ell b).indicator (fun x => f (gridCoords offset ell b x)) =
      fun x => (Model.cube (D + 1)).indicator f (gridCoords offset ell b x) := by
    funext x
    by_cases hx : x ∈ gridBlockClosed offset ell b
    · have hy : gridCoords offset ell b x ∈ Model.cube (D + 1) := hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · have hy : gridCoords offset ell b x ∉ Model.cube (D + 1) := hx
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  rw [← integral_indicator (gridBlockClosed_measurable offset ell b), heq,
    gridCoords_integral offset ell hell b, integral_indicator (Model.measurableSet_cube _)]
  rfl

end RoughRegime.LatticePriors
