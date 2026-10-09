module

public import RoughRegime.UniformCube
public import RoughRegime.DyadicTensor


@[expose] public section
/-! The exact transport between Euclidean unit-cube Lebesgue measure and the
coordinate product unit-cube law used in lattice Fourier calculations. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set

 theorem cubeVolume_ofLp_preserving (d : ℕ) :
    MeasurePreserving (@WithLp.ofLp 2 (Fin d → ℝ)) (Model.cubeVolume d) (DyadicDigits.cubeUniform d) := by
  have h := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc (a := (0 : ℝ)) (b := 1)))
  rw [← Model.cube_eq_preimage d] at h
  change MeasurePreserving _ (Model.cubeVolume d)
    ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict (pi univ (fun _ => Icc (0 : ℝ) 1))) at h
  rw [Measure.restrict_pi_pi] at h
  exact h

 theorem cubeVolume_integral_transport (d : ℕ) (f : Model.Covariate d → ℝ) :
    (∫ x, f x ∂Model.cubeVolume d) =
      ∫ y, f (WithLp.toLp 2 y) ∂DyadicDigits.cubeUniform d := by
  have hi := (cubeVolume_ofLp_preserving d).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).toMeasurableEquiv.measurableEmbedding
    (fun y => f (WithLp.toLp 2 y))
  simpa using hi

end RoughRegime.LatticePriors
