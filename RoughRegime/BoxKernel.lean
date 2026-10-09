module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic


@[expose] public section
namespace RoughRegime.LatticeFourier

open MeasureTheory Set

noncomputable def boxKernel (a : ℝ) : ℝ → ℂ :=
  (Set.Icc (-a) a).indicator (fun _ : ℝ => (((2 * a)⁻¹ : ℝ) : ℂ))

theorem boxKernel_integrable (a : ℝ) : Integrable (boxKernel a) := by
  unfold boxKernel
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const measure_Icc_lt_top.ne (by finiteness)

end RoughRegime.LatticeFourier
