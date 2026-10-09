module

public import RoughRegime.JetComposition
public import Mathlib.Analysis.Calculus.ContDiff.Comp


@[expose] public section
/-! Smoothness of genuine partial higher derivatives in all parameters. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Calculus
variable {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Higher derivatives in the second variable retain smooth dependence on the
first variable, with no formal-jet equality supplied as a hypothesis. -/
theorem contDiffAt_parametric_iteratedFDeriv
    (f : P → E → G) (p : P) (x : E)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (p, x)) (n : ℕ) :
    ContDiffAt ℝ ∞ (fun y : P × E => iteratedFDeriv ℝ n (f y.1) y.2) (p, x) := by
  induction n with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
    exact hf.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E G).symm : G →L[ℝ] E [×0]→L[ℝ] G)
  | succ n ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def]
    have hpartial : ContDiffAt ℝ ∞
        (fun y : P × E => fderiv ℝ (fun z => iteratedFDeriv ℝ n (f y.1) z) y.2) (p, x) := by
      apply ContDiffAt.fderiv (n := ∞) _ contDiffAt_snd (by simp)
      exact ih.comp ((p, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact hpartial.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) G).symm :
        (E →L[ℝ] E [×n]→L[ℝ] G) →L[ℝ] E [×(n + 1)]→L[ℝ] G)

end RoughRegime.Calculus
