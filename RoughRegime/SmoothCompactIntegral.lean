module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Set


@[expose] public section
open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace RoughRegime.Calculus

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
theorem contDiff_partial_fderiv (F : E → ℝ → G)
    (hf : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => fderiv ℝ (fun x => F x p.2) p.1) := by
  have hswap : ContDiff ℝ ∞ (fun p : ℝ × E => F p.2 p.1) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst)
  have hder : ContDiff ℝ ∞ (fun p : ℝ × E => fderiv ℝ (fun x => F x p.1) p.2) := by
    apply ContDiff.fderiv (n := ∞) (m := ∞) _ contDiff_snd (by simp)
    exact hswap.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hder.comp (contDiff_snd.prodMk contDiff_fst)

/-- A joint smooth function may be differentiated under a compact real
integration domain. The required common domination is obtained from actual
compactness of a neighborhood times the integration domain. -/
theorem hasFDerivAt_compactIntegral (F : E → ℝ → G)
    (hf : ContDiff ℝ ∞ (Function.uncurry F)) (s : Set ℝ) (hs : IsCompact s) (x0 : E) :
    HasFDerivAt (fun x => ∫ t in s, F x t)
      (∫ t in s, fderiv ℝ (fun x => F x t) x0) x0 := by
  let F' : E → ℝ → E →L[ℝ] G := fun x t => fderiv ℝ (fun y => F y t) x
  have hF' := contDiff_partial_fderiv F hf
  obtain ⟨U, hUc, hUn⟩ := exists_compact_mem_nhds x0
  have hcont : Continuous (fun p : E × ℝ => ‖F' p.1 p.2‖) := hF'.continuous.norm
  obtain ⟨B, hB⟩ := (hUc.prod hs).bddAbove_image hcont.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict s)
    (F' := F') (bound := fun _ => B) hUn
  · exact Eventually.of_forall fun x =>
      (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hs
  · exact (hF'.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict hs.measurableSet] with t ht
    intro x hx
    exact hB ⟨(x,t), ⟨hx,ht⟩, rfl⟩
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards [] with t
    intro x _
    exact ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x).hasFDerivAt

theorem contDiff_compactIntegral_nat (n : ℕ) (F : E → ℝ → G)
    (hf : ContDiff ℝ ∞ (Function.uncurry F)) (s : Set ℝ) (hs : IsCompact s) :
    ContDiff ℝ n (fun x => ∫ t in s, F x t) := by
  induction n generalizing G with
  | zero =>
    exact contDiff_zero.mpr (continuous_parametric_integral_of_continuous hf.continuous hs)
  | succ n ih =>
    rw [show (n + 1 : ℕ) = Nat.succ n from rfl]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ t in s, fderiv ℝ (fun y => F y t) x, ?_, ?_⟩
    · exact ih (fun x t => fderiv ℝ (fun y => F y t) x) (contDiff_partial_fderiv F hf)
    · intro x
      exact hasFDerivAt_compactIntegral F hf s hs x

theorem contDiff_compactIntegral (F : E → ℝ → G)
    (hf : ContDiff ℝ ∞ (Function.uncurry F)) (s : Set ℝ) (hs : IsCompact s) :
    ContDiff ℝ ∞ (fun x => ∫ t in s, F x t) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  exact contDiff_compactIntegral_nat n F hf s hs

end RoughRegime.Calculus
