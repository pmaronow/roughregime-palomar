module

public import RoughRegime.TreatmentSmoothLower
public import RoughRegime.ApplicationWaldBracket


@[expose] public section
/-! The actual Wald-ratio bracket also holds on the subclass with a globally
smooth covariate density, through the covariate-preserving A=Z embedding. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.Wald

theorem smooth_wald_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (cW : ℝ) (hc : 0<cW) (hc1 : cW≤1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.Bracket (target A) (modelClass A cW ∩ Model.smoothDensityClass A.d Response)
      A.bracketParameters (A.nu : ℝ) := by
  have hl := MAR.smooth_ate_lowerBracket A hM A.β A.hβ hlo hhi hH
  rw [same_treatment_parameters] at hl
  let K := Kernel.deterministic (embed A.d) (embed_measurable A.d)
  have hK : ∀P,Model.kernelLaw K P=embedLaw A P := by
    intro P
    apply Subtype.ext
    exact Measure.deterministic_comp_eq_map (embed_measurable A.d)
  constructor
  · apply Model.lowerBracket_kernel K _ _ _ _ _ _ _ hl
    · rintro P ⟨hP,hs⟩
      rw [hK]
      exact ⟨embedLaw_mem A cW hc1 (by linarith) P hP,embedLaw_mem_smoothDensityClass A P hs⟩
    · rintro P ⟨hP,_hs⟩
      rw [hK]
      exact embedLaw_target A (by linarith) P hP
  · exact Model.upperBracket_mono_class _ _ _ Set.inter_subset_left (wald_upperBracket A hM cW hc hc1)

end RoughRegime.Applications.Wald
