module

public import RoughRegime.MARSmoothLower
public import RoughRegime.ApplicationConditionalWaldEmbedding


@[expose] public section
/-! The actual average conditional Wald bracket persists with an actual
C-infinity design density under the genuine balanced-instrument kernel. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.ConditionalWald

theorem smooth_conditionalWald_bracket (A : Model.Parameters) (hM : 2≤A.M0)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.Bracket (target A.d) (modelClass A ∩ Model.smoothDensityClass A.d Response)
      A.bracketParameters (A.nu : ℝ) := by
  have : IsMarkovKernel (augmentationKernel A.d) := augmentationKernel_markov A.d
  constructor
  · apply Model.lowerBracket_kernel (augmentationKernel A.d) _ _ _ _ _ _ _
      (MAR.smooth_mar_lowerBracket A (by linarith) hlo hhi hH)
    · rintro P ⟨hP,hs⟩
      exact ⟨augmentation_mem_class A P hP,augmentationLaw_mem_smoothDensityClass A P hs⟩
    · rintro P ⟨⟨W⟩,_hs⟩
      exact augmentation_target_eq A hM P W
  · exact Model.upperBracket_mono_class _ _ _ Set.inter_subset_left (conditionalWald_upperBracket A hM)

end RoughRegime.Applications.ConditionalWald
