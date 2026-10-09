module

public import RoughRegime.ProductDerivedSmoothLower
public import RoughRegime.TrialVarianceBrackets
public import RoughRegime.TrialFullBracket


@[expose] public section
/-! Both original trial targets retain the full lower probability clause
when the actual design density is C-infinity. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.Trial

theorem smooth_squaredCATE_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) :
    Model.Bracket (squaredCATE A) (modelClass A ∩ Model.smoothDensityClass A.d Response)
      A.bracketParameters (A.nu : ℝ) := by
  constructor
  · apply Model.lowerBracket_kernel (reverseKernel A.d) (Products.quadraticTarget A) _
      (Products.quadraticClass A ∩ Model.smoothDensityClass A.d Products.BoundedResponse)
      (modelClass A ∩ Model.smoothDensityClass A.d Response) _ _ _
      (Products.smooth_quadratic_bracket A hM hlo hhi hab).1
    · rintro P ⟨hP,hs⟩
      exact ⟨reverseLaw_mem A P hP,reverseLaw_mem_smoothDensityClass A P hs⟩
    · rintro P ⟨hP,_hs⟩
      change squaredCATE A (reverseLaw A P)=Products.quadraticTarget A P
      rw [squaredCATE_eq A _ (reverseLaw_mem A P hP)]
      unfold quadraticTarget
      rw [forwardLaw_reverseLaw]
  · exact Model.upperBracket_mono_class _ _ _ Set.inter_subset_left
      (squaredCATE_upperBracket A hM ((le_max_left _ _).trans hlo.le) hab)

theorem smooth_cateVariance_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) :
    Model.Bracket (cateVariance A) (modelClass A ∩ Model.smoothDensityClass A.d Response)
      A.bracketParameters (A.nu : ℝ) := by
  constructor
  · apply Model.lowerBracket_kernel (reverseKernel A.d) (Products.explainedTarget A) _
      (Products.quadraticClass A ∩ Model.smoothDensityClass A.d Products.BoundedResponse)
      (modelClass A ∩ Model.smoothDensityClass A.d Response) _ _ _
      (Products.smooth_explained_bracket A hM hlo hhi hab).1
    · rintro P ⟨hP,hs⟩
      exact ⟨reverseLaw_mem A P hP,reverseLaw_mem_smoothDensityClass A P hs⟩
    · intro P hP
      change cateVariance A (reverseLaw A P)=Products.explainedTarget A P
      rw [cateVariance_eq A _ (reverseLaw_mem A P hP.1),forwardLaw_reverseLaw]
  · exact Model.upperBracket_mono_class _ _ _ Set.inter_subset_left
      (cateVariance_upperBracket A hM ((le_max_left _ _).trans hlo.le) hab)

end RoughRegime.Applications.Trial
