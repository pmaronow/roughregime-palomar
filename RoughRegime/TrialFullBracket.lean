module

public import RoughRegime.ApplicationTrialBrackets
public import RoughRegime.ProductFullBrackets
public import RoughRegime.ModelLowerConsequences


@[expose] public section
/-! Full source squared-CATE bracket, via the actual fair-coin reverse kernel. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.Trial

theorem squaredCATE_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    Model.LowerBracket (squaredCATE A) (modelClass A) A.bracketParameters := by
  apply Model.lowerBracket_kernel (reverseKernel A.d) (Products.quadraticTarget A)
    (squaredCATE A) (Products.quadraticClass A) (modelClass A) (reverseLaw_mem A)
    _ _ (Products.quadratic_bracket A hM hlo hhi hab).1
  intro P hP
  change squaredCATE A (reverseLaw A P) = Products.quadraticTarget A P
  rw [squaredCATE_eq A _ (reverseLaw_mem A P hP)]
  unfold quadraticTarget
  rw [forwardLaw_reverseLaw]

theorem squaredCATE_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    Model.Bracket (squaredCATE A) (modelClass A) A.bracketParameters (A.nu : ℝ) :=
  ⟨squaredCATE_lowerBracket A hM hlo hhi hab,
    squaredCATE_upperBracket A hM ((le_max_left _ _).trans hlo.le) hab⟩

end RoughRegime.Applications.Trial
