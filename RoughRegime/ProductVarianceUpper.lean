module

public import RoughRegime.ProductMoments
public import RoughRegime.SquareBracket


@[expose] public section
/-! Literal explained variance and coefficient of determination, with actual
bounded-response estimators and a positive response-variance class. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.Products
set_option maxHeartbeats 800000

def determinationTarget (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  explainedTarget A P / responseVariance A P

def positiveVarianceClass (A : Model.Parameters) (vmin : ℝ) :
    Set (ProbabilityMeasure (Model.Observation A BoundedResponse)) :=
  {P | P ∈ quadraticClass A ∧ vmin ≤ responseVariance A P}

theorem responseMean_upperBracket (A : Model.Parameters) :
    Model.UpperBracket (responseMean A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) :=
  Model.observableMean_upperBracket (fun o : Model.Observation A BoundedResponse => (o.2 : ℝ))
    (measurable_subtype_coe.comp measurable_snd) 1 zero_le_one
    (fun o => response_bound o.2) _ _ _ (by exact_mod_cast A.nu_ge_two)

theorem responseSecondMoment_upperBracket (A : Model.Parameters) :
    Model.UpperBracket (responseSecondMoment A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) := by
  apply Model.observableMean_upperBracket (fun o : Model.Observation A BoundedResponse => (o.2 : ℝ)^2)
    ((measurable_subtype_coe.comp measurable_snd).pow_const 2) 1 zero_le_one
    (fun o => ?_) _ _ _ (by exact_mod_cast A.nu_ge_two)
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := o.2.property
  nlinarith only [h.1,h.2]

theorem responseMeanSquare_upperBracket (A : Model.Parameters) :
    Model.UpperBracket (fun P => (responseMean A P)^2) (quadraticClass A)
      A.bracketParameters (A.nu : ℝ) :=
  Model.square_upperBracket _ _ _ _ (responseMean_upperBracket A) 1 zero_le_one
    (fun P _ => abs_le.mpr (responseMean_range A P))

theorem responseVariance_upperBracket (A : Model.Parameters) :
    Model.UpperBracket (responseVariance A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) :=
  Model.same_upperBracket_difference _ _ _ _ _ _ (responseSecondMoment_upperBracket A)
    (responseMeanSquare_upperBracket A) (fun P _ => responseVariance_identity A P)

theorem explained_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1) :
    Model.UpperBracket (explainedTarget A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) :=
  Model.same_upperBracket_difference _ _ _ _ _ _ (quadratic_upperBracket A hM hd)
    (responseMeanSquare_upperBracket A) (fun P _ => explainedTarget_identity A P)

theorem determination_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1)
    (vmin : ℝ) (hv : 0 < vmin) (hv1 : vmin ≤ 1) :
    Model.UpperBracket (determinationTarget A) (positiveVarianceClass A vmin)
      A.bracketParameters (A.nu : ℝ) := by
  apply Model.ratio_upperBracket _ _ _ _ _
    (Model.upperBracket_mono_class _ _ _ (fun _ h => h.1) (explained_upperBracket A hM hd))
    (Model.upperBracket_mono_class _ _ _ (fun _ h => h.1) (responseVariance_upperBracket A))
    1 vmin 1 zero_le_one hv hv1
  · intro P _
    exact ⟨by linarith [(explainedTarget_range A P).1],(explainedTarget_range A P).2⟩
  · intro P hP
    exact ⟨hP.2,(responseVariance_range A P).2⟩

end RoughRegime.Applications.Products
