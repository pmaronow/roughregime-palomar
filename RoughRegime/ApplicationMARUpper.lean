module

public import RoughRegime.ModelUpperConsequences
public import RoughRegime.ApplicationMARClass


@[expose] public section
/-! The literal MAR conditional-ratio mean has the full main upper bracket on
the actual reciprocal-propensity class. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.Applications.MAR

def observedMean (d : ℕ)
    (P : ProbabilityMeasure (Model.Covariate d × Response)) : ℝ :=
  ∫ o, ((P : Measure (Model.Covariate d × Response))[
    observedOutcome ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o /
    ((P : Measure (Model.Covariate d × Response))[
    observed ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o
    ∂(P : Measure (Model.Covariate d × Response))

theorem generic_target_eq_observedMean (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) :
    Model.target A (observables A hM) P = observedMean A.d P := by
  have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace (Model.Covariate A.d × Response)) :=
    measurable_fst.comap_le
  simp only [Model.target,observables,Function.comp_def,integral_zero,zero_add,one_mul]
  change (∫ o, ((P : Measure (Model.Covariate A.d × Response))[
    fun _ => (1 : ℝ) | MeasurableSpace.comap Prod.fst inferInstance]) o * _ / _ ∂_) = _
  rw [condExp_const hm]
  simp only [Pi.one_apply,one_mul]
  rfl

theorem observedMean_eq_regression_mean (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P) :
    observedMean A.d P = ∫ o, W.b o.1 ∂(P : Measure (Model.Covariate A.d × Response)) := by
  rw [← generic_target_eq_observedMean A hM P]
  exact target_eq_mean A hM P W

/-- The MAR row's actual upper bracket, with both parametric and rough rates. -/
theorem mar_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) :
    Model.UpperBracket (observedMean A.d) (modelClass A) A.bracketParameters
      (A.nu : ℝ) := by
  apply Model.upperBracket_congr_target (observedMean A.d)
    (Model.target A (observables A hM)) (modelClass A) A.bracketParameters (A.nu : ℝ)
  · intro P _
    exact (generic_target_eq_observedMean A hM P).symm
  · exact Model.upperBracket_mono_class _ _ _ (modelClass_subset_generic A hM)
      (Model.model_upperBracket A (observables A hM))

end RoughRegime.Applications.MAR
