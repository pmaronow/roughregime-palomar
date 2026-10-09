module

public import RoughRegime.ApplicationProductClass
public import RoughRegime.ApplicationMAR
public import RoughRegime.ModelUpperConsequences
public import RoughRegime.HolderConstants


@[expose] public section
/-! The literal overlap-weighted-effect class, with a binary treatment,
outcome in [0,1], actual conditional moments, and both generic-model targets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false

abbrev Response := MAR.TreatmentResponse
def treatment : Response → ℝ := MAR.armIndicator true
def outcome (z : Response) : ℝ := z.2
theorem treatment_measurable : Measurable treatment := MAR.armIndicator_measurable true
theorem outcome_measurable : Measurable outcome := measurable_subtype_coe.comp measurable_snd
theorem treatment_range (z : Response) : treatment z∈Icc (0:ℝ) 1 := by
  unfold treatment MAR.armIndicator
  split_ifs <;> norm_num
theorem outcome_range (z : Response) : outcome z∈Icc (0:ℝ) 1 := z.2.property
theorem treatment_bound (z : Response) : |treatment z|≤1 := by
  rw [abs_of_nonneg (treatment_range z).1]; exact (treatment_range z).2
theorem outcome_bound (z : Response) : |outcome z|≤1 := by
  rw [abs_of_nonneg (outcome_range z).1]; exact (outcome_range z).2
theorem treatment_sq (z : Response) : treatment z^2=treatment z := by
  unfold treatment MAR.armIndicator
  split_ifs <;> norm_num

abbrev diagonalParameters (A : Model.Parameters) : Model.Parameters :=
  {A with β:=A.α,hβ:=A.hα}

structure Witness (A : Model.Parameters) (ε : ℝ)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) extends
    Products.Witness A treatment outcome P where
  overlap : ∀ᵐ x ∂Model.cubeVolume A.d, ε ≤ mU x ∧ mU x≤1-ε

def modelClass (A : Model.Parameters) (ε : ℝ) :
    Set (ProbabilityMeasure (Model.Covariate A.d×Response)) := {P | Nonempty (Witness A ε P)}

abbrev numeratorObservables (A : Model.Parameters) (hM : 1≤A.M0) :=
  Products.covarianceObservables A hM treatment outcome treatment_measurable outcome_measurable
    treatment_bound outcome_bound
abbrev denominatorObservables (A : Model.Parameters) (hM : 1≤A.M0) :=
  Products.covarianceObservables (diagonalParameters A) hM treatment treatment
    treatment_measurable treatment_measurable treatment_bound treatment_bound

def numerator (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d×Response)) : ℝ :=
  ∫ o,ConditionalExamples.conditionalCovariance (MeasurableSpace.comap Prod.fst inferInstance)
    (treatment∘Prod.snd) (outcome∘Prod.snd) (P:Measure (Model.Covariate d×Response)) o
    ∂(P:Measure (Model.Covariate d×Response))
def denominator (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d×Response)) : ℝ :=
  ∫ o,condVar (MeasurableSpace.comap Prod.fst inferInstance) (treatment∘Prod.snd)
    (P:Measure (Model.Covariate d×Response)) o ∂(P:Measure (Model.Covariate d×Response))
def effect (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d×Response)) : ℝ :=
  numerator d P/denominator d P

theorem numerator_target (A : Model.Parameters) (hM : 1≤A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) :
    Model.target A (numeratorObservables A hM) P=numerator A.d P :=
  Products.target_eq_conditional_covariance A hM _ _ _ _ _ _ P
theorem denominator_target (A : Model.Parameters) (hM : 1≤A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) :
    Model.target (diagonalParameters A) (denominatorObservables A hM) P=denominator A.d P :=
  Products.target_eq_conditional_variance (diagonalParameters A) hM _ _ _ P

def Witness.denominatorWitness (A : Model.Parameters) (ε : ℝ)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A ε P) :
    Products.Witness (diagonalParameters A) treatment treatment P where
  p:=W.p
  mU:=W.mU
  mV:=W.mU
  measurableP:=W.measurableP
  measurableU:=W.measurableU
  measurableV:=W.measurableU
  nonnegativeP:=W.nonnegativeP
  marginal:=W.marginal
  momentU:=W.momentU
  momentV:=W.momentU
  smoothU:=W.smoothU
  smoothV:=W.smoothU
  densityBounds:=W.densityBounds

theorem numerator_upperBracket (A : Model.Parameters) (ε : ℝ) (hM : 1≤A.M0) (hδ : A.δ≤1) :
    Model.UpperBracket (numerator A.d) (modelClass A ε) A.bracketParameters (A.nu:ℝ) := by
  apply Model.upperBracket_congr_target _ (Model.target A (numeratorObservables A hM))
    _ _ _ (fun P _ => (numerator_target A hM P).symm)
  apply Model.upperBracket_mono_class _ _ _ _ (Model.model_upperBracket A (numeratorObservables A hM))
  rintro P ⟨W⟩
  exact ⟨W.toWitness.toModel A (numeratorObservables A hM) rfl hδ P⟩

theorem denominator_upperBracket (A : Model.Parameters) (ε : ℝ) (hM : 1≤A.M0) (hδ : A.δ≤1) :
    Model.UpperBracket (denominator A.d) (modelClass A ε)
      (diagonalParameters A).bracketParameters ((diagonalParameters A).nu:ℝ) := by
  apply Model.upperBracket_congr_target _ (Model.target (diagonalParameters A) (denominatorObservables A hM))
    _ _ _ (fun P _ => (denominator_target A hM P).symm)
  apply Model.upperBracket_mono_class _ _ _ _ (Model.model_upperBracket (diagonalParameters A) (denominatorObservables A hM))
  rintro P ⟨W⟩
  exact ⟨(W.denominatorWitness A ε P).toModel (diagonalParameters A) (denominatorObservables A hM) rfl hδ P⟩

end RoughRegime.Applications.Overlap
