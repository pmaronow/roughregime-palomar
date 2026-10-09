module

public import RoughRegime.ApplicationTreatmentUpper
public import RoughRegime.ApplicationConditionalWald


@[expose] public section
/-! The Wald ratio on the actual bounded instrument/treatment/outcome law.
The defining class uses the two literal deterministic marginal experiments,
so its restrictions are actual inverse propensities and four regressions. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.Wald
abbrev Response := ConditionalWald.Response

def outcomeMap (d : ℕ) (o : Model.Covariate d × Response) : Model.Covariate d × MAR.TreatmentResponse :=
  (o.1,(o.2.1,o.2.2.2))

def treatmentMap (d : ℕ) (o : Model.Covariate d × Response) : Model.Covariate d × MAR.TreatmentResponse :=
  (o.1,(o.2.1,MAR.bitOutcome o.2.2.1))

theorem bitOutcome_measurable : Measurable MAR.bitOutcome := measurable_of_countable _
theorem outcomeMap_measurable (d : ℕ) : Measurable (outcomeMap d) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_snd.comp (measurable_snd.comp measurable_snd)))
theorem treatmentMap_measurable (d : ℕ) : Measurable (treatmentMap d) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (bitOutcome_measurable.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))))

def outcomeLaw (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) :
    ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse) := P.map (outcomeMap A.d)
def treatmentLaw (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) :
    ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse) := P.map (treatmentMap A.d)

def numerator (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) : ℝ :=
  MAR.ate A.d (outcomeLaw A P)
def denominator (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) : ℝ :=
  MAR.ate A.d (treatmentLaw A P)
def target (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) : ℝ :=
  numerator A P / denominator A P

def modelClass (A : Model.Parameters) (cW : ℝ) : Set (ProbabilityMeasure (Model.Observation A Response)) :=
  {P | outcomeLaw A P ∈ MAR.treatmentClass A A.β A.hβ ∧
    treatmentLaw A P ∈ MAR.treatmentClass A A.β A.hβ ∧ cW ≤ denominator A P}

theorem same_treatment_parameters (A : Model.Parameters) :
    MAR.treatmentParameters A A.β A.hβ = A := by
  simp only [MAR.treatmentParameters,min_self,MAR.parametersWithBeta]

theorem treatment_ate_range (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (hP : P ∈ MAR.treatmentClass A A.β A.hβ) : MAR.ate A.d P ∈ Icc (-1) 1 := by
  obtain ⟨⟨h0⟩,⟨h1⟩⟩ := hP
  have hr0 := MAR.armMean_range A false P h0
  have hr1 := MAR.armMean_range (MAR.parametersWithBeta A A.β A.hβ) true P h1
  change MAR.armMean A.d true P ∈ Icc 0 1 at hr1
  dsimp only [MAR.ate]
  constructor <;> linarith [hr0.1,hr0.2,hr1.1,hr1.2]

theorem numerator_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (cW : ℝ) :
    Model.UpperBracket (numerator A) (modelClass A cW) A.bracketParameters (A.nu : ℝ) := by
  have h := MAR.ate_upperBracket A hM A.β A.hβ
  rw [same_treatment_parameters] at h
  obtain ⟨hν,C,hC,n0,hn0,hupper⟩ := h
  refine ⟨hν,C,hC,n0,hn0,?_⟩
  intro n hn
  let K := Kernel.deterministic (outcomeMap A.d) (outcomeMap_measurable A.d)
  have hK : ∀ P, Model.kernelLaw K P = outcomeLaw A P := by
    intro P
    apply Subtype.ext
    exact Measure.deterministic_comp_eq_map (outcomeMap_measurable A.d)
  exact ((Model.kernel_reduction n K (numerator A) (MAR.ate A.d) (modelClass A cW)
    (MAR.treatmentClass A A.β A.hβ)
    (by intro P hP; rw [hK]; exact hP.1)
    (by intro P _; rw [hK]; rfl) 0).2).trans (hupper n hn)

theorem denominator_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (cW : ℝ) :
    Model.UpperBracket (denominator A) (modelClass A cW) A.bracketParameters (A.nu : ℝ) := by
  have h := MAR.ate_upperBracket A hM A.β A.hβ
  rw [same_treatment_parameters] at h
  obtain ⟨hν,C,hC,n0,hn0,hupper⟩ := h
  refine ⟨hν,C,hC,n0,hn0,?_⟩
  intro n hn
  let K := Kernel.deterministic (treatmentMap A.d) (treatmentMap_measurable A.d)
  have hK : ∀ P, Model.kernelLaw K P = treatmentLaw A P := by
    intro P
    apply Subtype.ext
    exact Measure.deterministic_comp_eq_map (treatmentMap_measurable A.d)
  exact ((Model.kernel_reduction n K (denominator A) (MAR.ate A.d) (modelClass A cW)
    (MAR.treatmentClass A A.β A.hβ)
    (by intro P hP; rw [hK]; exact hP.2.1)
    (by intro P _; rw [hK]; rfl) 0).2).trans (hupper n hn)

theorem wald_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (cW : ℝ)
    (hc : 0 < cW) (hc1 : cW ≤ 1) :
    Model.UpperBracket (target A) (modelClass A cW) A.bracketParameters (A.nu : ℝ) := by
  apply Model.ratio_upperBracket _ _ _ _ _ (numerator_upperBracket A hM cW)
    (denominator_upperBracket A hM cW) 1 cW 1 zero_le_one hc hc1
  · intro P hP
    exact treatment_ate_range A (outcomeLaw A P) hP.1
  · intro P hP
    exact ⟨hP.2.2,(treatment_ate_range A (treatmentLaw A P) hP.2.1).2⟩

end RoughRegime.Applications.Wald
