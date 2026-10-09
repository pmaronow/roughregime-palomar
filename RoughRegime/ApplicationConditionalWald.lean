module

public import RoughRegime.ModelUpperConsequences
public import RoughRegime.ApplicationMARClass


@[expose] public section
/-! The average conditional Wald ratio with the paper's actual instrument,
treatment and bounded outcome response, and its generic-model upper bracket. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.ConditionalWald

abbrev Response := Bool × Bool × MAR.Outcome

def bit (b : Bool) : ℝ := if b then 1 else 0
def instrument (z : Response) : ℝ := bit z.1
def treatment (z : Response) : ℝ := bit z.2.1
def outcome (z : Response) : ℝ := z.2.2
def treatmentScore (z : Response) : ℝ := 2*treatment z
def outcomeScore (z : Response) : ℝ := 2*(2*instrument z-1)*outcome z

theorem bit_measurable : Measurable bit := measurable_of_countable _
theorem instrument_measurable : Measurable instrument := bit_measurable.comp measurable_fst
theorem treatment_measurable : Measurable treatment :=
  bit_measurable.comp (measurable_fst.comp measurable_snd)
theorem outcome_measurable : Measurable outcome :=
  measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
theorem treatmentScore_measurable : Measurable treatmentScore :=
  measurable_const.mul treatment_measurable
theorem outcomeScore_measurable : Measurable outcomeScore :=
  measurable_const.mul ((measurable_const.mul instrument_measurable).sub measurable_const) |>.mul
    outcome_measurable

theorem bit_range (b : Bool) : bit b ∈ Icc (0:ℝ) 1 := by cases b <;> norm_num [bit]
theorem instrument_sign_abs (z : Response) : |2*instrument z-1|=1 := by
  cases h : z.1 <;> norm_num [instrument,bit,h]

def observables (A : Model.Parameters) (hM : 2 ≤ A.M0) : Model.Observables Response A where
  D := treatmentScore
  U _ := 1
  V := outcomeScore
  W _ := 0
  lam := 1
  hlam := one_ne_zero
  measurableD := treatmentScore_measurable
  measurableU := measurable_const
  measurableV := outcomeScore_measurable
  measurableW := measurable_const
  boundD z := by
    have ht := bit_range z.2.1
    dsimp [treatmentScore,treatment]
    constructor <;> nlinarith [ht.1,ht.2]
  boundU _ := by simp only [abs_one]; linarith
  boundV z := by
    dsimp [outcomeScore]
    rw [abs_mul,abs_mul,instrument_sign_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    dsimp [outcome]
    rw [abs_of_nonneg z.2.2.property.1]
    nlinarith [z.2.2.property.2]
  boundW := ⟨0,le_rfl,fun _ => by simp⟩

/-- Conditional versions of the actual design density, first stage and Wald
regression. Instrument balance and one-sided treatment are part of the class. -/
structure Witness (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) where
  p : Model.Covariate A.d → ℝ
  q : Model.Covariate A.d → ℝ
  b : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  measurableQ : Measurable q
  measurableB : Measurable b
  nonnegativeP : 0≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P:Measure (Model.Covariate A.d × Response)).map Prod.fst=
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  instrumentHalf : (P:Measure (Model.Covariate A.d × Response))[
    instrument∘Prod.snd | Model.covariateInformation A Response] =ᵐ[
      (P:Measure (Model.Covariate A.d × Response))] fun _ => (1/2:ℝ)
  oneSided : ∀ᵐ o ∂(P:Measure (Model.Covariate A.d × Response)),
    treatment o.2 ≤ instrument o.2
  momentD : (P:Measure (Model.Covariate A.d × Response))[
    treatmentScore∘Prod.snd | Model.covariateInformation A Response] =ᵐ[
      (P:Measure (Model.Covariate A.d × Response))] q∘Prod.fst
  momentV : (P:Measure (Model.Covariate A.d × Response))[
    outcomeScore∘Prod.snd | Model.covariateInformation A Response] =ᵐ[
      (P:Measure (Model.Covariate A.d × Response))] fun o => q o.1*b o.1
  overlap : ∀ᵐ x ∂Model.cubeVolume A.d, A.δ≤q x ∧ q x≤1-A.δ
  smoothInverse : (fun x => (q x)⁻¹)∈Model.holderBall A.α A.H
  smoothB : b∈Model.holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d, A.gminus≤q x*p x ∧ q x*p x≤A.gplus

def modelClass (A : Model.Parameters) : Set (ProbabilityMeasure (Model.Covariate A.d × Response)) :=
  {P | Nonempty (Witness A P)}

def Witness.toModel (A : Model.Parameters) (hM : 2≤A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P) :
    Model.ModelWitness A (observables A hM) P where
  p := W.p
  w := W.q
  a x := (W.q x)⁻¹
  b := W.b
  measurableP := W.measurableP
  measurableW := W.measurableQ
  measurableA := W.measurableQ.inv
  measurableB := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentD := W.momentD
  momentU := by
    have hm : Model.covariateInformation A Response≤
        (inferInstance:MeasurableSpace (Model.Covariate A.d × Response)) := measurable_fst.comap_le
    have hw : ∀ᵐ o ∂(P:Measure (Model.Covariate A.d × Response)), A.δ≤W.q o.1 := by
      apply ae_of_ae_map (f:=Prod.fst) (p:=fun x => A.δ≤W.q x) measurable_fst.aemeasurable
      rw [W.marginal]
      exact (W.overlap.mono (fun x hx => hx.1)).filter_mono
        (withDensity_absolutelyContinuous _ _).ae_le
    change (P:Measure (Model.Covariate A.d × Response))[
      fun _ => (1:ℝ) | Model.covariateInformation A Response] =ᵐ[_]
      fun o => W.q o.1*(W.q o.1)⁻¹
    rw [condExp_const hm]
    filter_upwards [hw] with o ho
    exact (mul_inv_cancel₀ (ne_of_gt (A.hδ.trans_le ho))).symm
  momentV := W.momentV
  overlap := W.overlap.mono (fun x hx => hx.1)
  smoothA := W.smoothInverse
  smoothB := W.smoothB
  densityBounds := W.densityBounds

theorem modelClass_subset_generic (A : Model.Parameters) (hM : 2≤A.M0) :
    modelClass A⊆Model.modelClass A (observables A hM) := by
  rintro P ⟨W⟩
  exact ⟨W.toModel A hM P⟩

def target (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d × Response)) : ℝ :=
  ∫ o, ((P:Measure (Model.Covariate d × Response))[
    outcomeScore∘Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o /
    ((P:Measure (Model.Covariate d × Response))[
    treatmentScore∘Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o
    ∂(P:Measure (Model.Covariate d × Response))

theorem generic_target_eq (A : Model.Parameters) (hM : 2≤A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) :
    Model.target A (observables A hM) P=target A.d P := by
  have hm : Model.covariateInformation A Response≤
      (inferInstance:MeasurableSpace (Model.Covariate A.d × Response)) := measurable_fst.comap_le
  simp only [Model.target,observables,Function.comp_def,integral_zero,zero_add,one_mul]
  change (∫ o, ((P:Measure (Model.Covariate A.d × Response))[
    fun _ => (1:ℝ) | Model.covariateInformation A Response]) o * _ / _ ∂_) = _
  rw [condExp_const hm]
  simp only [Pi.one_apply,one_mul]
  rfl

/-- Both source upper-rate regimes for the actual conditional Wald class. -/
theorem conditionalWald_upperBracket (A : Model.Parameters) (hM : 2≤A.M0) :
    Model.UpperBracket (target A.d) (modelClass A) A.bracketParameters (A.nu:ℝ) := by
  apply Model.upperBracket_congr_target (target A.d) (Model.target A (observables A hM))
    (modelClass A) A.bracketParameters (A.nu:ℝ)
  · intro P _
    exact (generic_target_eq A hM P).symm
  · exact Model.upperBracket_mono_class _ _ _ (modelClass_subset_generic A hM)
      (Model.model_upperBracket A (observables A hM))

end RoughRegime.Applications.ConditionalWald
