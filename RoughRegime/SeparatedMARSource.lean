module

public import RoughRegime.ApplicationSeparatedMAR
public import RoughRegime.MARSourceMembership
public import RoughRegime.RhoScaling


@[expose] public section
/-! The separated hard family uses an auxiliary generic radius. The literal
class keeps its own radius, including every H0 > 1, for w, 1-w and b. -/
noncomputable section
open MeasureTheory Set Filter
namespace RoughRegime.Applications.SeparatedMAR
open RoughRegime.Localization RoughRegime.LatticePriors RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def lowerParameters (A : Model.Parameters) : Model.Parameters :=
  {A with
    H := max 3 A.H
    gminus := A.gminus/2
    gplus := A.gplus/2
    M0 := 1
    hM0 := zero_lt_one
    hH := (by norm_num : (0:ℝ)<3).trans_le (le_max_left _ _)
    hgminus := half_pos A.hgminus
    hgplus := by linarith [A.hgplus]}

theorem lowerParameters_tau (A : Model.Parameters) :
    Rates.tau (lowerParameters A).gminus (lowerParameters A).gplus = Rates.tau A.gminus A.gplus :=
  Rates.tau_div _ _ 2 (by norm_num)

def densityGerm : SmoothGerm where
  K _ := 1
  domain := univ
  open_domain := isOpen_univ
  origin_mem := mem_univ _
  smooth := contDiffOn_const

def extraConditions (A : Model.Parameters) : Fin 5 → SourceExtraCondition A.α A.β :=
  ![⟨.holder MAR.propensityGerm A.α A.H,.first,
      by intro v _; norm_num [Condition.germ,MAR.propensityGerm,SmoothGerm.baseline],le_rfl⟩,
    ⟨.holder MAR.otherPropensityGerm A.α A.H,.first,
      by intro v _; norm_num [Condition.germ,MAR.otherPropensityGerm,SmoothGerm.baseline],le_rfl⟩,
    ⟨.holder MAR.regressionGerm A.β A.H,.second,
      by intro u _; simp [Condition.germ,MAR.regressionGerm,SmoothGerm.baseline],le_rfl⟩,
    ⟨.interval MAR.propensityGerm A.δ (1-A.δ),.first,
      by intro v _; norm_num [Condition.germ,MAR.propensityGerm,SmoothGerm.baseline],trivial⟩,
    ⟨.weighted densityGerm A.gminus A.gplus,.first,
      by intro v _; rfl,trivial⟩]

def augmentableClass (A : Model.Parameters) : Set (ProbabilityMeasure (Model.Covariate A.d × Response)) :=
  {P | ∃ W : Witness A P, (fun x => 1-W.w x) ∈ Model.holderBall A.α A.H}

theorem augmentable_subset (A : Model.Parameters) : augmentableClass A ⊆ modelClass A := by
  rintro P ⟨W,_⟩
  exact ⟨W⟩

theorem extra_baseline (A : Model.Parameters) (D : ℕ)
    (F : SourceModelFamily (lowerParameters A) D
      (MAR.observables ((lowerParameters A).withDimension D) le_rfl) MAR.baseline)
    (hδ : A.δ < 1/2) (hH : 1/2 < A.H) :
    ∀ i,(extraConditions A i).condition.baselineAdmissible F.rminus F.rplus := by
  have hrm : F.rminus=A.gminus := by
    unfold SourceModelFamily.rminus
    rw [(MAR.baseline_ratios ((lowerParameters A).withDimension D) le_rfl).1]
    change (A.gminus/2)/(1/2)=A.gminus
    ring
  have hrp : F.rplus=A.gplus := by
    unfold SourceModelFamily.rplus
    rw [(MAR.baseline_ratios ((lowerParameters A).withDimension D) le_rfl).1]
    change (A.gplus/2)/(1/2)=A.gplus
    ring
  intro i
  fin_cases i
  · change 0<A.α ∧ |(1-0)/2|<A.H
    norm_num
    exact ⟨A.hα,hH⟩
  · change 0<A.α ∧ |(1+0)/2|<A.H
    norm_num
    exact ⟨A.hα,hH⟩
  · change 0<A.β ∧ |1/2+2*0/(1-0)|<A.H
    norm_num
    exact ⟨A.hβ,hH⟩
  · change A.δ<(1-0)/2 ∧ (1-0)/2<1-A.δ
    constructor <;> linarith
  · change 0<(1:ℝ) ∧ A.gminus≤F.rminus*1 ∧ F.rplus*1≤A.gplus
    simp only [hrm,hrp,mul_one,le_refl,and_self,and_true]
    exact zero_lt_one

variable (A : Model.Parameters)
    (S : Scores (MAR.baseline : Measure Response))
    (hp : residualMomentU (lowerParameters A) (MAR.observables (lowerParameters A) le_rfl) MAR.baseline S true=1 ∧
      residualMomentU (lowerParameters A) (MAR.observables (lowerParameters A) le_rfl) MAR.baseline S false=0 ∧
      residualMomentV (lowerParameters A) (MAR.observables (lowerParameters A) le_rfl) MAR.baseline S true=0 ∧
      residualMomentV (lowerParameters A) (MAR.observables (lowerParameters A) le_rfl) MAR.baseline S false=1)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*S.C ≤ 1/4)
    (he : ∀ i,(extraConditions A i).condition.Holds F.p F.u F.v)

def sourceWitness : Witness A (law S F hsmall).probabilityMeasure where
  p := F.p
  w x := MAR.propensityGerm.K (F.u x,F.v x)
  b x := MAR.regressionGerm.K (F.u x,F.v x)
  measurableP := F.measurableP
  measurableW := (measurable_const.sub F.measurableU).div_const 2
  measurableB := measurable_const.add ((F.measurableV.const_mul 2).div (measurable_const.sub F.measurableU))
  nonnegativeP := Eventually.of_forall (fun x=>(F.densityBounds x).1)
  marginal := law_marginal S F hsmall
  momentD := by
    have h := law_conditional_snd S F hsmall MAR.observed MAR.observed_measurable 1 zero_le_one
      (fun z=>by simpa only [abs_of_nonneg (MAR.observed_range z).1] using (MAR.observed_range z).2)
    change (law S F hsmall).measure[MAR.observed ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[(law S F hsmall).measure]
      fun o=>MAR.propensityGerm.K (F.u o.1,F.v o.1)
    filter_upwards [h] with o ho
    simp only [Function.comp_apply] at ho
    rw [ho,(MAR.source_response_moments (lowerParameters A) le_rfl S hp F o.1).1]
    rfl
  momentV := by
    have h := law_conditional_snd S F hsmall MAR.observedOutcome MAR.observedOutcome_measurable 1 zero_le_one
      (fun z=>by simpa only [abs_of_nonneg (MAR.observedOutcome_range z).1] using (MAR.observedOutcome_range z).2)
    change (law S F hsmall).measure[MAR.observedOutcome ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[(law S F hsmall).measure]
      fun o=>MAR.propensityGerm.K (F.u o.1,F.v o.1)*MAR.regressionGerm.K (F.u o.1,F.v o.1)
    filter_upwards [h] with o ho
    simp only [Function.comp_apply] at ho
    rw [ho,(MAR.source_response_moments (lowerParameters A) le_rfl S hp F o.1).2]
    change (1-F.u o.1)/4+F.v o.1=((1-F.u o.1)/2)*(1/2+2*F.v o.1/(1-F.u o.1))
    field_simp [(MAR.source_denominator_pos (lowerParameters A) le_rfl S hp F hsmall o.1).ne']
    ring
  overlap := by
    have h := he 3
    change ∀ x∈Model.cube A.d,A.δ≤(1-F.u x)/2 ∧ (1-F.u x)/2≤1-A.δ at h
    filter_upwards [ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet] with x hx
    exact h x hx
  smoothW := he 0
  smoothB := he 2
  densityBounds := by
    have h := he 4
    change ∀ x∈Model.cube A.d,A.gminus≤F.p x*1 ∧ F.p x*1≤A.gplus at h
    filter_upwards [ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet] with x hx
    simpa only [mul_one] using h x hx

include hp he in
 theorem source_mem_augmentable : (law S F hsmall).probabilityMeasure ∈ augmentableClass A := by
  refine ⟨sourceWitness A S hp F hsmall he,?_⟩
  have h := he 1
  change (fun x=>(1+F.u x)/2) ∈ Model.holderBall A.α A.H at h
  have hh : (fun x : Model.Covariate A.d=>1-(MAR.propensityGerm.K (F.u x,F.v x))) =
      (fun x=>(1+F.u x)/2) := by funext x; change 1-(1-F.u x)/2=(1+F.u x)/2; ring
  change (fun x : Model.Covariate A.d=>1-(MAR.propensityGerm.K (F.u x,F.v x))) ∈ _
  rw [hh]
  exact h

end RoughRegime.Applications.SeparatedMAR
