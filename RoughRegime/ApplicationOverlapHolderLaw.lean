module

public import RoughRegime.ApplicationOverlapHolderCounterexample
public import RoughRegime.ApplicationOverlapAffine
public import RoughRegime.ApplicationOverlapBracket


@[expose] public section
/-! A genuine uniform-design binary law realizes the higher-beta difference:
Y=A, the overlapping cusp is both conditional means, and gammaOW=1. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ContDiff
namespace RoughRegime.Applications.Overlap
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def perfectBaseline:ProbabilityMeasure Response:=
  ProbabilityMeasure.map ⟨(LatticeFourier.signLaw 1 (by norm_num)).toMeasure,inferInstance⟩ binaryPoint

theorem perfectBaseline_integral (f:Response→ℝ) (hf:Measurable f):
    (∫ z,f z ∂(perfectBaseline:Measure Response))=
      (f (binaryPoint (false,false))+f (binaryPoint (true,true)))/2 := by
  change (∫ z,f z ∂(LatticeFourier.signLaw 1 (by norm_num)).toMeasure.map binaryPoint)=_
  rw [integral_map (measurable_of_countable binaryPoint).aemeasurable hf.aestronglyMeasurable,PMF.integral_eq_sum]
  simp only [LatticeFourier.signLaw_apply,ENNReal.toReal_ofReal
    (RoughRegime.Lower.signWeight_nonneg (by norm_num : |(1:ℝ)| ≤ 1) _ _),smul_eq_mul,Fintype.sum_prod_type]
  simp [RoughRegime.Lower.signWeight,RoughRegime.Lower.sign]
  ring

def perfectScores:Scores (perfectBaseline:Measure Response) where
  su:=signA
  sv _:=0
  measurableU:=signA_measurable
  measurableV:=measurable_const
  C:=1
  nonnegativeC:=zero_le_one
  boundU z:=(signA_abs z).le
  boundV _:=by norm_num
  meanU:=by
    rw [perfectBaseline_integral _ signA_measurable]
    norm_num [signA,binaryPoint,RoughRegime.Lower.sign]
  meanV:=by simp

def cuspField:Field (Model.cubeVolume 1) where
  p _:=1
  u x:=2*cuspPropensity x-1
  v _:=0
  measurableP:=measurable_const
  measurableU:=(cuspPropensity_continuous.measurable.const_mul 2).sub_const 1
  measurableV:=measurable_const
  P:=1
  nonnegativeP:=zero_le_one
  densityBounds _:=⟨zero_le_one,le_refl _⟩
  integralP:=by simp
  epsilon:=1/4
  nonnegativeEpsilon:=by norm_num
  boundU x:=by
    rw [abs_of_nonneg (by linarith [(cuspPropensity_range x).1])]
    linarith [(cuspPropensity_range x).2]
  boundV _:=by norm_num

def cuspLaw:GeneralTesting.DensityLaw ((Model.cubeVolume 1).prod (perfectBaseline:Measure Response)):=
  law perfectScores cuspField (by norm_num [cuspField,perfectScores])

abbrev cuspParameters:Model.Parameters:=paperParameters 1 1 1 2 (1/2) 2
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem perfect_affine_means (u v:ℝ):
    affineMean perfectBaseline perfectScores (fun _=>1) u v=1 ∧
    affineMean perfectBaseline perfectScores treatment u v=(1+u)/2 ∧
    affineMean perfectBaseline perfectScores outcome u v=(1+u)/2 ∧
    affineMean perfectBaseline perfectScores (fun z=>treatment z*outcome z) u v=(1+u)/2 := by
  unfold affineMean
  simp only [perfectScores,mul_zero,integral_zero,add_zero,one_mul]
  rw [perfectBaseline_integral _ measurable_const,
    perfectBaseline_integral _ signA_measurable,
    perfectBaseline_integral _ treatment_measurable,
    perfectBaseline_integral (fun z=>treatment z*signA z) (treatment_measurable.mul signA_measurable),
    perfectBaseline_integral _ outcome_measurable,
    perfectBaseline_integral (fun z=>outcome z*signA z) (outcome_measurable.mul signA_measurable),
    perfectBaseline_integral (fun z=>treatment z*outcome z) (treatment_measurable.mul outcome_measurable),
    perfectBaseline_integral (fun z=>(treatment z*outcome z)*signA z) ((treatment_measurable.mul outcome_measurable).mul signA_measurable)]
  norm_num [signA,binaryPoint,treatment,outcome,MAR.armIndicator,MAR.bitOutcome,RoughRegime.Lower.sign]
  ring

def cuspLaw_witness:Witness cuspParameters (1/4) cuspLaw.probabilityMeasure:=by
  have hs:cuspField.epsilon*perfectScores.C ≤ 1/4:=by norm_num [cuspField,perfectScores]
  have hw:cuspPropensity∈Model.holderBall 1 2:=by
    change Model.holderNorm cuspPropensity 1 ≤ ENNReal.ofReal 2
    exact cuspPropensity_mem_holder_one.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  refine {
    p:=fun _=>1
    mU:=cuspPropensity
    mV:=cuspPropensity
    measurableP:=measurable_const
    measurableU:=cuspPropensity_continuous.measurable
    measurableV:=cuspPropensity_continuous.measurable
    nonnegativeP:=ae_of_all _ fun _=>zero_le_one
    marginal:=law_marginal perfectScores cuspField hs
    smoothU:=hw
    smoothV:=hw
    densityBounds:=ae_of_all _ fun _=>by norm_num [cuspParameters,paperParameters]
    overlap:=ae_of_all _ fun x=>by have h:=cuspPropensity_range x;constructor <;> linarith [h.1,h.2]
    momentU:=?_
    momentV:=?_}
  · have h:=law_conditional_snd perfectScores cuspField hs treatment treatment_measurable 1 zero_le_one treatment_bound
    apply h.trans (ae_of_all _ fun o=>?_)
    change responseMoment perfectScores cuspField treatment o.1=cuspPropensity o.1
    rw [bounded_responseMoment_eq_affineMean cuspParameters perfectBaseline perfectScores cuspField treatment
      treatment_measurable 1 zero_le_one treatment_bound,(perfect_affine_means _ _).2.1]
    dsimp [cuspField];ring
  · have h:=law_conditional_snd perfectScores cuspField hs outcome outcome_measurable 1 zero_le_one outcome_bound
    apply h.trans (ae_of_all _ fun o=>?_)
    change responseMoment perfectScores cuspField outcome o.1=cuspPropensity o.1
    rw [bounded_responseMoment_eq_affineMean cuspParameters perfectBaseline perfectScores cuspField outcome
      outcome_measurable 1 zero_le_one outcome_bound,(perfect_affine_means _ _).2.2.1]
    dsimp [cuspField];ring


theorem cuspLaw_uniform_design:
    (cuspLaw.probabilityMeasure:Measure (Model.Covariate 1×Response)).map Prod.fst=Model.cubeVolume 1:=by
  have h:=cuspLaw_witness.marginal
  change (cuspLaw.probabilityMeasure:Measure (Model.Covariate 1×Response)).map Prod.fst=
    (Model.cubeVolume 1).withDensity (fun _=>ENNReal.ofReal 1) at h
  simp only [ENNReal.ofReal_one] at h
  change (cuspLaw.probabilityMeasure:Measure (Model.Covariate 1×Response)).map Prod.fst=
    (Model.cubeVolume 1).withDensity (1:Model.Covariate 1→ℝ≥0∞) at h
  rw [withDensity_one] at h
  exact h

theorem cuspLaw_outcome_eq_treatment:
    ∀ᵐ o ∂(cuspLaw.probabilityMeasure:Measure (Model.Covariate 1×Response)),outcome o.2=treatment o.2:=by
  let f:Response→ℝ:=fun z=>outcome z-treatment z
  have hf:Measurable f:=outcome_measurable.sub treatment_measurable
  have hfL:MemLp f 2 (perfectBaseline:Measure Response):=bounded_memLp _ f hf 1 fun z=>by
    rw [abs_le];have ho:=outcome_range z;have ha:=treatment_range z
    constructor <;> dsimp [f] <;> linarith [ho.1,ho.2,ha.1,ha.2]
  have hz:(∫ z,f z^2 ∂(perfectBaseline:Measure Response))=0:=by
    rw [perfectBaseline_integral _ (hf.pow_const 2)]
    norm_num [f,outcome,treatment,binaryPoint,MAR.armIndicator,MAR.bitOutcome]
  have he:(fun z=>f z^2)=ᵐ[(perfectBaseline:Measure Response)] fun _=>0:=
    (integral_eq_zero_iff_of_nonneg (fun _=>sq_nonneg _) hfL.integrable_sq).mp hz
  have hπ:∀ᵐ z ∂(perfectBaseline:Measure Response),outcome z=treatment z:=by
    filter_upwards [he] with z hz
    dsimp [f] at hz
    nlinarith [sq_nonneg (outcome z-treatment z)]
  have hbase:∀ᵐ o ∂((Model.cubeVolume 1).prod (perfectBaseline:Measure Response)),outcome o.2=treatment o.2:=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hπ
  exact hbase.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

theorem cuspLaw_effect_one:effect 1 cuspLaw.probabilityMeasure=1:=by
  have hM:1 ≤ cuspParameters.M0:=by norm_num [cuspParameters,paperParameters]
  have hs:cuspField.epsilon*perfectScores.C ≤ 1/4:=by norm_num [cuspField,perfectScores]
  have hND:numerator 1 cuspLaw.probabilityMeasure=denominator 1 cuspLaw.probabilityMeasure:=by
    change numerator cuspParameters.d cuspLaw.probabilityMeasure=denominator cuspParameters.d cuspLaw.probabilityMeasure
    rw [← numerator_target cuspParameters hM,← denominator_target cuspParameters hM]
    change Model.target cuspParameters _ (law perfectScores cuspField hs).probabilityMeasure=
      Model.target (diagonalParameters cuspParameters) _ (law perfectScores cuspField hs).probabilityMeasure
    rw [model_target_integral cuspParameters (numeratorObservables cuspParameters hM) _ perfectScores cuspField hs
        (by change 0<(∫ _z,(1:ℝ) ∂(perfectBaseline:Measure Response));simp),
      model_target_integral (diagonalParameters cuspParameters) (denominatorObservables cuspParameters hM) _ perfectScores cuspField hs
        (by change 0<(∫ _z,(1:ℝ) ∂(perfectBaseline:Measure Response));simp)]
    apply integral_congr_ae
    filter_upwards with x
    have hsq:(fun z=>treatment z*treatment z)=treatment:=by
      funext z;simpa only [pow_two] using treatment_sq z
    change 1*(affineMean perfectBaseline perfectScores (fun z=>treatment z*outcome z) _ _+(-1)*
        (affineMean perfectBaseline perfectScores treatment _ _*affineMean perfectBaseline perfectScores outcome _ _/
          affineMean perfectBaseline perfectScores (fun _=>1) _ _))=
      1*(affineMean perfectBaseline perfectScores (fun z=>treatment z*treatment z) _ _+(-1)*
        (affineMean perfectBaseline perfectScores treatment _ _*affineMean perfectBaseline perfectScores treatment _ _/
          affineMean perfectBaseline perfectScores (fun _=>1) _ _))
    rw [hsq,(perfect_affine_means _ _).1,(perfect_affine_means _ _).2.1,
      (perfect_affine_means _ _).2.2.1,(perfect_affine_means _ _).2.2.2]
  have hd:0<denominator 1 cuspLaw.probabilityMeasure:=
    (by norm_num : (0:ℝ)<(1/4)*(1-1/4)).trans_le
      (denominator_bounds cuspParameters (1/4) (by norm_num) (by norm_num) _ cuspLaw_witness).1
  rw [effect,hND,div_self hd.ne']

/-- The actual OW coefficient equals one and the actual conditional outcome
mean is the cusp propensity, so the source's two conventions truly differ. -/
theorem higher_beta_actual_overlap_conditions_differ:
    let P:=cuspLaw.probabilityMeasure
    (P:Measure (Model.Covariate 1×Response)).map Prod.fst=Model.cubeVolume 1 ∧
    (∀ᵐ o ∂(P:Measure (Model.Covariate 1×Response)),outcome o.2=treatment o.2) ∧
    (∀ x,cuspPropensity x∈Icc (1/2:ℝ) (5/8)) ∧
    (P:Measure (Model.Covariate 1×Response))[treatment∘Prod.snd|MeasurableSpace.comap Prod.fst inferInstance]=ᵐ[(P:Measure (Model.Covariate 1×Response))]
      cuspPropensity∘Prod.fst ∧
    (P:Measure (Model.Covariate 1×Response))[outcome∘Prod.snd|MeasurableSpace.comap Prod.fst inferInstance]=ᵐ[(P:Measure (Model.Covariate 1×Response))]
      cuspPropensity∘Prod.fst ∧
    effect 1 P=1 ∧ cuspPropensity∈Model.holderBall 1 1 ∧
    (fun x=>cuspPropensity x-effect 1 P*cuspPropensity x)∈Model.holderBall 2 1 ∧
    (∀ H:ℝ,cuspPropensity∉Model.holderBall 2 H) := by
  refine ⟨cuspLaw_uniform_design,cuspLaw_outcome_eq_treatment,cuspPropensity_range,cuspLaw_witness.momentU,cuspLaw_witness.momentV,cuspLaw_effect_one,
    cuspPropensity_mem_holder_one,?_,cuspPropensity_not_mem_holder_two⟩
  rw [cuspLaw_effect_one]
  simpa only [one_mul,sub_self] using Model.const_mem_holderBall (d:=1) (t:=2) (c:=0) (H:=1) (by norm_num) (by norm_num)

end RoughRegime.Applications.Overlap
