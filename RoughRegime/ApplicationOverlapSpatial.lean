module

public import RoughRegime.ApplicationOverlapAffine
public import RoughRegime.HolderConstants


@[expose] public section
/-! Membership in the literal overlap class for the actual normalized affine
observation laws, including the two distinct hard-family mean structures. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Overlap
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

 theorem independent_law_mem (A : Model.Parameters) (ε c : ℝ) (hc : |c|≤1/4)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*(scores c hc).C≤1/4)
    (ha : (fun x=>1/2+F.u x)∈Model.holderBall A.α A.H)
    (hb : (fun x=>1/2+F.v x)∈Model.holderBall A.β A.H)
    (hd : ∀ᵐ x ∂Model.cubeVolume A.d,A.gminus≤F.p x ∧ F.p x≤A.gplus)
    (hov : ∀ᵐ x ∂Model.cubeVolume A.d,ε≤1/2+F.u x ∧ 1/2+F.u x≤1-ε) :
    (law (scores c hc) F hsmall).probabilityMeasure∈modelClass A ε := by
  refine ⟨{
    p:=F.p
    mU:=fun x=>1/2+F.u x
    mV:=fun x=>1/2+F.v x
    measurableP:=F.measurableP
    measurableU:=measurable_const.add F.measurableU
    measurableV:=measurable_const.add F.measurableV
    nonnegativeP:=ae_of_all _ fun x=>(F.densityBounds x).1
    marginal:=law_marginal _ _ _
    smoothU:=ha
    smoothV:=hb
    densityBounds:=hd
    overlap:=hov
    momentU:=?_
    momentV:=?_}⟩
  · have he := law_conditional_snd (scores c hc) F hsmall treatment treatment_measurable 1 zero_le_one treatment_bound
    refine he.trans (ae_of_all _ fun o=>?_)
    change responseMoment _ F treatment o.1=1/2+F.u o.1
    rw [bounded_responseMoment_eq_affineMean A (baseline c hc) (scores c hc) F treatment treatment_measurable 1
      zero_le_one treatment_bound,affineMean_treatment]
  · have he := law_conditional_snd (scores c hc) F hsmall outcome outcome_measurable 1 zero_le_one outcome_bound
    refine he.trans (ae_of_all _ fun o=>?_)
    change responseMoment _ F outcome o.1=1/2+F.v o.1
    rw [bounded_responseMoment_eq_affineMean A (baseline c hc) (scores c hc) F outcome outcome_measurable 1
      zero_le_one outcome_bound,affineMean_outcome]

 theorem diagonal_law_mem (A : Model.Parameters) (ε : ℝ) (hH : 1/2≤A.H)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*diagonalScores.C≤1/4)
    (ha : (fun x=>1/2+F.u x+F.v x)∈Model.holderBall A.α A.H)
    (hd : ∀ᵐ x ∂Model.cubeVolume A.d,A.gminus≤F.p x ∧ F.p x≤A.gplus)
    (hov : ∀ᵐ x ∂Model.cubeVolume A.d,ε≤1/2+F.u x+F.v x ∧ 1/2+F.u x+F.v x≤1-ε) :
    (law diagonalScores F hsmall).probabilityMeasure∈modelClass A ε := by
  refine ⟨{
    p:=F.p
    mU:=fun x=>1/2+F.u x+F.v x
    mV:=fun _=>1/2
    measurableP:=F.measurableP
    measurableU:=(measurable_const.add F.measurableU).add F.measurableV
    measurableV:=measurable_const
    nonnegativeP:=ae_of_all _ fun x=>(F.densityBounds x).1
    marginal:=law_marginal _ _ _
    smoothU:=ha
    smoothV:=Model.const_mem_holderBall A.hβ (by simpa only [abs_of_pos (by norm_num : (0:ℝ)<1/2)] using hH)
    densityBounds:=hd
    overlap:=hov
    momentU:=?_
    momentV:=?_}⟩
  · have he := law_conditional_snd diagonalScores F hsmall treatment treatment_measurable 1 zero_le_one treatment_bound
    refine he.trans (ae_of_all _ fun o=>?_)
    change responseMoment _ F treatment o.1=1/2+F.u o.1+F.v o.1
    rw [bounded_responseMoment_eq_affineMean A _ diagonalScores F treatment treatment_measurable 1
      zero_le_one treatment_bound,(diagonal_affine_means _ _).2.1]
  · have he := law_conditional_snd diagonalScores F hsmall outcome outcome_measurable 1 zero_le_one outcome_bound
    refine he.trans (ae_of_all _ fun o=>?_)
    change responseMoment _ F outcome o.1=1/2
    rw [bounded_responseMoment_eq_affineMean A _ diagonalScores F outcome outcome_measurable 1
      zero_le_one outcome_bound,(diagonal_affine_means _ _).2.2.1]

end RoughRegime.Applications.Overlap
