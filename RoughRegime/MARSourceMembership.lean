module

public import RoughRegime.MARSourceGerms
public import RoughRegime.ApplicationEffectTransfers


@[expose] public section
/-! Actual conditional-moment membership of the source affine MAR laws in
both treatment augmentation classes, obtained from the finite genuine germs. -/
noncomputable section
open MeasureTheory Set Filter
namespace RoughRegime.Applications.MAR
open RoughRegime.SpatialAffine RoughRegime.Localization RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (S : Scores (baseline : Measure Response))
    (hp : residualMomentU A (observables A hM) baseline S true=1 ∧
      residualMomentU A (observables A hM) baseline S false=0 ∧
      residualMomentV A (observables A hM) baseline S true=0 ∧
      residualMomentV A (observables A hM) baseline S false=1)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*S.C ≤ 1/4)
    (he : ∀ i,(treatmentExtraConditions A i).condition.Holds F.p F.u F.v)

 include hM hp hsmall in
 theorem source_denominator_pos (x : Model.Covariate A.d) : 0<1-F.u x := by
   have h := responseMoment_D_lower A (observables A hM) baseline S F hsmall (by
     rw [(baseline_ratios A hM).1]; norm_num) x
   change Model.baselineW A (observables A hM) baseline/2 ≤ responseMoment S F observed x at h
   rw [(baseline_ratios A hM).1,(source_response_moments A hM S hp F x).1] at h
   linarith

 def sourceMARWitness : Witness A (law S F hsmall).probabilityMeasure where
   p := F.p
   w x := propensityGerm.K (F.u x,F.v x)
   b x := regressionGerm.K (F.u x,F.v x)
   measurableP := F.measurableP
   measurableW := (measurable_const.sub F.measurableU).div_const 2
   measurableB := measurable_const.add ((F.measurableV.const_mul 2).div (measurable_const.sub F.measurableU))
   nonnegativeP := Eventually.of_forall (fun x=>(F.densityBounds x).1)
   marginal := law_marginal S F hsmall
   momentD := by
     have h := law_conditional_snd S F hsmall observed observed_measurable 1 zero_le_one
       (fun z=>by simpa only [abs_of_nonneg (observed_range z).1] using (observed_range z).2)
     change (law S F hsmall).measure[observed ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[(law S F hsmall).measure]
       fun o=>propensityGerm.K (F.u o.1,F.v o.1)
     filter_upwards [h] with o ho
     simp only [Function.comp_apply] at ho
     rw [ho,(source_response_moments A hM S hp F o.1).1]
     rfl
   momentV := by
     have h := law_conditional_snd S F hsmall observedOutcome observedOutcome_measurable 1 zero_le_one
       (fun z=>by simpa only [abs_of_nonneg (observedOutcome_range z).1] using (observedOutcome_range z).2)
     change (law S F hsmall).measure[observedOutcome ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[(law S F hsmall).measure]
       fun o=>propensityGerm.K (F.u o.1,F.v o.1)*regressionGerm.K (F.u o.1,F.v o.1)
     filter_upwards [h] with o ho
     simp only [Function.comp_apply] at ho
     rw [ho,(source_response_moments A hM S hp F o.1).2]
     change (1-F.u o.1)/4+F.v o.1=((1-F.u o.1)/2)*(1/2+2*F.v o.1/(1-F.u o.1))
     field_simp [(source_denominator_pos A hM S hp F hsmall o.1).ne']
     ring
   overlap := by
     have h := he 3
     change ∀ x∈Model.cube A.d,A.δ≤(1-F.u x)/2 ∧ (1-F.u x)/2≤1-A.δ at h
     filter_upwards [ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet] with x hx
     exact h x hx
   smoothInverse := by
     have h := he 0
     change (fun x=>2/(1-F.u x)) ∈ Model.holderBall A.α A.H at h
     have hid : (fun x : Model.Covariate A.d => (propensityGerm.K (F.u x,F.v x))⁻¹) =
       (fun x=>2/(1-F.u x)) := by
       funext x
       exact inv_div _ _
     rw [hid]
     exact h
   smoothB := he 1
   densityBounds := by
     have h := he 4
     change ∀ x∈Model.cube A.d,A.gminus ≤ F.p x*((1-F.u x)/2) ∧ F.p x*((1-F.u x)/2)≤A.gplus at h
     filter_upwards [ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet] with x hx
     change A.gminus≤((1-F.u x)/2)*F.p x ∧ ((1-F.u x)/2)*F.p x≤A.gplus
     simpa only [mul_comm] using h x hx

 include he hM hp in
 theorem source_law_mem_augmentable : (law S F hsmall).probabilityMeasure ∈ augmentableClass A := by
   let W := sourceMARWitness A hM S hp F hsmall he
   refine ⟨W,?_,?_⟩
   · have h := he 2
     change (fun x=>2/(1+F.u x)) ∈ Model.holderBall A.α A.H at h
     have hid : (fun x : Model.Covariate A.d => (1-W.w x)⁻¹) = (fun x=>2/(1+F.u x)) := by
       funext x
       change (1-(1-F.u x)/2)⁻¹=2/(1+F.u x)
       have hh : 1-(1-F.u x)/2=(1+F.u x)/2 := by ring
       rw [hh,inv_div]
     rw [hid]
     exact h
   · have h := he 5
     change ∀ x∈Model.cube A.d,A.gminus≤F.p x*((1+F.u x)/2) ∧ F.p x*((1+F.u x)/2)≤A.gplus at h
     filter_upwards [ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet] with x hx
     change A.gminus≤(1-(1-F.u x)/2)*F.p x ∧ (1-(1-F.u x)/2)*F.p x≤A.gplus
     have hh : 1-(1-F.u x)/2=(1+F.u x)/2 := by ring
     rw [hh]
     simpa only [mul_comm] using h x hx

end RoughRegime.Applications.MAR
