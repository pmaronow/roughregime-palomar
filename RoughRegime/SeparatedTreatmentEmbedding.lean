module

public import RoughRegime.ApplicationSeparatedTreatment
public import RoughRegime.SeparatedMARSource
public import RoughRegime.ApplicationEffects


@[expose] public section
/-! Literal separated treatment laws from the actual independent fair-coin
augmentation, retaining the exact source Hölder radius. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.SeparatedMAR
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def Witness.selectedArm (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P) :
    SeparatedTreatment.ArmWitness A j (MAR.augmentationLaw A j P) where
  p := W.p
  w := W.w
  b := W.b
  measurableP := W.measurableP
  measurableW := W.measurableW
  measurableB := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := by rw [MAR.augmentationLaw_measure,MAR.augmentation_marginal]; exact W.marginal
  momentD := by
    rw [MAR.augmentationLaw_measure]
    exact (MAR.augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d×Response))
      W.w W.b W.measurableW W.measurableB W.momentD W.momentV).1
  momentV := by
    rw [MAR.augmentationLaw_measure]
    exact (MAR.augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d×Response))
      W.w W.b W.measurableW W.measurableB W.momentD W.momentV).2.1
  overlap := W.overlap
  smoothW := W.smoothW
  smoothB := W.smoothB
  densityBounds := W.densityBounds

def Witness.otherArm (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P)
    (hH : 1/2≤A.H) (hother : (fun x=>1-W.w x) ∈ Model.holderBall A.α A.H) :
    SeparatedTreatment.ArmWitness (MAR.parametersWithBeta A βother hβother) (!j) (MAR.augmentationLaw A j P) where
  p := W.p
  w x := 1-W.w x
  b _ := 1/2
  measurableP := W.measurableP
  measurableW := measurable_const.sub W.measurableW
  measurableB := measurable_const
  nonnegativeP := W.nonnegativeP
  marginal := by rw [MAR.augmentationLaw_measure,MAR.augmentation_marginal]; exact W.marginal
  momentD := by
    rw [MAR.augmentationLaw_measure]
    simpa only [Function.comp_def] using
      (MAR.augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d×Response))
        W.w W.b W.measurableW W.measurableB W.momentD W.momentV).2.2.1
  momentV := by
    rw [MAR.augmentationLaw_measure]
    simpa only [div_eq_mul_inv,one_mul] using
      (MAR.augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d×Response))
        W.w W.b W.measurableW W.measurableB W.momentD W.momentV).2.2.2
  overlap := W.overlap.mono (fun x hx=>⟨by linarith [hx.2],by linarith [hx.1]⟩)
  smoothW := hother
  smoothB := Model.const_mem_holderBall hβother (by norm_num; exact hH)
  densityBounds := W.densityBounds

def Witness.falseTreatment (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P)
    (hH : 1/2≤A.H) (hother : (fun x=>1-W.w x) ∈ Model.holderBall A.α A.H) :
    SeparatedTreatment.Witness A β1 hβ1 (MAR.augmentationLaw A false P) where
  p := W.p
  w x := 1-W.w x
  b0 := W.b
  b1 _ := 1/2
  measurableP := W.measurableP
  measurableW := measurable_const.sub W.measurableW
  measurableB0 := W.measurableB
  measurableB1 := measurable_const
  nonnegativeP := W.nonnegativeP
  marginal := (W.selectedArm A false P).marginal
  momentD0 := by simpa only [Function.comp_def,sub_sub_cancel,Witness.selectedArm,Model.covariateInformation] using (W.selectedArm A false P).momentD
  momentD1 := (W.otherArm A false β1 hβ1 P hH hother).momentD
  momentV0 := by simpa only [sub_sub_cancel,Witness.selectedArm,Model.covariateInformation] using (W.selectedArm A false P).momentV
  momentV1 := (W.otherArm A false β1 hβ1 P hH hother).momentV
  overlap := (W.otherArm A false β1 hβ1 P hH hother).overlap
  smoothW := hother
  smoothB0 := W.smoothB
  smoothB1 := Model.const_mem_holderBall hβ1 (by norm_num; exact hH)
  densityBounds := W.densityBounds

def Witness.trueTreatment (A : Model.Parameters) (β0 : ℝ) (hβ0 : 0<β0)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P)
    (hH : 1/2≤A.H) (hother : (fun x=>1-W.w x) ∈ Model.holderBall A.α A.H) :
    SeparatedTreatment.Witness (MAR.parametersWithBeta A β0 hβ0) A.β A.hβ (MAR.augmentationLaw A true P) where
  p := W.p
  w := W.w
  b0 _ := 1/2
  b1 := W.b
  measurableP := W.measurableP
  measurableW := W.measurableW
  measurableB0 := measurable_const
  measurableB1 := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := (W.selectedArm A true P).marginal
  momentD0 := (W.otherArm A true β0 hβ0 P hH hother).momentD
  momentD1 := (W.selectedArm A true P).momentD
  momentV0 := (W.otherArm A true β0 hβ0 P hH hother).momentV
  momentV1 := (W.selectedArm A true P).momentV
  overlap := W.overlap
  smoothW := W.smoothW
  smoothB0 := Model.const_mem_holderBall hβ0 (by norm_num; exact hH)
  smoothB1 := W.smoothB
  densityBounds := W.densityBounds

theorem augmentation_selected_armMean (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P) :
    MAR.armMean A.d j (MAR.augmentationLaw A j P)=target A.d P := by
  rw [(W.selectedArm A j P).armMean_eq_mean A j _,W.target_eq_mean A P,
    MAR.augmentationLaw_measure,MAR.augmentationKernel_law]
  change (∫o,(W.b ∘ Prod.fst) o ∂((P : Measure (Model.Covariate A.d×Response)).prod
    (MAR.fairCoin : Measure Bool)).map (MAR.augment A.d j)) = _
  rw [integral_map (MAR.augment_measurable A.d j).aemeasurable
    (W.measurableB.comp measurable_fst).aestronglyMeasurable]
  change (∫o,(W.b ∘ Prod.fst) o.1 ∂(P : Measure (Model.Covariate A.d×Response)).prod
    (MAR.fairCoin : Measure Bool)) = _
  rw [integral_fun_fst]
  simp only [probReal_univ,one_smul,Function.comp_def]

theorem augmentation_other_armMean (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P)
    (hH : 1/2≤A.H) (hother : (fun x=>1-W.w x) ∈ Model.holderBall A.α A.H) :
    MAR.armMean A.d (!j) (MAR.augmentationLaw A j P)=1/2 := by
  rw [(W.otherArm A j βother hβother P hH hother).armMean_eq_mean (MAR.parametersWithBeta A βother hβother) (!j) _]
  change (∫_o : Model.Covariate A.d×MAR.TreatmentResponse,(1/2:ℝ)
    ∂(MAR.augmentationLaw A j P : Measure (Model.Covariate A.d×MAR.TreatmentResponse))) = _
  simp only [integral_const,probReal_univ,one_smul]

end RoughRegime.Applications.SeparatedMAR
