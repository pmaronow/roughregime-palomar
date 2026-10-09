module

public import RoughRegime.SeparatedTreatmentEmbedding


@[expose] public section
/-! Conditional regressions, positive arm probabilities and exact constant
CATE effects from the literal separated moment witnesses. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.SeparatedTreatment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem ArmWitness.overlap_on_observations (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse)) (W : ArmWitness A j P) :
    ∀ᵐo ∂(P : Measure (Model.Covariate A.d×MAR.TreatmentResponse)),A.δ≤W.w o.1 ∧ W.w o.1≤1-A.δ := by
  apply ae_of_ae_map (f:=Prod.fst) (p:=fun x=>A.δ≤W.w x ∧ W.w x≤1-A.δ) measurable_fst.aemeasurable
  rw [W.marginal]
  exact W.overlap.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

theorem ArmWitness.regression_eq (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse)) (W : ArmWitness A j P) :
    MAR.regression A.d j P =ᵐ[(P : Measure (Model.Covariate A.d×MAR.TreatmentResponse))] W.b ∘ Prod.fst := by
  filter_upwards [W.momentD,W.momentV,W.overlap_on_observations A j P] with o hd hv hw
  dsimp only [MAR.regression,Function.comp_apply] at hd ⊢
  rw [hd,hv]
  exact mul_div_cancel_left₀ _ (ne_of_gt (A.hδ.trans_le hw.1))

theorem ArmWitness.armProbability_pos (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d×MAR.TreatmentResponse)) (W : ArmWitness A j P) :
    0<MAR.armProbability A.d j P := by
  have hw : Integrable (W.w ∘ Prod.fst) (P : Measure (Model.Covariate A.d×MAR.TreatmentResponse)) :=
    Integrable.of_mem_Icc A.δ (1-A.δ) (W.measurableW.comp measurable_fst).aemeasurable
      (W.overlap_on_observations A j P)
  have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace (Model.Covariate A.d×MAR.TreatmentResponse)) := measurable_fst.comap_le
  have he : MAR.armProbability A.d j P=∫o,W.w o.1 ∂(P : Measure (Model.Covariate A.d×MAR.TreatmentResponse)) := by
    unfold MAR.armProbability
    rw [←integral_condExp hm]
    exact integral_congr_ae W.momentD
  rw [he]
  have hle := integral_mono_ae (integrable_const A.δ) hw
    ((W.overlap_on_observations A j P).mono (fun o ho=>ho.1))
  simp only [integral_const,probReal_univ,one_smul,Function.comp_apply] at hle
  exact A.hδ.trans_le hle

end RoughRegime.Applications.SeparatedTreatment
namespace RoughRegime.Applications.SeparatedMAR

theorem augmentation_constant_effects (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P)
    (hH : 1/2≤A.H) (hother : (fun x=>1-W.w x) ∈ Model.holderBall A.α A.H)
    (c : ℝ) (hc : ∀x,W.b x=c) :
    MAR.ate A.d (MAR.augmentationLaw A j P)=MAR.armSign j*(c-1/2) ∧
      ∀k,MAR.conditionalEffect A.d k (MAR.augmentationLaw A j P)=MAR.armSign j*(c-1/2) := by
  have hm : target A.d P=c := by
    rw [W.target_eq_mean A P]
    simp only [hc,integral_const,probReal_univ,one_smul]
  have hs := augmentation_selected_armMean A j P W
  have ho := augmentation_other_armMean A j βother hβother P W hH hother
  constructor
  · cases j <;> simp only [Bool.not_false,Bool.not_true] at ho <;>
      simp [MAR.ate,MAR.armSign,hs,ho,hm]
  · intro k
    have hreg : (fun o=>MAR.regression A.d true (MAR.augmentationLaw A j P) o-
        MAR.regression A.d false (MAR.augmentationLaw A j P) o) =ᵐ[
          (MAR.augmentationLaw A j P : Measure (Model.Covariate A.d×MAR.TreatmentResponse))]
          fun _=>MAR.armSign j*(c-1/2) := by
      have hjs := (W.selectedArm A j P).regression_eq A j _
      have hjo := (W.otherArm A j βother hβother P hH hother).regression_eq
        (MAR.parametersWithBeta A βother hβother) (!j) _
      filter_upwards [hjs,hjo] with o hso hoo
      cases j <;> simp [MAR.armSign,Witness.selectedArm,Witness.otherArm,hc] at hso hoo ⊢ <;> linarith
    have hp : 0<MAR.armProbability A.d k (MAR.augmentationLaw A j P) := by
      by_cases hkj : k=j
      · subst k
        exact (W.selectedArm A j P).armProbability_pos A j _
      · have he : k= !j := by cases k <;> cases j <;> simp_all
        rw [he]
        exact (W.otherArm A j βother hβother P hH hother).armProbability_pos
          (MAR.parametersWithBeta A βother hβother) (!j) _
    unfold MAR.conditionalEffect
    have he : (∫o,MAR.armIndicator k o.2*(MAR.regression A.d true (MAR.augmentationLaw A j P) o-
        MAR.regression A.d false (MAR.augmentationLaw A j P) o) ∂(MAR.augmentationLaw A j P :
          Measure (Model.Covariate A.d×MAR.TreatmentResponse))) =
          MAR.armProbability A.d k (MAR.augmentationLaw A j P)*(MAR.armSign j*(c-1/2)) := by
      calc
        _ = ∫o,MAR.armIndicator k o.2*(MAR.armSign j*(c-1/2)) ∂(MAR.augmentationLaw A j P :
            Measure (Model.Covariate A.d×MAR.TreatmentResponse)) := integral_congr_ae
          (hreg.mono (fun o ho=>congrArg (fun z=>MAR.armIndicator k o.2*z) ho))
        _ = _ := integral_mul_const _ _
    rw [he]
    exact mul_div_cancel_left₀ _ hp.ne'

end RoughRegime.Applications.SeparatedMAR
