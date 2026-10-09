module

public import RoughRegime.ApplicationMARUpper


@[expose] public section
/-! The literal separated-density missing-data class: smooth propensity,
bounded design density and bounded outcome, with no design smoothness. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.SeparatedMAR

abbrev Response := MAR.Response

structure Witness (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) where
  p : Model.Covariate A.d → ℝ
  w : Model.Covariate A.d → ℝ
  b : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableB : Measurable b
  nonnegativeP : 0≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P : Measure (Model.Covariate A.d × Response)).map Prod.fst =
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  momentD : (P : Measure (Model.Covariate A.d × Response))[
    MAR.observed ∘ Prod.snd | Model.covariateInformation A Response] =ᵐ[
      (P : Measure (Model.Covariate A.d × Response))] w ∘ Prod.fst
  momentV : (P : Measure (Model.Covariate A.d × Response))[
    MAR.observedOutcome ∘ Prod.snd | Model.covariateInformation A Response] =ᵐ[
      (P : Measure (Model.Covariate A.d × Response))] fun o => w o.1*b o.1
  overlap : ∀ᵐ x ∂Model.cubeVolume A.d, A.δ≤w x ∧ w x≤1-A.δ
  smoothW : w ∈ Model.holderBall A.α A.H
  smoothB : b ∈ Model.holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d, A.gminus≤p x ∧ p x≤A.gplus

def modelClass (A : Model.Parameters) : Set (ProbabilityMeasure (Model.Covariate A.d × Response)) :=
  {P | Nonempty (Witness A P)}

abbrev target := MAR.observedMean

theorem Witness.target_eq_mean (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P) :
    target A.d P = ∫ o, W.b o.1 ∂(P : Measure (Model.Covariate A.d × Response)) := by
  have hw : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)), A.δ≤W.w o.1 := by
    apply ae_of_ae_map (f := Prod.fst) (p := fun x => A.δ≤W.w x) measurable_fst.aemeasurable
    rw [W.marginal]
    exact (W.overlap.mono (fun x hx => hx.1)).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  apply integral_congr_ae
  filter_upwards [W.momentD,W.momentV,hw] with o hd hv ho
  simp only [Function.comp_apply] at hd
  change _ / _ = W.b o.1
  rw [hd,hv]
  exact mul_div_cancel_left₀ _ (ne_of_gt (A.hδ.trans_le ho))

end RoughRegime.Applications.SeparatedMAR
