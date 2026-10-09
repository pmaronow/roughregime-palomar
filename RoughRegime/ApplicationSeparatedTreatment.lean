module

public import RoughRegime.ApplicationSeparatedMAR
public import RoughRegime.ApplicationEffects
public import RoughRegime.HolderFiniteAffine


@[expose] public section
/-! Literal separated-density treatment laws and their genuine arm maps. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.SeparatedTreatment
set_option maxHeartbeats 600000

structure ArmWitness (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) where
  p : Model.Covariate A.d → ℝ
  w : Model.Covariate A.d → ℝ
  b : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableB : Measurable b
  nonnegativeP : 0 ≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)).map Prod.fst =
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  momentD : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))[MAR.armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
    (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))] w ∘ Prod.fst
  momentV : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))[MAR.armOutcome j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
    (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))] fun o => w o.1 * b o.1
  overlap : ∀ᵐ x ∂Model.cubeVolume A.d, A.δ ≤ w x ∧ w x ≤ 1 - A.δ
  smoothW : w ∈ Model.holderBall A.α A.H
  smoothB : b ∈ Model.holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d,
    A.gminus ≤ p x ∧ p x ≤ A.gplus

def ArmWitness.keepArmWitness (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) (h : ArmWitness A j P) :
    SeparatedMAR.Witness A (MAR.keepArmLaw A j P) where
  p := h.p
  w := h.w
  b := h.b
  measurableP := h.measurableP
  measurableW := h.measurableW
  measurableB := h.measurableB
  nonnegativeP := h.nonnegativeP
  marginal := by
    rw [MAR.keepArmLaw_measure, Measure.map_map measurable_fst (MAR.keepArm_measurable A.d j)]
    exact h.marginal
  momentD := by
    rw [MAR.keepArmLaw_measure]
    apply MAR.keepArm_conditional A.d j (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)) MAR.observed MAR.observed_measurable h.w h.measurableW
    · apply Integrable.of_mem_Icc 0 1
      · exact (MAR.observed_measurable.comp ((MAR.keepArmResponse_measurable j).comp measurable_snd)).aemeasurable
      · exact Filter.Eventually.of_forall (fun o => MAR.observed_range (MAR.keepArmResponse j o.2))
    · have hf : (fun o : Model.Covariate A.d × MAR.TreatmentResponse =>
          MAR.observed (MAR.keepArmResponse j o.2)) = MAR.armIndicator j ∘ Prod.snd :=
        funext (fun o => (MAR.keepArmResponse_moments j o.2).1)
      rw [hf]
      exact h.momentD
  momentV := by
    rw [MAR.keepArmLaw_measure]
    apply MAR.keepArm_conditional A.d j (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)) MAR.observedOutcome MAR.observedOutcome_measurable
      (fun x => h.w x * h.b x) (h.measurableW.mul h.measurableB)
    · apply Integrable.of_mem_Icc 0 1
      · exact (MAR.observedOutcome_measurable.comp
          ((MAR.keepArmResponse_measurable j).comp measurable_snd)).aemeasurable
      · exact Filter.Eventually.of_forall (fun o => MAR.observedOutcome_range (MAR.keepArmResponse j o.2))
    · have hf : (fun o : Model.Covariate A.d × MAR.TreatmentResponse =>
          MAR.observedOutcome (MAR.keepArmResponse j o.2)) = MAR.armOutcome j ∘ Prod.snd :=
        funext (fun o => (MAR.keepArmResponse_moments j o.2).2)
      rw [hf]
      exact h.momentV
  overlap := h.overlap
  smoothW := h.smoothW
  smoothB := h.smoothB
  densityBounds := h.densityBounds

theorem ArmWitness.armMean_eq_mean (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) (h : ArmWitness A j P) :
    MAR.armMean A.d j P = ∫ o, h.b o.1 ∂(P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)) := by
  have hw : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)), A.δ ≤ h.w o.1 := by
    apply ae_of_ae_map (μ := (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)))
      (f := Prod.fst) (p := fun x => A.δ ≤ h.w x) measurable_fst.aemeasurable
    rw [h.marginal]
    exact (h.overlap.mono (fun x hx => hx.1)).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  apply integral_congr_ae
  filter_upwards [h.momentD, h.momentV, hw] with o hD hV ho
  dsimp only [Function.comp_apply] at hD
  rw [hD, hV]
  exact mul_div_cancel_left₀ _ (ne_of_gt (A.hδ.trans_le ho))

def armClass (A : Model.Parameters) (j : Bool) :
    Set (ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) :=
  {P | Nonempty (ArmWitness A j P)}

theorem keepArm_target_eq_armMean (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) (W : ArmWitness A j P) :
    SeparatedMAR.target A.d (MAR.keepArmLaw A j P) = MAR.armMean A.d j P := by
  rw [SeparatedMAR.Witness.target_eq_mean A _ (W.keepArmWitness A j P),
    W.armMean_eq_mean A j P, MAR.keepArmLaw_measure]
  change (∫ o, (W.b ∘ Prod.fst) o ∂(P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)).map
    (MAR.keepArm A.d j)) = _
  rw [integral_map (MAR.keepArm_measurable A.d j).aemeasurable
      (W.measurableB.comp measurable_fst).aestronglyMeasurable]
  rfl

theorem keepArm_risk_transfer (A : Model.Parameters) (j : Bool) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (MAR.armMean A.d j) (armClass A j) t ≤
      Model.minimaxTail n (SeparatedMAR.target A.d) (SeparatedMAR.modelClass A) t ∧
    Model.minimaxRMSE n (MAR.armMean A.d j) (armClass A j) ≤
      Model.minimaxRMSE n (SeparatedMAR.target A.d) (SeparatedMAR.modelClass A) := by
  apply Model.kernel_reduction n (MAR.keepArmKernel A.d j) (MAR.armMean A.d j)
    (SeparatedMAR.target A.d) (armClass A j) (SeparatedMAR.modelClass A)
  · rintro P ⟨W⟩
    rw [MAR.keepArmKernel_law]
    exact ⟨W.keepArmWitness A j P⟩
  · rintro P ⟨W⟩
    rw [MAR.keepArmKernel_law]
    exact keepArm_target_eq_armMean A j P W



/-- The literal separated treatment class shares one propensity and one design
 density while allowing distinct arm regression indices. -/
structure Witness (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) where
  p : Model.Covariate A.d → ℝ
  w : Model.Covariate A.d → ℝ
  b0 : Model.Covariate A.d → ℝ
  b1 : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableB0 : Measurable b0
  measurableB1 : Measurable b1
  nonnegativeP : 0 ≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse)).map Prod.fst =
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  momentD0 : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))[
    MAR.armIndicator false ∘ Prod.snd | Model.covariateInformation A MAR.TreatmentResponse] =ᵐ[
      (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))] fun o => 1-w o.1
  momentD1 : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))[
    MAR.armIndicator true ∘ Prod.snd | Model.covariateInformation A MAR.TreatmentResponse] =ᵐ[
      (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))] w ∘ Prod.fst
  momentV0 : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))[
    MAR.armOutcome false ∘ Prod.snd | Model.covariateInformation A MAR.TreatmentResponse] =ᵐ[
      (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))] fun o => (1-w o.1)*b0 o.1
  momentV1 : (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))[
    MAR.armOutcome true ∘ Prod.snd | Model.covariateInformation A MAR.TreatmentResponse] =ᵐ[
      (P : Measure (Model.Covariate A.d × MAR.TreatmentResponse))] fun o => w o.1*b1 o.1
  overlap : ∀ᵐ x ∂Model.cubeVolume A.d, A.δ≤w x ∧ w x≤1-A.δ
  smoothW : w ∈ Model.holderBall A.α A.H
  smoothB0 : b0 ∈ Model.holderBall A.β A.H
  smoothB1 : b1 ∈ Model.holderBall β1 A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d, A.gminus≤p x ∧ p x≤A.gplus

def modelClass (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1) :
    Set (ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) :=
  {P | Nonempty (Witness A β1 hβ1 P)}

/-- This radius increase is only used in the pilot representation; the class
itself retains the source radius H. -/
def armParameters (A : Model.Parameters) (β : ℝ) (hβ : 0<β) : Model.Parameters :=
  {A with β := β, hβ := hβ, H := A.H+1, hH := by linarith [A.hH]}

def Witness.controlArm (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (W : Witness A β1 hβ1 P) : ArmWitness (armParameters A A.β A.hβ) false P where
  p := W.p
  w x := 1-W.w x
  b := W.b0
  measurableP := W.measurableP
  measurableW := measurable_const.sub W.measurableW
  measurableB := W.measurableB0
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentD := W.momentD0
  momentV := W.momentV0
  overlap := by
    change ∀ᵐ x ∂Model.cubeVolume A.d, A.δ≤1-W.w x ∧ 1-W.w x≤1-A.δ
    exact W.overlap.mono (fun x hx => ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  smoothW := Model.holderBall_complement_finite W.w A.α A.H A.hα A.hH.le W.smoothW
  smoothB := W.smoothB0.trans (ENNReal.ofReal_le_ofReal (by linarith : A.H≤A.H+1))
  densityBounds := W.densityBounds

def Witness.treatedArm (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (W : Witness A β1 hβ1 P) : ArmWitness (armParameters A β1 hβ1) true P where
  p := W.p
  w := W.w
  b := W.b1
  measurableP := W.measurableP
  measurableW := W.measurableW
  measurableB := W.measurableB1
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentD := W.momentD1
  momentV := W.momentV1
  overlap := W.overlap
  smoothW := W.smoothW.trans (ENNReal.ofReal_le_ofReal (by linarith : A.H≤A.H+1))
  smoothB := W.smoothB1.trans (ENNReal.ofReal_le_ofReal (by linarith : A.H≤A.H+1))
  densityBounds := W.densityBounds

theorem modelClass_subset_control (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1) :
    modelClass A β1 hβ1 ⊆ armClass (armParameters A A.β A.hβ) false := by
  rintro P ⟨W⟩
  exact ⟨W.controlArm A β1 hβ1 P⟩

theorem modelClass_subset_treated (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1) :
    modelClass A β1 hβ1 ⊆ armClass (armParameters A β1 hβ1) true := by
  rintro P ⟨W⟩
  exact ⟨W.treatedArm A β1 hβ1 P⟩

end RoughRegime.Applications.SeparatedTreatment
