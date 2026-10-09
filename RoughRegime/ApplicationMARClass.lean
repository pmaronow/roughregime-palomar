module

public import RoughRegime.ApplicationMAR
public import RoughRegime.HolderConstants


@[expose] public section
/-! Faithful missing-data class membership and keep-arm reductions. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.MAR

def observables (A : Model.Parameters) (hM : 1 ≤ A.M0) : Model.Observables Response A where
  D := observed
  U _ := 1
  V := observedOutcome
  W _ := 0
  lam := 1
  hlam := one_ne_zero
  measurableD := observed_measurable
  measurableU := measurable_const
  measurableV := observedOutcome_measurable
  measurableW := measurable_const
  boundD z := ⟨(observed_range z).1, (observed_range z).2.trans hM⟩
  boundU _ := by simpa using hM
  boundV z := by
    rw [abs_of_nonneg (observedOutcome_range z).1]
    exact (observedOutcome_range z).2.trans hM
  boundW := ⟨0, le_rfl, fun _ => by simp⟩

/-- The paper's MAR restrictions are expressed through actual conditional means.
The reciprocal propensity is the literal pointwise reciprocal. -/
structure Witness (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) where
  p : Model.Covariate A.d → ℝ
  w : Model.Covariate A.d → ℝ
  b : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableB : Measurable b
  nonnegativeP : 0 ≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P : Measure (Model.Covariate A.d × Response)).map Prod.fst =
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  momentD : (P : Measure (Model.Covariate A.d × Response))[observed ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
    (P : Measure (Model.Covariate A.d × Response))] w ∘ Prod.fst
  momentV : (P : Measure (Model.Covariate A.d × Response))[observedOutcome ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
    (P : Measure (Model.Covariate A.d × Response))] fun o => w o.1 * b o.1
  overlap : ∀ᵐ x ∂Model.cubeVolume A.d, A.δ ≤ w x ∧ w x ≤ 1 - A.δ
  smoothInverse : (fun x => (w x)⁻¹) ∈ Model.holderBall A.α A.H
  smoothB : b ∈ Model.holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d,
    A.gminus ≤ w x * p x ∧ w x * p x ≤ A.gplus

def modelClass (A : Model.Parameters) : Set (ProbabilityMeasure (Model.Covariate A.d × Response)) :=
  {P | Nonempty (Witness A P)}

def Witness.toModel (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P) :
    Model.ModelWitness A (observables A hM) P where
  p := h.p
  w := h.w
  a x := (h.w x)⁻¹
  b := h.b
  measurableP := h.measurableP
  measurableW := h.measurableW
  measurableA := h.measurableW.inv
  measurableB := h.measurableB
  nonnegativeP := h.nonnegativeP
  marginal := h.marginal
  momentD := h.momentD
  momentU := by
    have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
        (inferInstance : MeasurableSpace (Model.Covariate A.d × Response)) := measurable_fst.comap_le
    have hw : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)), A.δ ≤ h.w o.1 := by
      apply ae_of_ae_map (μ := (P : Measure (Model.Covariate A.d × Response)))
        (f := Prod.fst) (p := fun x => A.δ ≤ h.w x) measurable_fst.aemeasurable
      rw [h.marginal]
      exact (h.overlap.mono (fun x hx => hx.1)).filter_mono
        (withDensity_absolutelyContinuous _ _).ae_le
    change (P : Measure (Model.Covariate A.d × Response))[fun _ => (1 : ℝ) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      (P : Measure (Model.Covariate A.d × Response))] fun o => h.w o.1 * (h.w o.1)⁻¹
    rw [condExp_const hm]
    filter_upwards [hw] with o ho
    exact (mul_inv_cancel₀ (ne_of_gt (A.hδ.trans_le ho))).symm
  momentV := h.momentV
  overlap := h.overlap.mono (fun x hx => hx.1)
  smoothA := h.smoothInverse
  smoothB := h.smoothB
  densityBounds := h.densityBounds

theorem modelClass_subset_generic (A : Model.Parameters) (hM : 1 ≤ A.M0) :
    modelClass A ⊆ Model.modelClass A (observables A hM) := by
  rintro P ⟨h⟩
  exact ⟨h.toModel A hM P⟩

/-- The generic target is exactly the paper's MAR mean on the actual law. -/
theorem target_eq_mean (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P) :
    Model.target A (observables A hM) P = ∫ o, h.b o.1 ∂(P : Measure (Model.Covariate A.d × Response)) := by
  rw [Model.target_weighted_representation A (observables A hM) P (h.toModel A hM P),
    Model.marginal_integral A (observables A hM) P (h.toModel A hM P) h.b h.measurableB]
  simp only [observables, Witness.toModel, integral_zero, zero_add, one_mul]
  apply integral_congr_ae
  filter_upwards [h.overlap] with x hx
  have hw : h.w x ≠ 0 := ne_of_gt (A.hδ.trans_le hx.1)
  field_simp

/-- A treatment arm's actual source restrictions, before the keep-arm map. -/
structure ArmWitness (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) where
  p : Model.Covariate A.d → ℝ
  w : Model.Covariate A.d → ℝ
  b : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableB : Measurable b
  nonnegativeP : 0 ≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P : Measure (Model.Covariate A.d × TreatmentResponse)).map Prod.fst =
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  momentD : (P : Measure (Model.Covariate A.d × TreatmentResponse))[armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
    (P : Measure (Model.Covariate A.d × TreatmentResponse))] w ∘ Prod.fst
  momentV : (P : Measure (Model.Covariate A.d × TreatmentResponse))[armOutcome j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
    (P : Measure (Model.Covariate A.d × TreatmentResponse))] fun o => w o.1 * b o.1
  overlap : ∀ᵐ x ∂Model.cubeVolume A.d, A.δ ≤ w x ∧ w x ≤ 1 - A.δ
  smoothInverse : (fun x => (w x)⁻¹) ∈ Model.holderBall A.α A.H
  smoothB : b ∈ Model.holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d,
    A.gminus ≤ w x * p x ∧ w x * p x ≤ A.gplus

def keepArmLaw (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) :
    ProbabilityMeasure (Model.Covariate A.d × Response) := P.map (keepArm A.d j)

lemma keepArmLaw_measure (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) :
    (keepArmLaw A j P : Measure (Model.Covariate A.d × Response)) = (P : Measure (Model.Covariate A.d × TreatmentResponse)).map (keepArm A.d j) :=
  rfl

def ArmWitness.keepArmWitness (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    Witness A (keepArmLaw A j P) where
  p := h.p
  w := h.w
  b := h.b
  measurableP := h.measurableP
  measurableW := h.measurableW
  measurableB := h.measurableB
  nonnegativeP := h.nonnegativeP
  marginal := by
    rw [keepArmLaw_measure, Measure.map_map measurable_fst (keepArm_measurable A.d j)]
    exact h.marginal
  momentD := by
    rw [keepArmLaw_measure]
    apply keepArm_conditional A.d j (P : Measure (Model.Covariate A.d × TreatmentResponse)) observed observed_measurable h.w h.measurableW
    · apply Integrable.of_mem_Icc 0 1
      · exact (observed_measurable.comp ((keepArmResponse_measurable j).comp measurable_snd)).aemeasurable
      · exact Filter.Eventually.of_forall (fun o => observed_range (keepArmResponse j o.2))
    · have hf : (fun o : Model.Covariate A.d × TreatmentResponse =>
          observed (keepArmResponse j o.2)) = armIndicator j ∘ Prod.snd :=
        funext (fun o => (keepArmResponse_moments j o.2).1)
      rw [hf]
      exact h.momentD
  momentV := by
    rw [keepArmLaw_measure]
    apply keepArm_conditional A.d j (P : Measure (Model.Covariate A.d × TreatmentResponse)) observedOutcome observedOutcome_measurable
      (fun x => h.w x * h.b x) (h.measurableW.mul h.measurableB)
    · apply Integrable.of_mem_Icc 0 1
      · exact (observedOutcome_measurable.comp
          ((keepArmResponse_measurable j).comp measurable_snd)).aemeasurable
      · exact Filter.Eventually.of_forall (fun o => observedOutcome_range (keepArmResponse j o.2))
    · have hf : (fun o : Model.Covariate A.d × TreatmentResponse =>
          observedOutcome (keepArmResponse j o.2)) = armOutcome j ∘ Prod.snd :=
        funext (fun o => (keepArmResponse_moments j o.2).2)
      rw [hf]
      exact h.momentV
  overlap := h.overlap
  smoothInverse := h.smoothInverse
  smoothB := h.smoothB
  densityBounds := h.densityBounds

theorem keepArm_mem_generic (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    keepArmLaw A j P ∈ Model.modelClass A (observables A hM) :=
  ⟨(h.keepArmWitness A j P).toModel A hM _⟩

theorem keepArm_target_eq_arm_mean (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    Model.target A (observables A hM) (keepArmLaw A j P) = ∫ o, h.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)) := by
  rw [target_eq_mean A hM _ (h.keepArmWitness A j P), keepArmLaw_measure,
    show (h.keepArmWitness A j P).b = h.b from rfl]
  change (∫ o, (h.b ∘ Prod.fst) o ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)).map
    (keepArm A.d j)) = _
  rw [integral_map (keepArm_measurable A.d j).aemeasurable
      (h.measurableB.comp measurable_fst).aestronglyMeasurable]
  rfl

def augmentationLaw (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) :
    ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse) := by
  have : IsMarkovKernel (augmentationKernel A.d j) := augmentationKernel_markov A.d j
  exact (augmentationKernel A.d j ∘ₘ (P : Measure (Model.Covariate A.d × Response))).toProbabilityMeasure

lemma augmentationLaw_measure (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) :
    (augmentationLaw A j P : Measure (Model.Covariate A.d × TreatmentResponse)) =
      augmentationKernel A.d j ∘ₘ (P : Measure (Model.Covariate A.d × Response)) := rfl

def Witness.augmentationSelectedWitness (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P) :
    ArmWitness A j (augmentationLaw A j P) where
  p := h.p
  w := h.w
  b := h.b
  measurableP := h.measurableP
  measurableW := h.measurableW
  measurableB := h.measurableB
  nonnegativeP := h.nonnegativeP
  marginal := by rw [augmentationLaw_measure, augmentation_marginal]; exact h.marginal
  momentD := by
    rw [augmentationLaw_measure]
    exact (augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d × Response)) h.w h.b
      h.measurableW h.measurableB h.momentD h.momentV).1
  momentV := by
    rw [augmentationLaw_measure]
    exact (augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d × Response)) h.w h.b
      h.measurableW h.measurableB h.momentD h.momentV).2.1
  overlap := h.overlap
  smoothInverse := h.smoothInverse
  smoothB := h.smoothB
  densityBounds := h.densityBounds

/-- The additional reciprocal and weighted-density restrictions for the other
arm are the source's explicit treatment class restrictions. -/
def Witness.augmentationOtherWitness (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P)
    (hH : 1 / 2 ≤ A.H)
    (hInv : (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H)
    (hDensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus) :
    ArmWitness A (!j) (augmentationLaw A j P) where
  p := h.p
  w x := 1 - h.w x
  b _ := 1 / 2
  measurableP := h.measurableP
  measurableW := measurable_const.sub h.measurableW
  measurableB := measurable_const
  nonnegativeP := h.nonnegativeP
  marginal := by rw [augmentationLaw_measure, augmentation_marginal]; exact h.marginal
  momentD := by
    rw [augmentationLaw_measure]
    simpa only [Function.comp_def] using
      (augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d × Response)) h.w h.b
        h.measurableW h.measurableB h.momentD h.momentV).2.2.1
  momentV := by
    rw [augmentationLaw_measure]
    simpa only [div_eq_mul_inv, one_mul] using
      (augmentation_conditional_moments A.d j (P : Measure (Model.Covariate A.d × Response)) h.w h.b
        h.measurableW h.measurableB h.momentD h.momentV).2.2.2
  overlap := h.overlap.mono (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  smoothInverse := hInv
  smoothB := Model.const_mem_holderBall A.hβ (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hH)
  densityBounds := hDensity

def armMean (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) : ℝ :=
  ∫ o, ((P : Measure (Model.Covariate d × TreatmentResponse))[
      armOutcome j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o /
    ((P : Measure (Model.Covariate d × TreatmentResponse))[
      armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o
    ∂(P : Measure (Model.Covariate d × TreatmentResponse))

theorem armMean_eq_mean (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    armMean A.d j P = ∫ o, h.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)) := by
  have hw : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)), A.δ ≤ h.w o.1 := by
    apply ae_of_ae_map (μ := (P : Measure (Model.Covariate A.d × TreatmentResponse)))
      (f := Prod.fst) (p := fun x => A.δ ≤ h.w x) measurable_fst.aemeasurable
    rw [h.marginal]
    exact (h.overlap.mono (fun x hx => hx.1)).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  apply integral_congr_ae
  filter_upwards [h.momentD, h.momentV, hw] with o hD hV ho
  dsimp only [Function.comp_apply] at hD
  rw [hD, hV]
  exact mul_div_cancel_left₀ _ (ne_of_gt (A.hδ.trans_le ho))

theorem keepArm_target_eq_armMean (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    Model.target A (observables A hM) (keepArmLaw A j P) = armMean A.d j P := by
  rw [keepArm_target_eq_arm_mean A hM j P h, armMean_eq_mean A j P h]

theorem augmentation_selected_armMean (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P) :
    armMean A.d j (augmentationLaw A j P) = Model.target A (observables A hM) P := by
  rw [armMean_eq_mean A j _ (h.augmentationSelectedWitness A j P),
    target_eq_mean A hM P h, augmentationLaw_measure, augmentationKernel_law]
  change (∫ o, (h.b ∘ Prod.fst) o ∂((P : Measure (Model.Covariate A.d × Response)).prod
    (fairCoin : Measure Bool)).map (augment A.d j)) = _
  rw [integral_map (augment_measurable A.d j).aemeasurable
    (h.measurableB.comp measurable_fst).aestronglyMeasurable]
  change (∫ o, (h.b ∘ Prod.fst) o.1 ∂(P : Measure (Model.Covariate A.d × Response)).prod
    (fairCoin : Measure Bool)) = _
  rw [integral_fun_fst]
  simp only [probReal_univ, one_smul, Function.comp_def]

theorem augmentation_other_armMean (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P)
    (hH : 1 / 2 ≤ A.H)
    (hInv : (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H)
    (hDensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus) :
    armMean A.d (!j) (augmentationLaw A j P) = 1 / 2 := by
  rw [armMean_eq_mean A (!j) _ (h.augmentationOtherWitness A j P hH hInv hDensity)]
  change (∫ _o : Model.Covariate A.d × TreatmentResponse, (1 / 2 : ℝ)
    ∂(augmentationLaw A j P : Measure (Model.Covariate A.d × TreatmentResponse))) = _
  simp only [integral_const, probReal_univ, one_smul]

def ate (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) : ℝ :=
  armMean d true P - armMean d false P

def armSign (j : Bool) : ℝ := if j then 1 else -1

/-- The source's ATE kernel identity follows from actual conditional moments. -/
theorem augmentation_ate (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P)
    (hH : 1 / 2 ≤ A.H)
    (hInv : (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H)
    (hDensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus) :
    ate A.d (augmentationLaw A j P) = armSign j * (Model.target A (observables A hM) P - 1 / 2) := by
  have hj := augmentation_selected_armMean A hM j P h
  have ho := augmentation_other_armMean A j P h hH hInv hDensity
  cases j
  · simp only [Bool.not_false] at ho
    simp [ate, armSign, hj, ho]
  · simp only [Bool.not_true] at ho
    simp [ate, armSign, hj, ho]

def keepArmKernel (d : ℕ) (j : Bool) :
    Kernel (Model.Covariate d × TreatmentResponse) (Model.Covariate d × Response) :=
  Kernel.deterministic (keepArm d j) (keepArm_measurable d j)

instance keepArmKernel_markov (d : ℕ) (j : Bool) : IsMarkovKernel (keepArmKernel d j) :=
  inferInstanceAs (IsMarkovKernel (Kernel.deterministic (keepArm d j) (keepArm_measurable d j)))

lemma keepArmKernel_law (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) :
    Model.kernelLaw (keepArmKernel A.d j) P = keepArmLaw A j P := by
  apply Subtype.ext
  change keepArmKernel A.d j ∘ₘ (P : Measure (Model.Covariate A.d × TreatmentResponse)) =
    (P : Measure (Model.Covariate A.d × TreatmentResponse)).map (keepArm A.d j)
  exact Measure.deterministic_comp_eq_map (keepArm_measurable A.d j)

def armClass (A : Model.Parameters) (j : Bool) :
    Set (ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) := {P | Nonempty (ArmWitness A j P)}

/-- The genuine keep-arm kernel transfers both minimax tail and RMSE bounds
from the generic MAR class to the treatment arm's class. -/
theorem keepArm_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool)
    (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (armMean A.d j) (armClass A j) t ≤
      Model.minimaxTail n (Model.target A (observables A hM))
        (Model.modelClass A (observables A hM)) t ∧
    Model.minimaxRMSE n (armMean A.d j) (armClass A j) ≤
      Model.minimaxRMSE n (Model.target A (observables A hM))
        (Model.modelClass A (observables A hM)) := by
  apply Model.kernel_reduction n (keepArmKernel A.d j) (armMean A.d j)
    (Model.target A (observables A hM)) (armClass A j) (Model.modelClass A (observables A hM))
  · rintro P ⟨h⟩
    rw [keepArmKernel_law]
    exact keepArm_mem_generic A hM j P h
  · rintro P ⟨h⟩
    rw [keepArmKernel_law]
    exact keepArm_target_eq_armMean A hM j P h

end RoughRegime.Applications.MAR
