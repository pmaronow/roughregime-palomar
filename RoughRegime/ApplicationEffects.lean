module

public import RoughRegime.ApplicationMARClass
public import RoughRegime.Conditional


@[expose] public section
/-! Treatment effects and observable-mean identities on actual probability laws. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR

abbrev parametersWithBeta (A : Model.Parameters) (β : ℝ) (hβ : 0 < β) : Model.Parameters :=
  { A with β := β, hβ := hβ }

/-- The treatment class retains the two source regression smoothness indices. -/
def treatmentClass (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1) :
    Set (ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) :=
  armClass A false ∩ armClass (parametersWithBeta A β1 hβ1) true

def Witness.augmentationOtherWitnessBeta (A : Model.Parameters) (β : ℝ) (hβ : 0 < β) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P)
    (hH : 1 / 2 ≤ A.H)
    (hInv : (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H)
    (hDensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus) :
    ArmWitness (parametersWithBeta A β hβ) (!j) (augmentationLaw A j P) := by
  let h' := h.augmentationOtherWitness A j P hH hInv hDensity
  exact {
    p := h'.p
    w := h'.w
    b := h'.b
    measurableP := h'.measurableP
    measurableW := h'.measurableW
    measurableB := h'.measurableB
    nonnegativeP := h'.nonnegativeP
    marginal := h'.marginal
    momentD := h'.momentD
    momentV := h'.momentV
    overlap := h'.overlap
    smoothInverse := h'.smoothInverse
    smoothB := by
      change (fun _ : Model.Covariate A.d => (1 / 2 : ℝ)) ∈ Model.holderBall β A.H
      apply Model.const_mem_holderBall hβ
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hH
    densityBounds := h'.densityBounds }

theorem augmentation_false_mem_treatmentClass (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P)
    (hH : 1 / 2 ≤ A.H)
    (hInv : (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H)
    (hDensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus) :
    augmentationLaw A false P ∈ treatmentClass A β1 hβ1 :=
  ⟨⟨h.augmentationSelectedWitness A false P⟩,
    ⟨h.augmentationOtherWitnessBeta A β1 hβ1 false P hH hInv hDensity⟩⟩

theorem augmentation_true_mem_treatmentClass (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response))
    (h : Witness (parametersWithBeta A β1 hβ1) P)
    (hH : 1 / 2 ≤ A.H)
    (hInv : (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H)
    (hDensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus) :
    augmentationLaw (parametersWithBeta A β1 hβ1) true P ∈ treatmentClass A β1 hβ1 := by
  exact ⟨⟨h.augmentationOtherWitnessBeta (parametersWithBeta A β1 hβ1) A.β A.hβ
      true P hH hInv hDensity⟩,
    ⟨h.augmentationSelectedWitness (parametersWithBeta A β1 hβ1) true P⟩⟩

def regression (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse))
    (o : Model.Covariate d × TreatmentResponse) : ℝ :=
  ((P : Measure (Model.Covariate d × TreatmentResponse))[
    armOutcome j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o /
  ((P : Measure (Model.Covariate d × TreatmentResponse))[
    armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]) o

def armProbability (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) : ℝ :=
  ∫ o, armIndicator j o.2 ∂(P : Measure (Model.Covariate d × TreatmentResponse))

/-- The literal conditional average treatment effect in the indicated arm. -/
def conditionalEffect (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) : ℝ :=
  (∫ o, armIndicator j o.2 * (regression d true P o - regression d false P o)
    ∂(P : Measure (Model.Covariate d × TreatmentResponse))) / armProbability d j P

abbrev att (d : ℕ) := conditionalEffect d true
abbrev atu (d : ℕ) := conditionalEffect d false

lemma armIndicator_range (j : Bool) (z : TreatmentResponse) : armIndicator j z ∈ Icc (0 : ℝ) 1 := by
  unfold armIndicator
  split_ifs <;> norm_num

lemma armOutcome_range (j : Bool) (z : TreatmentResponse) : armOutcome j z ∈ Icc (0 : ℝ) 1 := by
  unfold armOutcome armIndicator
  split_ifs
  · simpa only [one_mul] using z.2.property
  · norm_num

lemma armOutcome_le_indicator (j : Bool) (z : TreatmentResponse) : armOutcome j z ≤ armIndicator j z := by
  unfold armOutcome armIndicator
  split_ifs
  · simpa only [one_mul] using z.2.property.2
  · norm_num

lemma ArmWitness.overlap_on_observations (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)),
      A.δ ≤ h.w o.1 ∧ h.w o.1 ≤ 1 - A.δ := by
  apply ae_of_ae_map (μ := (P : Measure (Model.Covariate A.d × TreatmentResponse)))
    (f := Prod.fst) (p := fun x => A.δ ≤ h.w x ∧ h.w x ≤ 1 - A.δ) measurable_fst.aemeasurable
  rw [h.marginal]
  exact h.overlap.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

lemma ArmWitness.regression_eq (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    regression A.d j P =ᵐ[(P : Measure (Model.Covariate A.d × TreatmentResponse))] h.b ∘ Prod.fst := by
  filter_upwards [h.momentD, h.momentV, h.overlap_on_observations A j P] with o hD hV hw
  dsimp only [regression, Function.comp_apply] at hD ⊢
  rw [hD, hV]
  exact mul_div_cancel_left₀ _ (ne_of_gt (A.hδ.trans_le hw.1))

lemma ArmWitness.regression_range (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)), h.b o.1 ∈ Icc (0 : ℝ) 1 := by
  let μ := (P : Measure (Model.Covariate A.d × TreatmentResponse))
  have hDi : Integrable (armIndicator j ∘ Prod.snd) μ := Integrable.of_mem_Icc 0 1
    ((armIndicator_measurable j).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => armIndicator_range j o.2))
  have hVi : Integrable (armOutcome j ∘ Prod.snd) μ := Integrable.of_mem_Icc 0 1
    ((armOutcome_measurable j).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => armOutcome_range j o.2))
  have hn := condExp_nonneg (m := MeasurableSpace.comap Prod.fst inferInstance)
    (μ := μ) (f := armOutcome j ∘ Prod.snd)
    (Filter.Eventually.of_forall (fun o => (armOutcome_range j o.2).1))
  have hc := condExp_mono (m := MeasurableSpace.comap Prod.fst inferInstance) hVi hDi
    (Filter.Eventually.of_forall (fun o => armOutcome_le_indicator j o.2))
  filter_upwards [hn, hc, h.momentD, h.momentV, h.overlap_on_observations A j P]
    with o hnon hle hD hV hw
  dsimp only [Function.comp_apply] at hD
  rw [hD, hV] at hle
  rw [hV] at hnon
  change 0 ≤ h.w o.1 * h.b o.1 at hnon
  have hwpos := A.hδ.trans_le hw.1
  exact ⟨by nlinarith, by nlinarith⟩

lemma ArmWitness.b_integrable (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    Integrable (h.b ∘ Prod.fst) (P : Measure (Model.Covariate A.d × TreatmentResponse)) :=
  Integrable.of_mem_Icc 0 1 (h.measurableB.comp measurable_fst).aemeasurable
    (h.regression_range A j P)

lemma ArmWitness.weighted_b_integrable (A : Model.Parameters) (j r : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    Integrable (fun o => armIndicator r o.2 * h.b o.1)
      (P : Measure (Model.Covariate A.d × TreatmentResponse)) := by
  apply Integrable.of_mem_Icc 0 1
    (((armIndicator_measurable r).comp measurable_snd).mul
      (h.measurableB.comp measurable_fst)).aemeasurable
  filter_upwards [h.regression_range A j P] with o ho
  exact ⟨mul_nonneg (armIndicator_range r o.2).1 ho.1,
    (mul_le_mul (armIndicator_range r o.2).2 ho.2 ho.1 (by norm_num)).trans_eq (by norm_num)⟩

lemma armIndicator_partition (z : TreatmentResponse) :
    armIndicator true z + armIndicator false z = 1 := by
  rcases z with ⟨a, y⟩
  cases a <;> norm_num [armIndicator]

lemma armOutcome_partition (z : TreatmentResponse) :
    armOutcome true z + armOutcome false z = z.2 := by
  unfold armOutcome
  rw [← add_mul, armIndicator_partition, one_mul]

lemma armIndicator_integrable (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) :
    Integrable (armIndicator j ∘ Prod.snd) (P : Measure (Model.Covariate d × TreatmentResponse)) :=
  Integrable.of_mem_Icc 0 1 ((armIndicator_measurable j).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => armIndicator_range j o.2))

lemma armOutcome_integrable (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) :
    Integrable (armOutcome j ∘ Prod.snd) (P : Measure (Model.Covariate d × TreatmentResponse)) :=
  Integrable.of_mem_Icc 0 1 ((armOutcome_measurable j).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => armOutcome_range j o.2))

theorem armProbability_complement (d : ℕ)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) :
    armProbability d false P = 1 - armProbability d true P := by
  have hs : armProbability d true P + armProbability d false P = 1 := by
    unfold armProbability
    rw [← integral_add (f := fun o : Model.Covariate d × TreatmentResponse => armIndicator true o.2)
      (g := fun o : Model.Covariate d × TreatmentResponse => armIndicator false o.2)
      (armIndicator_integrable d true P) (armIndicator_integrable d false P)]
    simp only [armIndicator_partition, integral_const, probReal_univ, one_smul]
  linarith

lemma ArmWitness.integral_outcome_eq_weighted_b (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    (∫ o, armOutcome j o.2 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) =
      ∫ o, armIndicator j o.2 * h.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)) := by
  have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace (Model.Covariate A.d × TreatmentResponse)) := measurable_fst.comap_le
  have hbm : @StronglyMeasurable (Model.Covariate A.d × TreatmentResponse) ℝ
      inferInstance (MeasurableSpace.comap Prod.fst inferInstance) (h.b ∘ Prod.fst) :=
    (h.measurableB.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hp := RoughRegime.Conditional.integral_mul_condExp hm (armIndicator j ∘ Prod.snd)
    (h.b ∘ Prod.fst) (armIndicator_integrable A.d j P) hbm (h.weighted_b_integrable A j j P)
  calc
    _ = ∫ o, (P : Measure (Model.Covariate A.d × TreatmentResponse))[
        armOutcome j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o
        ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)) :=
      (integral_condExp hm).symm
    _ = ∫ o, (P : Measure (Model.Covariate A.d × TreatmentResponse))[
        armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o * h.b o.1
        ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)) := by
      apply integral_congr_ae
      filter_upwards [h.momentD, h.momentV] with o hD hV
      exact hV.trans (by rw [hD]; rfl)
    _ = _ := hp.symm

theorem expected_outcome_decomposition (A : Model.Parameters) {β1 : ℝ} {hβ1 : 0 < β1}
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (h0 : ArmWitness A false P) (h1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    (∫ o, (o.2.2 : ℝ) ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) =
      (∫ o, armIndicator true o.2 * h1.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) +
      (∫ o, armIndicator false o.2 * h0.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) := by
  rw [← h1.integral_outcome_eq_weighted_b (parametersWithBeta A β1 hβ1) true P, ← h0.integral_outcome_eq_weighted_b A false P,
    ← integral_add (f := fun o : Model.Covariate A.d × TreatmentResponse => armOutcome true o.2)
      (g := fun o : Model.Covariate A.d × TreatmentResponse => armOutcome false o.2)
      (armOutcome_integrable A.d true P) (armOutcome_integrable A.d false P)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun o => (armOutcome_partition o.2).symm))

lemma ArmWitness.integral_b_decomposition (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    (∫ o, h.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) =
      (∫ o, armIndicator true o.2 * h.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) +
      (∫ o, armIndicator false o.2 * h.b o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) := by
  rw [← integral_add (h.weighted_b_integrable A j true P) (h.weighted_b_integrable A j false P)]
  apply integral_congr_ae
  filter_upwards [] with o
  rw [← add_mul, armIndicator_partition, one_mul]

theorem att_observable_identity (A : Model.Parameters) {β1 : ℝ} {hβ1 : 0 < β1}
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (h0 : ArmWitness A false P) (h1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    att A.d P =
      ((∫ o, (o.2.2 : ℝ) ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) -
        armMean A.d false P) / armProbability A.d true P := by
  unfold att conditionalEffect
  congr 1
  have he : (∫ o, armIndicator true o.2 * (regression A.d true P o - regression A.d false P o)
      ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) =
      (∫ o, armIndicator true o.2 * (h1.b o.1 - h0.b o.1)
        ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) := by
    apply integral_congr_ae
    filter_upwards [h0.regression_eq A false P, h1.regression_eq (parametersWithBeta A β1 hβ1) true P] with o h0o h1o
    simp only [Function.comp_apply] at h0o h1o
    rw [h0o, h1o]
  rw [he, armMean_eq_mean A false P h0, expected_outcome_decomposition A P h0 h1,
    h0.integral_b_decomposition A false P]
  simp only [mul_sub]
  rw [integral_sub (h1.weighted_b_integrable (parametersWithBeta A β1 hβ1) true true P) (h0.weighted_b_integrable A false true P)]
  ring

theorem atu_observable_identity (A : Model.Parameters) {β1 : ℝ} {hβ1 : 0 < β1}
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (h0 : ArmWitness A false P) (h1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    atu A.d P =
      (armMean A.d true P -
        (∫ o, (o.2.2 : ℝ) ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)))) /
        (1 - armProbability A.d true P) := by
  unfold atu conditionalEffect
  rw [armProbability_complement]
  congr 1
  have he : (∫ o, armIndicator false o.2 * (regression A.d true P o - regression A.d false P o)
      ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) =
      (∫ o, armIndicator false o.2 * (h1.b o.1 - h0.b o.1)
        ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) := by
    apply integral_congr_ae
    filter_upwards [h0.regression_eq A false P, h1.regression_eq (parametersWithBeta A β1 hβ1) true P] with o h0o h1o
    simp only [Function.comp_apply] at h0o h1o
    rw [h0o, h1o]
  rw [he, armMean_eq_mean (parametersWithBeta A β1 hβ1) true P h1, expected_outcome_decomposition A P h0 h1,
    h1.integral_b_decomposition (parametersWithBeta A β1 hβ1) true P]
  simp only [mul_sub]
  rw [integral_sub (h1.weighted_b_integrable (parametersWithBeta A β1 hβ1) true false P) (h0.weighted_b_integrable A false false P)]
  ring

lemma ArmWitness.armProbability_eq_mean (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    armProbability A.d j P = ∫ o, h.w o.1 ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)) := by
  unfold armProbability
  calc
    _ = ∫ o, (P : Measure (Model.Covariate A.d × TreatmentResponse))[
        armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o
        ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)) :=
      (integral_condExp measurable_fst.comap_le).symm
    _ = _ := integral_congr_ae h.momentD

theorem armProbability_range (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    armProbability A.d j P ∈ Icc A.δ (1 - A.δ) := by
  have hi : Integrable (h.w ∘ Prod.fst) (P : Measure (Model.Covariate A.d × TreatmentResponse)) :=
    integrable_condExp.congr h.momentD
  have hlo := integral_mono_ae (integrable_const A.δ) hi
    ((h.overlap_on_observations A j P).mono (fun o ho => ho.1))
  have hhi := integral_mono_ae hi (integrable_const (1 - A.δ))
    ((h.overlap_on_observations A j P).mono (fun o ho => ho.2))
  rw [h.armProbability_eq_mean A j P]
  exact ⟨by simpa only [integral_const, probReal_univ, one_smul, Function.comp_def] using hlo,
    by simpa only [integral_const, probReal_univ, one_smul, Function.comp_def] using hhi⟩

theorem armMean_range (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) (h : ArmWitness A j P) :
    armMean A.d j P ∈ Icc (0 : ℝ) 1 := by
  rw [armMean_eq_mean A j P h]
  have hlo := integral_mono_ae (integrable_const (0 : ℝ)) (h.b_integrable A j P)
    ((h.regression_range A j P).mono (fun o ho => ho.1))
  have hhi := integral_mono_ae (h.b_integrable A j P) (integrable_const (1 : ℝ))
    ((h.regression_range A j P).mono (fun o ho => ho.2))
  exact ⟨by simpa only [integral_const, probReal_univ, one_smul, Function.comp_def] using hlo,
    by simpa only [integral_const, probReal_univ, one_smul, Function.comp_def] using hhi⟩

theorem att_reverse_identity (A : Model.Parameters) {β1 : ℝ} {hβ1 : 0 < β1}
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (h0 : ArmWitness A false P) (h1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    armMean A.d false P =
      (∫ o, (o.2.2 : ℝ) ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) -
        armProbability A.d true P * att A.d P := by
  rw [att_observable_identity A P h0 h1]
  have hp : armProbability A.d true P ≠ 0 := ne_of_gt (A.hδ.trans_le (armProbability_range (parametersWithBeta A β1 hβ1) true P h1).1)
  field_simp
  ring

theorem atu_reverse_identity (A : Model.Parameters) {β1 : ℝ} {hβ1 : 0 < β1}
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (h0 : ArmWitness A false P) (h1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    armMean A.d true P =
      (∫ o, (o.2.2 : ℝ) ∂(P : Measure (Model.Covariate A.d × TreatmentResponse))) +
        (1 - armProbability A.d true P) * atu A.d P := by
  rw [atu_observable_identity A P h0 h1]
  have hp : 1 - armProbability A.d true P ≠ 0 := ne_of_gt
    (by linarith [(armProbability_range (parametersWithBeta A β1 hβ1) true P h1).2, A.hδ] : 0 < 1 - armProbability A.d true P)
  field_simp
  ring

theorem conditionalEffect_of_constant_regressions (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) (c0 c1 : ℝ)
    (h0 : regression d false P =ᵐ[(P : Measure (Model.Covariate d × TreatmentResponse))] fun _ => c0)
    (h1 : regression d true P =ᵐ[(P : Measure (Model.Covariate d × TreatmentResponse))] fun _ => c1)
    (hp : armProbability d j P ≠ 0) : conditionalEffect d j P = c1 - c0 := by
  unfold conditionalEffect
  have he : (∫ o, armIndicator j o.2 * (regression d true P o - regression d false P o)
      ∂(P : Measure (Model.Covariate d × TreatmentResponse))) =
      (∫ o, armIndicator j o.2 * (c1 - c0)
        ∂(P : Measure (Model.Covariate d × TreatmentResponse))) := by
    apply integral_congr_ae
    filter_upwards [h0, h1] with o ho0 ho1
    rw [ho0, ho1]
  rw [he, integral_mul_const]
  change armProbability d j P * (c1 - c0) / armProbability d j P = _
  exact mul_div_cancel_left₀ _ hp

theorem ate_of_constant_regressions (d : ℕ)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) (c0 c1 : ℝ)
    (h0 : regression d false P =ᵐ[(P : Measure (Model.Covariate d × TreatmentResponse))] fun _ => c0)
    (h1 : regression d true P =ᵐ[(P : Measure (Model.Covariate d × TreatmentResponse))] fun _ => c1) :
    ate d P = c1 - c0 := by
  unfold ate armMean
  have he0 := integral_congr_ae h0
  have he1 := integral_congr_ae h1
  change (∫ o, regression d true P o ∂(P : Measure (Model.Covariate d × TreatmentResponse))) -
    (∫ o, regression d false P o ∂(P : Measure (Model.Covariate d × TreatmentResponse))) = _
  rw [he0, he1]
  simp only [integral_const, probReal_univ, one_smul]

/-- The constant MAR family gives exactly the same ATE, ATT and ATU after
the genuine augmentation kernel, as required by the root-n applications. -/
theorem augmentation_constant_effects (A : Model.Parameters) (hM : 1 ≤ A.M0) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (h : Witness A P)
    (hH : 1 / 2 ≤ A.H)
    (hInv : (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H)
    (hDensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus)
    (c : ℝ) (hconst : ∀ x, h.b x = c) :
    ate A.d (augmentationLaw A j P) = armSign j * (Model.target A (observables A hM) P - 1 / 2) ∧
      ∀ r : Bool, conditionalEffect A.d r (augmentationLaw A j P) =
        armSign j * (Model.target A (observables A hM) P - 1 / 2) := by
  let Q := augmentationLaw A j P
  let hs := h.augmentationSelectedWitness A j P
  let ht := h.augmentationOtherWitness A j P hH hInv hDensity
  have hc : regression A.d j Q =ᵐ[(Q : Measure (Model.Covariate A.d × TreatmentResponse))] fun _ => c := by
    filter_upwards [hs.regression_eq A j Q] with o ho
    change regression A.d j Q o = h.b o.1 at ho
    rw [ho, hconst]
  have ho := ht.regression_eq A (!j) Q
  change regression A.d (!j) Q =ᵐ[(Q : Measure (Model.Covariate A.d × TreatmentResponse))]
    (fun _ => (1 / 2 : ℝ)) at ho
  have hps : 0 < armProbability A.d j Q := A.hδ.trans_le (armProbability_range A j Q hs).1
  have hpt : 0 < armProbability A.d (!j) Q := A.hδ.trans_le (armProbability_range A (!j) Q ht).1
  have hp : ∀ r, armProbability A.d r Q ≠ 0 := by
    intro r
    cases j <;> cases r
    · exact hps.ne'
    · exact hpt.ne'
    · exact hpt.ne'
    · exact hps.ne'
  have hψ : Model.target A (observables A hM) P = c := by
    rw [target_eq_mean A hM P h]
    simp only [hconst, integral_const, probReal_univ, one_smul]
  refine ⟨augmentation_ate A hM j P h hH hInv hDensity, fun r => ?_⟩
  change conditionalEffect A.d r Q = _
  cases j
  · simp only [Bool.not_false] at ho
    rw [conditionalEffect_of_constant_regressions A.d r Q c (1 / 2) hc ho (hp r), hψ]
    simp [armSign]
  · simp only [Bool.not_true] at ho
    rw [conditionalEffect_of_constant_regressions A.d r Q (1 / 2) c ho hc (hp r), hψ]
    simp [armSign]

end RoughRegime.Applications.MAR
