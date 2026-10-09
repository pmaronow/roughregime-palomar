module

public import RoughRegime.ApplicationTransport
public import RoughRegime.KernelSeedBridge


@[expose] public section
/-! Actual missing-data and treatment response maps and their conditional moments. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.MAR

abbrev Outcome := Icc (0 : ℝ) 1
abbrev Response := Unit ⊕ Outcome
abbrev TreatmentResponse := Bool × Outcome

instance : MeasurableSingletonClass Response where
  measurableSet_singleton z := by
    apply measurableSet_sum_iff.mpr
    cases z <;> simp [Set.preimage]

def observed : Response → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)
def observedOutcome : Response → ℝ := Sum.elim (fun _ => 0) Subtype.val
def armIndicator (j : Bool) (z : TreatmentResponse) : ℝ := if z.1 = j then 1 else 0
def armOutcome (j : Bool) (z : TreatmentResponse) : ℝ := armIndicator j z * z.2

lemma observed_measurable : Measurable observed := measurable_const.sumElim measurable_const
lemma observedOutcome_measurable : Measurable observedOutcome :=
  measurable_const.sumElim measurable_subtype_coe

lemma observed_range (z : Response) : observed z ∈ Icc (0 : ℝ) 1 := by
  cases z <;> norm_num [observed]

lemma observedOutcome_range (z : Response) : observedOutcome z ∈ Icc (0 : ℝ) 1 := by
  cases z with
  | inl u => norm_num [observedOutcome]
  | inr y => exact y.property

lemma armIndicator_measurable (j : Bool) : Measurable (armIndicator j) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const measurable_const

lemma armOutcome_measurable (j : Bool) : Measurable (armOutcome j) :=
  (armIndicator_measurable j).mul (measurable_subtype_coe.comp measurable_snd)

def keepArmResponse (j : Bool) (z : TreatmentResponse) : Response :=
  if z.1 = j then Sum.inr z.2 else Sum.inl ()

lemma keepArmResponse_measurable (j : Bool) : Measurable (keepArmResponse j) :=
  (measurable_inr.comp measurable_snd).ite
    (measurableSet_eq_fun measurable_fst measurable_const) measurable_const

lemma keepArmResponse_moments (j : Bool) (z : TreatmentResponse) :
    observed (keepArmResponse j z) = armIndicator j z ∧
    observedOutcome (keepArmResponse j z) = armOutcome j z := by
  by_cases h : z.1 = j <;> simp [keepArmResponse, h, observed, observedOutcome, armIndicator, armOutcome]

def keepArm (d : ℕ) (j : Bool) (o : Model.Covariate d × TreatmentResponse) :
    Model.Covariate d × Response := (o.1, keepArmResponse j o.2)

lemma keepArm_measurable (d : ℕ) (j : Bool) : Measurable (keepArm d j) :=
  measurable_fst.prodMk ((keepArmResponse_measurable j).comp measurable_snd)

def bitOutcome (b : Bool) : Outcome := if b then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

def augmentResponse (j : Bool) (z : Response) (b : Bool) : TreatmentResponse :=
  Sum.elim (fun _ => (!j, bitOutcome b)) (fun y => (j, y)) z

lemma augmentResponse_measurable (j : Bool) :
    Measurable (Function.uncurry (augmentResponse j)) := by
  apply measurable_from_prod_countable_left
  intro b
  change Measurable (Sum.elim (fun _ : Unit => (!j, bitOutcome b)) (fun y : Outcome => (j, y)))
  exact measurable_const.sumElim (measurable_const.prodMk measurable_id)

lemma augmentResponse_moments (j : Bool) (z : Response) (b : Bool) :
    armIndicator j (augmentResponse j z b) = observed z ∧
    armOutcome j (augmentResponse j z b) = observedOutcome z ∧
    armIndicator (!j) (augmentResponse j z b) = 1 - observed z ∧
    armOutcome (!j) (augmentResponse j z b) = (1 - observed z) * (bitOutcome b : ℝ) := by
  cases j <;> cases z <;> simp [augmentResponse, armIndicator, armOutcome, observed, observedOutcome]

def augment (d : ℕ) (j : Bool) (o : (Model.Covariate d × Response) × Bool) :
    Model.Covariate d × TreatmentResponse := (o.1.1, augmentResponse j o.1.2 o.2)

lemma augment_measurable (d : ℕ) (j : Bool) : Measurable (augment d j) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((augmentResponse_measurable j).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

def fairCoin : ProbabilityMeasure Bool :=
  ⟨bernoulliMeasure true false ⟨1 / 2, by norm_num⟩, inferInstance⟩

lemma fairCoin_mean : ∫ b, (bitOutcome b : ℝ) ∂(fairCoin : Measure Bool) = 1 / 2 := by
  change (∫ b, (bitOutcome b : ℝ) ∂bernoulliMeasure true false ⟨1 / 2, by norm_num⟩) = 1 / 2
  rw [integral_bernoulliMeasure]
  norm_num [bitOutcome]

def augmentationKernel (d : ℕ) (j : Bool) :
    Kernel (Model.Covariate d × Response) (Model.Covariate d × TreatmentResponse) :=
  (Kernel.id ×ₖ Kernel.const _ (fairCoin : Measure Bool)).map (augment d j)

lemma augmentationKernel_markov (d : ℕ) (j : Bool) : IsMarkovKernel (augmentationKernel d j) :=
  Kernel.IsMarkovKernel.map _ (augment_measurable d j)

lemma augmentationKernel_law (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × Response)) [SFinite μ] :
    augmentationKernel d j ∘ₘ μ = (μ.prod (fairCoin : Measure Bool)).map (augment d j) := by
  rw [augmentationKernel, ← Measure.map_comp μ _ (augment_measurable d j),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

/-- The augmentation keeps the observed arm exactly, for every data point and seed. -/
lemma keepArm_augment (d : ℕ) (j : Bool) (o : (Model.Covariate d × Response) × Bool) :
    keepArm d j (augment d j o) = o.1 := by
  rcases o with ⟨⟨x, z⟩, b⟩
  cases j <;> cases z <;> simp [keepArm, augment, augmentResponse, keepArmResponse]

/-- The actual output law returns to the input law under the keep-arm map. -/
lemma keepArm_augmentation_law (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ] :
    (augmentationKernel d j ∘ₘ μ).map (keepArm d j) = μ := by
  rw [augmentationKernel_law, Measure.map_map (keepArm_measurable d j) (augment_measurable d j)]
  have hf : keepArm d j ∘ augment d j = Prod.fst := funext (keepArm_augment d j)
  rw [hf]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

/-- Conditional response moments are transported under the genuine keep-arm map. -/
lemma keepArm_conditional (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × TreatmentResponse)) [IsProbabilityMeasure μ]
    (f : Response → ℝ) (hf : Measurable f) (g : Model.Covariate d → ℝ) (hg : Measurable g)
    (hfi : Integrable (fun o => f (keepArmResponse j o.2)) μ)
    (hc : μ[(fun o => f (keepArmResponse j o.2)) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      fun o => g o.1) :
    (μ.map (keepArm d j))[(fun o => f o.2) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      μ.map (keepArm d j)] fun o => g o.1 := by
  have hinfo : MeasurableSpace.comap (keepArm d j)
      (MeasurableSpace.comap Prod.fst inferInstance) =
      MeasurableSpace.comap (@Prod.fst (Model.Covariate d) TreatmentResponse) inferInstance := by
    rw [MeasurableSpace.comap_comp]
    rfl
  have hgm : @Measurable (Model.Covariate d × Response) ℝ
      (MeasurableSpace.comap Prod.fst inferInstance) inferInstance (fun o => g o.1) :=
    hg.comp (measurable_iff_comap_le.mpr le_rfl)
  apply conditional_map μ (keepArm d j) (keepArm_measurable d j)
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    (fun o => f o.2) (fun o => g o.1) (hf.comp measurable_snd) hgm hfi
  simpa only [hinfo, Function.comp_def, keepArm] using hc

lemma augmentation_marginal (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ] :
    (augmentationKernel d j ∘ₘ μ).map Prod.fst = μ.map Prod.fst := by
  rw [augmentationKernel_law, Measure.map_map measurable_fst (augment_measurable d j)]
  have hf : Prod.fst ∘ augment d j = Prod.fst ∘ Prod.fst := rfl
  rw [hf, ← Measure.map_map measurable_fst measurable_fst]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

lemma augmentation_conditional (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ]
    (f : TreatmentResponse → ℝ) (hf : Measurable f)
    (g : Model.Covariate d → ℝ) (hg : Measurable g)
    (hfi : Integrable (fun o => f (augmentResponse j o.1.2 o.2))
      (μ.prod (fairCoin : Measure Bool)))
    (hc : (μ.prod (fairCoin : Measure Bool))[(fun o => f (augmentResponse j o.1.2 o.2)) |
      MeasurableSpace.comap Prod.fst (MeasurableSpace.comap Prod.fst inferInstance)] =ᵐ[
        μ.prod (fairCoin : Measure Bool)] fun o => g o.1.1) :
    (augmentationKernel d j ∘ₘ μ)[(fun o => f o.2) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      augmentationKernel d j ∘ₘ μ] fun o => g o.1 := by
  rw [augmentationKernel_law]
  have hinfo : MeasurableSpace.comap (augment d j)
      (MeasurableSpace.comap Prod.fst inferInstance) =
      MeasurableSpace.comap (@Prod.fst (Model.Covariate d × Response) Bool)
        (MeasurableSpace.comap Prod.fst inferInstance) := by
    rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    rfl
  have hgm : @Measurable (Model.Covariate d × TreatmentResponse) ℝ
      (MeasurableSpace.comap Prod.fst inferInstance) inferInstance (fun o => g o.1) :=
    hg.comp (measurable_iff_comap_le.mpr le_rfl)
  apply conditional_map (μ.prod (fairCoin : Measure Bool)) (augment d j) (augment_measurable d j)
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    (fun o => f o.2) (fun o => g o.1) (hf.comp measurable_snd) hgm hfi
  simpa only [hinfo, Function.comp_def, augment] using hc

/-- The observed arm's moment is copied without any assumption on the unknown law. -/
lemma augmentation_selected_moment (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ]
    (f : Response → ℝ) (g : Model.Covariate d → ℝ)
    (hg : Measurable g) (hfi : Integrable (f ∘ Prod.snd) μ)
    (fout : TreatmentResponse → ℝ) (hfout : Measurable fout)
    (hcopy : ∀ z b, fout (augmentResponse j z b) = f z)
    (hc : μ[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ] g ∘ Prod.fst) :
    (augmentationKernel d j ∘ₘ μ)[fout ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      augmentationKernel d j ∘ₘ μ] g ∘ Prod.fst := by
  have hi : Integrable (fun o => f (o.1.2)) (μ.prod (fairCoin : Measure Bool)) := by
    change Integrable ((f ∘ Prod.snd) ∘ Prod.fst) (μ.prod (fairCoin : Measure Bool))
    apply Integrable.comp_measurable (f := Prod.fst) _ measurable_fst
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hfi
  apply augmentation_conditional d j μ fout hfout g hg
  · simpa only [hcopy] using hi
  · have hp := conditional_fst_product μ (fairCoin : Measure Bool) (f ∘ Prod.snd) hfi
      (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    have he := hc.comp_tendsto
      ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (fairCoin : Measure Bool))).tendsto_ae)
    simpa only [hcopy, Function.comp_def] using hp.trans he

/-- The newly generated arm averages the independent, genuinely Bernoulli seed. -/
lemma augmentation_other_moment (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ]
    (f : Response → ℝ) (g : Model.Covariate d → ℝ)
    (hg : Measurable g) (hfi : Integrable (f ∘ Prod.snd) μ)
    (fout : TreatmentResponse → ℝ) (hfout : Measurable fout)
    (hcopy : ∀ z b, fout (augmentResponse j z b) = f z * (bitOutcome b : ℝ))
    (hc : μ[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ] g ∘ Prod.fst) :
    (augmentationKernel d j ∘ₘ μ)[fout ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      augmentationKernel d j ∘ₘ μ] fun o => g o.1 / 2 := by
  have hb : Integrable (fun b => (bitOutcome b : ℝ)) (fairCoin : Measure Bool) :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall (fun b => (bitOutcome b).property))
  have hi : Integrable (fun o => f o.1.2 * (bitOutcome o.2 : ℝ))
      (μ.prod (fairCoin : Measure Bool)) := hfi.mul_prod hb
  have hp := conditional_product_mul μ (fairCoin : Measure Bool) (f ∘ Prod.snd) hfi
    (fun b => (bitOutcome b : ℝ)) hb
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
  have he := hc.comp_tendsto
    ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (fairCoin : Measure Bool))).tendsto_ae)
  apply augmentation_conditional d j μ fout hfout (fun x => g x / 2) (hg.div_const 2)
  · simpa only [hcopy] using hi
  · have hh : (μ.prod (fairCoin : Measure Bool))[(fun o => f o.1.2 * (bitOutcome o.2 : ℝ)) |
        MeasurableSpace.comap Prod.fst (MeasurableSpace.comap Prod.fst inferInstance)] =ᵐ[
        μ.prod (fairCoin : Measure Bool)] fun o => g o.1.1 / 2 := by
      filter_upwards [hp, he] with o ho heo
      simp only [Function.comp_apply] at heo
      rw [heo, fairCoin_mean] at ho
      simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using ho
    simpa only [hcopy] using hh

/-- All four source treatment moment identities hold under the actual augmentation law. -/
theorem augmentation_conditional_moments (d : ℕ) (j : Bool)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ]
    (w b : Model.Covariate d → ℝ) (hw : Measurable w) (hb : Measurable b)
    (hD : μ[observed ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      w ∘ Prod.fst)
    (hV : μ[observedOutcome ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      fun o => w o.1 * b o.1) :
    let ν := augmentationKernel d j ∘ₘ μ
    (ν[armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν]
      w ∘ Prod.fst) ∧
    (ν[armOutcome j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν]
      fun o => w o.1 * b o.1) ∧
    (ν[armIndicator (!j) ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν]
      fun o => 1 - w o.1) ∧
    (ν[armOutcome (!j) ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν]
      fun o => (1 - w o.1) / 2) := by
  have hiD : Integrable (observed ∘ Prod.snd) μ := Integrable.of_mem_Icc 0 1
    (observed_measurable.comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => observed_range o.2))
  have hiV : Integrable (observedOutcome ∘ Prod.snd) μ := Integrable.of_mem_Icc 0 1
    (observedOutcome_measurable.comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => observedOutcome_range o.2))
  have hiOther : Integrable ((fun z => 1 - observed z) ∘ Prod.snd) μ :=
    (integrable_const 1).sub hiD
  have hOther : μ[(fun z => 1 - observed z) ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ] (fun x => 1 - w x) ∘ Prod.fst := by
    have hs := condExp_sub (integrable_const (1 : ℝ)) hiD
      (MeasurableSpace.comap Prod.fst inferInstance)
    rw [condExp_const measurable_fst.comap_le] at hs
    simpa only [Pi.sub_def, Function.comp_def] using hs.trans
      ((Filter.EventuallyEq.refl (ae μ) (fun _ => (1 : ℝ))).sub hD)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact augmentation_selected_moment d j μ observed w hw hiD (armIndicator j)
      (armIndicator_measurable j) (fun z coin => (augmentResponse_moments j z coin).1) hD
  · exact augmentation_selected_moment d j μ observedOutcome (fun x => w x * b x)
      (hw.mul hb) hiV (armOutcome j) (armOutcome_measurable j)
      (fun z coin => (augmentResponse_moments j z coin).2.1) hV
  · exact augmentation_selected_moment d j μ (fun z => 1 - observed z) (fun x => 1 - w x)
      (measurable_const.sub hw) hiOther (armIndicator (!j)) (armIndicator_measurable (!j))
      (fun z coin => (augmentResponse_moments j z coin).2.2.1) hOther
  · exact augmentation_other_moment d j μ (fun z => 1 - observed z) (fun x => 1 - w x)
      (measurable_const.sub hw) hiOther (armOutcome (!j)) (armOutcome_measurable (!j))
      (fun z coin => (augmentResponse_moments j z coin).2.2.2) hOther

end RoughRegime.Applications.MAR
