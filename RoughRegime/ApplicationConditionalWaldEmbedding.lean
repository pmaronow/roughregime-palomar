module

public import RoughRegime.ApplicationConditionalWald
public import RoughRegime.ModelLowerConsequences


@[expose] public section
/-! The paper's missing-data embedding into the actual conditional Wald
experiment, using an independent balanced instrument. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.ConditionalWald

def zeroOutcome : MAR.Outcome := ⟨0, by norm_num⟩

def augmentResponse (z : MAR.Response) (coin : Bool) : Response :=
  if coin then
    Sum.elim (fun _ => (true, false, zeroOutcome)) (fun y => (true, true, y)) z
  else (false, false, zeroOutcome)

theorem augmentResponse_measurable :
    Measurable (Function.uncurry augmentResponse) := by
  apply measurable_from_prod_countable_left
  intro coin
  cases coin
  · exact measurable_const
  · exact measurable_const.sumElim
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem augmentResponse_moments (z : MAR.Response) (coin : Bool) :
    instrument (augmentResponse z coin) = bit coin ∧
    treatmentScore (augmentResponse z coin) = 2 * MAR.observed z * bit coin ∧
    outcomeScore (augmentResponse z coin) = 2 * MAR.observedOutcome z * bit coin ∧
    treatment (augmentResponse z coin) ≤ instrument (augmentResponse z coin) := by
  cases coin <;> cases z <;>
    norm_num [augmentResponse, instrument, treatmentScore, treatment,
      outcomeScore, outcome, bit, zeroOutcome, MAR.observed, MAR.observedOutcome]

def augment (d : ℕ) (o : (Model.Covariate d × MAR.Response) × Bool) :
    Model.Covariate d × Response := (o.1.1, augmentResponse o.1.2 o.2)

theorem augment_measurable (d : ℕ) : Measurable (augment d) :=
  (measurable_fst.comp measurable_fst).prodMk
    (augmentResponse_measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

def augmentationKernel (d : ℕ) :
    Kernel (Model.Covariate d × MAR.Response) (Model.Covariate d × Response) :=
  (Kernel.id ×ₖ Kernel.const _ (MAR.fairCoin : Measure Bool)).map (augment d)

theorem augmentationKernel_markov (d : ℕ) : IsMarkovKernel (augmentationKernel d) :=
  Kernel.IsMarkovKernel.map _ (augment_measurable d)

theorem augmentationKernel_law (d : ℕ)
    (μ : Measure (Model.Covariate d × MAR.Response)) [SFinite μ] :
    augmentationKernel d ∘ₘ μ = (μ.prod (MAR.fairCoin : Measure Bool)).map (augment d) := by
  rw [augmentationKernel, ← Measure.map_comp μ _ (augment_measurable d),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

theorem augmentation_marginal (d : ℕ)
    (μ : Measure (Model.Covariate d × MAR.Response)) [IsProbabilityMeasure μ] :
    (augmentationKernel d ∘ₘ μ).map Prod.fst = μ.map Prod.fst := by
  rw [augmentationKernel_law, Measure.map_map measurable_fst (augment_measurable d)]
  have hf : Prod.fst ∘ augment d = Prod.fst ∘ Prod.fst := rfl
  rw [hf, ← Measure.map_map measurable_fst measurable_fst]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

theorem bit_mean : ∫ b, bit b ∂(MAR.fairCoin : Measure Bool) = 1 / 2 := by
  have he : bit = fun b => (MAR.bitOutcome b : ℝ) := by
    funext b; cases b <;> rfl
  rw [he]
  exact MAR.fairCoin_mean

theorem augmentation_conditional (d : ℕ)
    (μ : Measure (Model.Covariate d × MAR.Response)) [IsProbabilityMeasure μ]
    (f : Response → ℝ) (hf : Measurable f)
    (g : Model.Covariate d → ℝ) (hg : Measurable g)
    (hfi : Integrable (fun o => f (augmentResponse o.1.2 o.2))
      (μ.prod (MAR.fairCoin : Measure Bool)))
    (hc : (μ.prod (MAR.fairCoin : Measure Bool))[
      (fun o => f (augmentResponse o.1.2 o.2)) |
      MeasurableSpace.comap Prod.fst (MeasurableSpace.comap Prod.fst inferInstance)] =ᵐ[
        μ.prod (MAR.fairCoin : Measure Bool)] fun o => g o.1.1) :
    (augmentationKernel d ∘ₘ μ)[f ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
        augmentationKernel d ∘ₘ μ] g ∘ Prod.fst := by
  rw [augmentationKernel_law]
  have hinfo : MeasurableSpace.comap (augment d)
      (MeasurableSpace.comap Prod.fst inferInstance) =
      MeasurableSpace.comap (@Prod.fst (Model.Covariate d × MAR.Response) Bool)
        (MeasurableSpace.comap Prod.fst inferInstance) := by
    rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    rfl
  have hgm : @Measurable (Model.Covariate d × Response) ℝ
      (MeasurableSpace.comap Prod.fst inferInstance) inferInstance (g ∘ Prod.fst) :=
    hg.comp (measurable_iff_comap_le.mpr le_rfl)
  apply conditional_map (μ.prod (MAR.fairCoin : Measure Bool)) (augment d)
    (augment_measurable d) (MeasurableSpace.comap Prod.fst inferInstance)
    measurable_fst.comap_le (f ∘ Prod.snd) (g ∘ Prod.fst)
    (hf.comp measurable_snd) hgm hfi
  simpa only [hinfo, Function.comp_def, augment] using hc

/-- Independent instrument randomization averages the source conditional
moment; no unknown-law dependent observation map is used. -/
theorem augmentation_coin_moment (d : ℕ)
    (μ : Measure (Model.Covariate d × MAR.Response)) [IsProbabilityMeasure μ]
    (c : ℝ) (f : MAR.Response → ℝ) (g : Model.Covariate d → ℝ)
    (hg : Measurable g) (hfi : Integrable (f ∘ Prod.snd) μ)
    (fout : Response → ℝ) (hfout : Measurable fout)
    (hcopy : ∀ z coin, fout (augmentResponse z coin) = c*f z*bit coin)
    (hc : μ[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      g ∘ Prod.fst) :
    (augmentationKernel d ∘ₘ μ)[fout ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
        augmentationKernel d ∘ₘ μ] fun o => c*g o.1/2 := by
  have hb : Integrable bit (MAR.fairCoin : Measure Bool) :=
    Integrable.of_mem_Icc 0 1 bit_measurable.aemeasurable
      (Filter.Eventually.of_forall bit_range)
  have hcf : Integrable (fun o => c*f o.2) μ := hfi.const_mul c
  have hi := hcf.mul_prod hb
  have hs := condExp_smul (μ := μ) c (f ∘ Prod.snd)
    (MeasurableSpace.comap Prod.fst inferInstance)
  have hcs : μ[(fun o => c*f o.2) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      fun o => c*g o.1 := by
    filter_upwards [hs,hc] with o ho he
    change μ[(fun o => c*f o.2) | MeasurableSpace.comap Prod.fst inferInstance] o =
      c*(μ[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o) at ho
    simpa only [Pi.smul_apply, smul_eq_mul, he, Function.comp_apply] using ho
  have hp := conditional_product_mul μ (MAR.fairCoin : Measure Bool)
    (fun o => c*f o.2) hcf bit hb
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
  have he := hcs.comp_tendsto
    ((Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := (MAR.fairCoin : Measure Bool))).tendsto_ae)
  apply augmentation_conditional d μ fout hfout (fun x => c*g x/2)
    ((measurable_const.mul hg).div_const 2)
  · simpa only [hcopy] using hi
  · have hh : (μ.prod (MAR.fairCoin : Measure Bool))[
        (fun o => c*f o.1.2*bit o.2) |
        MeasurableSpace.comap Prod.fst (MeasurableSpace.comap Prod.fst inferInstance)] =ᵐ[
          μ.prod (MAR.fairCoin : Measure Bool)] fun o => c*g o.1.1/2 := by
      filter_upwards [hp,he] with o ho heo
      simp only [Function.comp_apply] at heo
      rw [heo,bit_mean] at ho
      simpa only [div_eq_mul_inv, one_mul] using ho
    simpa only [hcopy] using hh

def augmentationLaw (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.Response)) :
    ProbabilityMeasure (Model.Covariate A.d × Response) := by
  have : IsMarkovKernel (augmentationKernel A.d) := augmentationKernel_markov A.d
  exact (augmentationKernel A.d ∘ₘ (P : Measure (Model.Covariate A.d × MAR.Response))).toProbabilityMeasure

theorem augmentationLaw_measure (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.Response)) :
    (augmentationLaw A P : Measure (Model.Covariate A.d × Response)) =
      augmentationKernel A.d ∘ₘ (P : Measure (Model.Covariate A.d × MAR.Response)) := rfl

def sourceWitness (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.Response)) (W : MAR.Witness A P) :
    Witness A (augmentationLaw A P) where
  p := W.p
  q := W.w
  b := W.b
  measurableP := W.measurableP
  measurableQ := W.measurableW
  measurableB := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := by rw [augmentationLaw_measure, augmentation_marginal]; exact W.marginal
  instrumentHalf := by
    rw [augmentationLaw_measure]
    have hm : MeasurableSpace.comap (@Prod.fst (Model.Covariate A.d) MAR.Response)
        inferInstance ≤ (inferInstance : MeasurableSpace (Model.Covariate A.d × MAR.Response)) :=
      measurable_fst.comap_le
    have hc := augmentation_coin_moment A.d
      (P : Measure (Model.Covariate A.d × MAR.Response)) 1 (fun _ => 1) (fun _ => 1)
      measurable_const (integrable_const 1) instrument instrument_measurable
      (fun z coin => by simpa using (augmentResponse_moments z coin).1)
      (by simpa only [Function.comp_def] using
        (condExp_const (μ := (P : Measure (Model.Covariate A.d × MAR.Response))) hm (1:ℝ)).eventuallyEq)
    simpa only [one_mul] using hc
  oneSided := by
    rw [augmentationLaw_measure, augmentationKernel_law]
    apply ae_map_iff (augment_measurable A.d).aemeasurable
      (measurableSet_le (treatment_measurable.comp measurable_snd)
        (instrument_measurable.comp measurable_snd)) |>.mpr
    exact Filter.Eventually.of_forall (fun o => (augmentResponse_moments o.1.2 o.2).2.2.2)
  momentD := by
    rw [augmentationLaw_measure]
    have hi : Integrable (MAR.observed ∘ Prod.snd)
        (P : Measure (Model.Covariate A.d × MAR.Response)) :=
      Integrable.of_mem_Icc 0 1 (MAR.observed_measurable.comp measurable_snd).aemeasurable
        (Filter.Eventually.of_forall (fun o => MAR.observed_range o.2))
    have hc := augmentation_coin_moment A.d
      (P : Measure (Model.Covariate A.d × MAR.Response)) 2 MAR.observed W.w
      W.measurableW hi treatmentScore treatmentScore_measurable
      (fun z coin => (augmentResponse_moments z coin).2.1) W.momentD
    filter_upwards [hc] with o ho
    simpa only [Function.comp_apply, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using ho
  momentV := by
    rw [augmentationLaw_measure]
    have hi : Integrable (MAR.observedOutcome ∘ Prod.snd)
        (P : Measure (Model.Covariate A.d × MAR.Response)) :=
      Integrable.of_mem_Icc 0 1 (MAR.observedOutcome_measurable.comp measurable_snd).aemeasurable
        (Filter.Eventually.of_forall (fun o => MAR.observedOutcome_range o.2))
    have hc := augmentation_coin_moment A.d
      (P : Measure (Model.Covariate A.d × MAR.Response)) 2 MAR.observedOutcome
      (fun x => W.w x*W.b x) (W.measurableW.mul W.measurableB) hi
      outcomeScore outcomeScore_measurable
      (fun z coin => (augmentResponse_moments z coin).2.2.1) W.momentV
    filter_upwards [hc] with o ho
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using ho
  overlap := W.overlap
  smoothInverse := W.smoothInverse
  smoothB := W.smoothB
  densityBounds := W.densityBounds

theorem augmentation_mem_class (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.Response))
    (hP : P ∈ MAR.modelClass A) : augmentationLaw A P ∈ modelClass A := by
  rcases hP with ⟨W⟩
  exact ⟨sourceWitness A P W⟩

theorem target_eq_mean (A : Model.Parameters) (hM : 2≤A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P) :
    target A.d P = ∫ o, W.b o.1 ∂(P : Measure (Model.Covariate A.d × Response)) := by
  rw [← generic_target_eq A hM P,
    Model.target_weighted_representation A (observables A hM) P (W.toModel A hM P),
    Model.marginal_integral A (observables A hM) P (W.toModel A hM P) W.b W.measurableB]
  simp only [observables, Witness.toModel, integral_zero, zero_add, one_mul]
  apply integral_congr_ae
  filter_upwards [W.overlap] with x hx
  have hq : W.q x ≠ 0 := ne_of_gt (A.hδ.trans_le hx.1)
  field_simp

/-- The balanced instrument embedding preserves the actual target exactly. -/
theorem augmentation_target_eq (A : Model.Parameters) (hM : 2≤A.M0)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.Response)) (W : MAR.Witness A P) :
    target A.d (augmentationLaw A P) =
      Model.target A (MAR.observables A (by linarith)) P := by
  rw [target_eq_mean A hM _ (sourceWitness A P W),
    MAR.target_eq_mean A (by linarith) P W, augmentationLaw_measure, augmentationKernel_law]
  change (∫ o, (W.b ∘ Prod.fst) o ∂((P : Measure (Model.Covariate A.d × MAR.Response)).prod
    (MAR.fairCoin : Measure Bool)).map (augment A.d)) = _
  rw [integral_map (augment_measurable A.d).aemeasurable
    (W.measurableB.comp measurable_fst).aestronglyMeasurable]
  change (∫ o, W.b o.1.1 ∂(P : Measure (Model.Covariate A.d × MAR.Response)).prod
    (MAR.fairCoin : Measure Bool)) = _
  simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using
    integral_prod_mul (μ := (P : Measure (Model.Covariate A.d × MAR.Response)))
    (ν := (MAR.fairCoin : Measure Bool)) (fun o => W.b o.1) (fun _ : Bool => (1:ℝ))

/-- Actual iid kernel reduction for both risks on the whole missing-data class. -/
theorem augmentation_risk_reduction (A : Model.Parameters) (hM : 2≤A.M0)
    (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Model.target A (MAR.observables A (by linarith)))
        (MAR.modelClass A) t ≤ Model.minimaxTail n (target A.d) (modelClass A) t ∧
    Model.minimaxRMSE n (Model.target A (MAR.observables A (by linarith)))
        (MAR.modelClass A) ≤ Model.minimaxRMSE n (target A.d) (modelClass A) := by
  haveI : IsMarkovKernel (augmentationKernel A.d) := augmentationKernel_markov A.d
  apply Model.kernel_reduction n (augmentationKernel A.d)
  · intro P hP
    exact augmentation_mem_class A P hP
  · rintro P ⟨W⟩
    exact augmentation_target_eq A hM P W

theorem lowerBracket_of_MAR (A : Model.Parameters) (hM : 2≤A.M0)
    (S : Model.BracketParameters)
    (hMAR : Model.LowerBracket (Model.target A (MAR.observables A (by linarith)))
      (MAR.modelClass A) S) : Model.LowerBracket (target A.d) (modelClass A) S := by
  haveI : IsMarkovKernel (augmentationKernel A.d) := augmentationKernel_markov A.d
  apply Model.lowerBracket_kernel (augmentationKernel A.d) _ _ (MAR.modelClass A) _
    (fun P hP => augmentation_mem_class A P hP)
    (fun P hP => by obtain ⟨W⟩ := hP; exact augmentation_target_eq A hM P W) S hMAR

end RoughRegime.Applications.ConditionalWald
