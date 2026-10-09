module

public import RoughRegime.ProductResponseBaselines
public import RoughRegime.ApplicationMAR


@[expose] public section
/-! The actual randomized-trial forward map and independent fair-coin reverse
kernel, including exact inverse response and design laws. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.Trial

abbrev Response := MAR.TreatmentResponse

def transformedResponse (z : Response) : Products.BoundedResponse :=
  ⟨Products.sign z.1 * (2 * (z.2 : ℝ) - 1), by
    change -1 ≤ _ ∧ _ ≤ 1
    apply abs_le.mp
    rw [abs_mul, Products.sign_abs, one_mul]
    apply abs_le.mpr
    constructor <;> linarith [(z.2.property).1, (z.2.property).2]⟩

theorem transformedResponse_measurable : Measurable transformedResponse := by
  apply Measurable.subtype_mk
  exact (Products.sign_measurable.comp measurable_fst).mul
    (((measurable_subtype_coe.comp measurable_snd).const_mul 2).sub measurable_const)

def forward (d : ℕ) (o : Model.Covariate d × Response) :
    Model.Covariate d × Products.BoundedResponse := (o.1, transformedResponse o.2)

theorem forward_measurable (d : ℕ) : Measurable (forward d) :=
  measurable_fst.prodMk (transformedResponse_measurable.comp measurable_snd)

theorem transformedResponse_formula (z : Response) :
    (transformedResponse z : ℝ) = 2 * MAR.armOutcome true z -
      2 * MAR.armOutcome false z - 2 * MAR.armIndicator true z + 1 := by
  rcases z with ⟨b,y⟩
  cases b <;> simp [transformedResponse, Products.sign, MAR.armOutcome, MAR.armIndicator] <;> ring

theorem falseIndicator_formula (z : Response) :
    MAR.armIndicator false z = 1 - MAR.armIndicator true z := by
  rcases z with ⟨b,y⟩
  cases b <;> norm_num [MAR.armIndicator]

def reverseResponse (y : Products.BoundedResponse) (b : Bool) : Response :=
  (b, ⟨(1 + Products.sign b * (y : ℝ)) / 2, by
    have hs : |Products.sign b * (y : ℝ)| ≤ 1 := by
      rw [abs_mul, Products.sign_abs, one_mul]
      exact Products.response_bound y
    obtain ⟨hl, hu⟩ := abs_le.mp hs
    constructor <;> linarith⟩)

theorem reverseResponse_measurable : Measurable (Function.uncurry reverseResponse) := by
  apply measurable_from_prod_countable_left
  intro b
  exact measurable_const.prodMk
    (((measurable_const.add (measurable_subtype_coe.const_mul (Products.sign b))).div_const 2).subtype_mk)

def reverse (d : ℕ) (o : (Model.Covariate d × Products.BoundedResponse) × Bool) :
    Model.Covariate d × Response := (o.1.1, reverseResponse o.1.2 o.2)

theorem reverse_measurable (d : ℕ) : Measurable (reverse d) :=
  (measurable_fst.comp measurable_fst).prodMk
    (reverseResponse_measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem transformed_reverseResponse (y : Products.BoundedResponse) (b : Bool) :
    transformedResponse (reverseResponse y b) = y := by
  apply Subtype.ext
  cases b <;> simp [transformedResponse, reverseResponse, Products.sign] <;> ring

theorem forward_reverse (d : ℕ) (o : (Model.Covariate d × Products.BoundedResponse) × Bool) :
    forward d (reverse d o) = o.1 := by
  rcases o with ⟨⟨x, y⟩, b⟩
  simp [forward, reverse, transformed_reverseResponse]

def reverseKernel (d : ℕ) :
    Kernel (Model.Covariate d × Products.BoundedResponse) (Model.Covariate d × Response) :=
  (Kernel.id ×ₖ Kernel.const _ (MAR.fairCoin : Measure Bool)).map (reverse d)

instance reverseKernel_markov (d : ℕ) : IsMarkovKernel (reverseKernel d) :=
  Kernel.IsMarkovKernel.map _ (reverse_measurable d)

theorem reverseKernel_law (d : ℕ) (μ : Measure (Model.Covariate d × Products.BoundedResponse))
    [SFinite μ] : reverseKernel d ∘ₘ μ = (μ.prod (MAR.fairCoin : Measure Bool)).map (reverse d) := by
  rw [reverseKernel, ← Measure.map_comp μ _ (reverse_measurable d),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

theorem forward_reverseKernel_law (d : ℕ)
    (μ : Measure (Model.Covariate d × Products.BoundedResponse)) [IsProbabilityMeasure μ] :
    (reverseKernel d ∘ₘ μ).map (forward d) = μ := by
  rw [reverseKernel_law, Measure.map_map (forward_measurable d) (reverse_measurable d)]
  have hf : forward d ∘ reverse d = Prod.fst := funext (forward_reverse d)
  rw [hf]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

theorem reverseKernel_marginal (d : ℕ)
    (μ : Measure (Model.Covariate d × Products.BoundedResponse)) [IsProbabilityMeasure μ] :
    (reverseKernel d ∘ₘ μ).map Prod.fst = μ.map Prod.fst := by
  rw [reverseKernel_law, Measure.map_map measurable_fst (reverse_measurable d)]
  change (μ.prod (MAR.fairCoin : Measure Bool)).map (Prod.fst ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_fst measurable_fst]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

theorem reverse_conditional (d : ℕ)
    (μ : Measure (Model.Covariate d × Products.BoundedResponse)) [IsProbabilityMeasure μ]
    (f : Response → ℝ) (hf : Measurable f) (g : Model.Covariate d → ℝ) (hg : Measurable g)
    (hfi : Integrable (fun o => f (reverseResponse o.1.2 o.2)) (μ.prod (MAR.fairCoin : Measure Bool)))
    (hc : (μ.prod (MAR.fairCoin : Measure Bool))[(fun o => f (reverseResponse o.1.2 o.2)) |
      MeasurableSpace.comap Prod.fst (MeasurableSpace.comap Prod.fst inferInstance)] =ᵐ[
        μ.prod (MAR.fairCoin : Measure Bool)] fun o => g o.1.1) :
    (reverseKernel d ∘ₘ μ)[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      reverseKernel d ∘ₘ μ] g ∘ Prod.fst := by
  rw [reverseKernel_law]
  have hinfo : MeasurableSpace.comap (reverse d)
      (MeasurableSpace.comap Prod.fst inferInstance) =
      MeasurableSpace.comap (@Prod.fst (Model.Covariate d × Products.BoundedResponse) Bool)
        (MeasurableSpace.comap Prod.fst inferInstance) := by
    rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    rfl
  have hgm : @Measurable (Model.Covariate d × Response) ℝ
      (MeasurableSpace.comap Prod.fst inferInstance) inferInstance (g ∘ Prod.fst) :=
    hg.comp (measurable_iff_comap_le.mpr le_rfl)
  apply conditional_map (μ.prod (MAR.fairCoin : Measure Bool)) (reverse d) (reverse_measurable d)
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    (f ∘ Prod.snd) (g ∘ Prod.fst) (hf.comp measurable_snd) hgm hfi
  simpa only [hinfo, Function.comp_def, reverse] using hc

theorem reverse_preserved_moment (d : ℕ)
    (μ : Measure (Model.Covariate d × Products.BoundedResponse)) [IsProbabilityMeasure μ]
    (f : Model.Covariate d → ℝ) (hf : Measurable f)
    (hc : μ[((Subtype.val : Products.BoundedResponse → ℝ) ∘ Prod.snd) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ] f ∘ Prod.fst) :
    (reverseKernel d ∘ₘ μ)[((fun z => (transformedResponse z : ℝ)) ∘ Prod.snd) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[reverseKernel d ∘ₘ μ] f ∘ Prod.fst := by
  have hi : Integrable ((Subtype.val : Products.BoundedResponse → ℝ) ∘ Prod.snd) μ :=
    Integrable.of_mem_Icc (-1) 1 (measurable_subtype_coe.comp measurable_snd).aemeasurable
      (Filter.Eventually.of_forall (fun o => o.2.property))
  have hip : Integrable (((Subtype.val : Products.BoundedResponse → ℝ) ∘ Prod.snd) ∘ Prod.fst)
      (μ.prod (MAR.fairCoin : Measure Bool)) := by
    apply Integrable.comp_measurable (f := Prod.fst) _ measurable_fst
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hi
  apply reverse_conditional d μ (fun z => (transformedResponse z : ℝ))
    (measurable_subtype_coe.comp transformedResponse_measurable) f hf
  · simpa only [transformed_reverseResponse, Function.comp_def] using hip
  · have hp := conditional_fst_product μ (MAR.fairCoin : Measure Bool)
      ((Subtype.val : Products.BoundedResponse → ℝ) ∘ Prod.snd) hi
      (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    have he := hc.comp_tendsto ((Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := (MAR.fairCoin : Measure Bool))).tendsto_ae)
    simpa only [transformed_reverseResponse, Function.comp_def] using hp.trans he

theorem reverse_fair_moment (d : ℕ)
    (μ : Measure (Model.Covariate d × Products.BoundedResponse)) [IsProbabilityMeasure μ] :
    (reverseKernel d ∘ₘ μ)[MAR.armIndicator true ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[reverseKernel d ∘ₘ μ] fun _ => (1 / 2 : ℝ) := by
  have hb : Integrable (fun b => (MAR.bitOutcome b : ℝ)) (MAR.fairCoin : Measure Bool) :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall (fun b => (MAR.bitOutcome b).property))
  have hi : Integrable (fun o : (Model.Covariate d × Products.BoundedResponse) × Bool =>
      (1 : ℝ) * (MAR.bitOutcome o.2 : ℝ)) (μ.prod (MAR.fairCoin : Measure Bool)) :=
    (integrable_const (1 : ℝ)).mul_prod hb
  have hp := conditional_product_mul μ (MAR.fairCoin : Measure Bool) (fun _ => (1 : ℝ))
    (integrable_const 1) (fun b => (MAR.bitOutcome b : ℝ)) hb
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
  have hcopy : ∀ y b, MAR.armIndicator true (reverseResponse y b) = (MAR.bitOutcome b : ℝ) := by
    intro y b
    cases b <;> simp [MAR.armIndicator, reverseResponse, MAR.bitOutcome]
  apply reverse_conditional d μ (MAR.armIndicator true) (MAR.armIndicator_measurable true)
    (fun _ => 1 / 2) measurable_const
  · simpa only [hcopy, one_mul] using hi
  · rw [condExp_const measurable_fst.comap_le, MAR.fairCoin_mean] at hp
    simpa only [hcopy, one_mul] using hp

/-- The transformed mean is the CATE computed from the actual arm
conditional means.  Both arm denominators are derived from fair randomization. -/
theorem transformed_conditional_eq_cate (d : ℕ)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ]
    (hf : μ[MAR.armIndicator true ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      fun _ => (1 / 2 : ℝ)) :
    μ[((fun z => (transformedResponse z : ℝ)) ∘ Prod.snd) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      fun o => μ[MAR.armOutcome true ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o /
        μ[MAR.armIndicator true ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o -
        μ[MAR.armOutcome false ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o /
        μ[MAR.armIndicator false ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o := by
  let m : MeasurableSpace (Model.Covariate d × Response) := MeasurableSpace.comap Prod.fst inferInstance
  let a : Model.Covariate d × Response → ℝ := MAR.armOutcome true ∘ Prod.snd
  let b : Model.Covariate d × Response → ℝ := MAR.armOutcome false ∘ Prod.snd
  let r : Model.Covariate d × Response → ℝ := MAR.armIndicator true ∘ Prod.snd
  have hir : Integrable r μ := Integrable.of_mem_Icc 0 1
    ((MAR.armIndicator_measurable true).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => by rcases o with ⟨x,b,y⟩; cases b <;> norm_num [r,MAR.armIndicator]))
  have hia : Integrable a μ := Integrable.of_mem_Icc 0 1
    ((MAR.armOutcome_measurable true).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => by
      rcases o with ⟨x,b,y⟩
      cases b <;> simp [a,MAR.armOutcome,MAR.armIndicator]))
  have hib : Integrable b μ := Integrable.of_mem_Icc 0 1
    ((MAR.armOutcome_measurable false).comp measurable_snd).aemeasurable
    (Filter.Eventually.of_forall (fun o => by
      rcases o with ⟨x,b,y⟩
      cases b <;> simp [b,MAR.armOutcome,MAR.armIndicator]))
  have hfalse : μ[MAR.armIndicator false ∘ Prod.snd | m] =ᵐ[μ] fun _ => (1 / 2 : ℝ) := by
    have he : MAR.armIndicator false ∘ Prod.snd = (fun _ => (1 : ℝ)) - r := by
      funext o
      exact falseIndicator_formula o.2
    rw [he]
    have hs := condExp_sub (integrable_const (1 : ℝ)) hir m
    rw [condExp_const measurable_fst.comap_le] at hs
    filter_upwards [hs,hf] with o ho hf
    change μ[r | m] o = 1 / 2 at hf
    simpa only [Pi.sub_apply,hf,show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using ho
  have hiab : Integrable ((2 : ℝ) • a - (2 : ℝ) • b) μ :=
    (hia.smul (2 : ℝ)).sub (hib.smul (2 : ℝ))
  have hiabr : Integrable ((2 : ℝ) • a - (2 : ℝ) • b - (2 : ℝ) • r) μ :=
    hiab.sub (hir.smul (2 : ℝ))
  have hab := condExp_sub (hia.smul (2 : ℝ)) (hib.smul (2 : ℝ)) m
  have habr := condExp_sub hiab (hir.smul (2 : ℝ)) m
  have he := condExp_add hiabr (integrable_const (1 : ℝ)) m
  rw [condExp_const measurable_fst.comap_le] at he
  have hformula : ((fun z => (transformedResponse z : ℝ)) ∘ Prod.snd) =
      (2 : ℝ) • a - (2 : ℝ) • b - (2 : ℝ) • r + (fun _ => 1) := by
    funext o
    simpa only [a,b,r,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Function.comp_def]
      using transformedResponse_formula o.2
  rw [hformula]
  filter_upwards [he,habr,hab,hf,hfalse,condExp_smul (2 : ℝ) a m,
    condExp_smul (2 : ℝ) b m,condExp_smul (2 : ℝ) r m] with o ho hr hab hf hfalse ha hb hrr
  change μ[r | m] o = 1 / 2 at hf
  simp only [Pi.add_apply,Pi.sub_apply] at ho hr hab
  rw [hr,hab,ha,hb,hrr] at ho
  simp only [Pi.smul_apply,smul_eq_mul] at ho
  change μ[(2 : ℝ) • a - (2 : ℝ) • b - (2 : ℝ) • r + (fun _ => 1) | m] o = _
  rw [ho]
  change 2 * μ[a|m] o - 2 * μ[b|m] o - 2 * μ[r|m] o + 1 =
    μ[a|m] o / μ[r|m] o - μ[b|m] o / μ[MAR.armIndicator false ∘ Prod.snd|m] o
  rw [hf,hfalse]
  ring

end RoughRegime.Applications.Trial
