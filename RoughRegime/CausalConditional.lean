module

public import RoughRegime.ApplicationTransport
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.FactorsThrough


@[expose] public section
/-! Conditional independence and measurable coarsening imply the true
conditional-product and selection identities used in causal examples. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

theorem condExp_product_of_condIndep {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f g : Ω→ℝ) (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) (hp : Integrable (fun ω=>f ω*g ω) μ)
    (hi : CondIndepFun m hm f g μ) :
    μ[(fun ω=>f ω*g ω)|m]=ᵐ[μ] fun ω=>μ[f|m] ω*μ[g|m] ω := by
  let : MeasurableSpace Ω := mΩ
  have hid := (condIndepFun_iff_map_prod_eq_prod_map_map hf hg).mp hi
  have hid' := ae_of_ae_trim hm hid
  have hcf := condExp_ae_eq_integral_condExpKernel hm hfi
  have hcg := condExp_ae_eq_integral_condExpKernel hm hgi
  have hcp := condExp_ae_eq_integral_condExpKernel hm hp
  filter_upwards [hid',hcf,hcg,hcp] with ω hi hfeq hgeq hpeq
  rw [hpeq,hfeq,hgeq]
  have hind : IndepFun f g ((condExpKernel μ m) ω) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr
    simpa only [Kernel.map_apply _ (hf.prodMk hg),Kernel.map_apply _ hf,Kernel.map_apply _ hg,Kernel.prod_apply] using hi
  exact hind.integral_fun_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable

theorem condExp_map_pullback {Ω Y : Type*} [mΩ : MeasurableSpace Ω] [mY : MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω→Y) (hT : Measurable T)
    (m : MeasurableSpace Y) (hm : m ≤ mY) (f : Y→ℝ) (hf : Measurable[mY] f)
    (hfi : Integrable (f∘T) μ) :
    ((@Measure.map Ω Y mΩ mY T μ)[f|m])∘T=ᵐ[μ] μ[f∘T|MeasurableSpace.comap T m] := by
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace Y := mY
  obtain ⟨g,hg,hgEq⟩ := (stronglyMeasurable_condExp
    (μ:=μ) (m:=MeasurableSpace.comap T m) (f:=f∘T)).exists_eq_measurable_comp (mY:=m) (f:=T)
  have hout := Applications.conditional_map μ T hT m hm f g hf hg.measurable hfi
    (EventuallyEq.of_eq hgEq)
  have hpull : ((@Measure.map Ω Y mΩ mY T μ)[f|m])∘T=ᵐ[μ] g∘T :=
    ae_of_ae_map (f:=T) (p:=fun y=>((@Measure.map Ω Y mΩ mY T μ)[f|m]) y=g y) hT.aemeasurable hout
  exact hpull.trans (EventuallyEq.of_eq hgEq.symm)

theorem conditional_ratio_map_integral {Ω Y : Type*} [mΩ : MeasurableSpace Ω] [mY : MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω→Y) (hT : Measurable T)
    (m : MeasurableSpace Y) (hm : m ≤ mY) (f g : Y→ℝ)
    (hf : Measurable[mY] f) (hg : Measurable[mY] g)
    (hfi : Integrable (f∘T) μ) (hgi : Integrable (g∘T) μ) :
    (∫ y,((@Measure.map Ω Y mΩ mY T μ)[f|m]) y/((@Measure.map Ω Y mΩ mY T μ)[g|m]) y
      ∂(@Measure.map Ω Y mΩ mY T μ))=
      ∫ ω,μ[f∘T|MeasurableSpace.comap T m] ω/μ[g∘T|MeasurableSpace.comap T m] ω ∂μ := by
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace Y := mY
  have hfCE : Measurable ((μ.map T)[f|m]) := (stronglyMeasurable_condExp.mono hm).measurable
  have hgCE : Measurable ((μ.map T)[g|m]) := (stronglyMeasurable_condExp.mono hm).measurable
  have hmeas : Measurable (fun y=>((μ.map T)[f|m]) y/((μ.map T)[g|m]) y) := hfCE.div hgCE
  rw [integral_map (μ:=μ) (f:=fun y=>((μ.map T)[f|m]) y/((μ.map T)[g|m]) y) hT.aemeasurable hmeas.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [condExp_map_pullback μ T hT m hm f hf hfi,
    condExp_map_pullback μ T hT m hm g hg hgi] with ω hfo hgo
  exact congrArg₂ (fun a b : ℝ=>a/b) hfo hgo

theorem selection_conditional_product {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (r y potential : Ω→ℝ)
    (hr : Measurable[mΩ] r) (hp : Measurable[mΩ] potential)
    (hir : Integrable r μ) (hip : Integrable potential μ)
    (hirp : Integrable (fun ω=>r ω*potential ω) μ)
    (hconsistency : (fun ω=>r ω*y ω)=ᵐ[μ] fun ω=>r ω*potential ω)
    (hexchangeability : CondIndepFun m hm r potential μ) :
    μ[(fun ω=>r ω*y ω)|m]=ᵐ[μ] fun ω=>μ[r|m] ω*μ[potential|m] ω := by
  let : MeasurableSpace Ω := mΩ
  exact (condExp_congr_ae hconsistency (m:=m)).trans
    (condExp_product_of_condIndep μ m hm r potential hr hp hir hip hirp hexchangeability)

theorem selection_conditional_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (r y potential : Ω→ℝ)
    (hr : Measurable[mΩ] r) (hp : Measurable[mΩ] potential)
    (hir : Integrable r μ) (hip : Integrable potential μ)
    (hirp : Integrable (fun ω=>r ω*potential ω) μ)
    (hconsistency : (fun ω=>r ω*y ω)=ᵐ[μ] fun ω=>r ω*potential ω)
    (hexchangeability : CondIndepFun m hm r potential μ)
    (hpositive : ∀ᵐ ω ∂μ,μ[r|m] ω≠0) :
    (fun ω=>μ[(fun ω=>r ω*y ω)|m] ω/μ[r|m] ω)=ᵐ[μ] μ[potential|m] := by
  let : MeasurableSpace Ω := mΩ
  have he := condExp_product_of_condIndep μ m hm r potential hr hp hir hip hirp hexchangeability
  have hc := condExp_congr_ae hconsistency (m:=m)
  filter_upwards [he,hc,hpositive] with ω he hc hw
  rw [hc,he,mul_div_cancel_left₀ _ hw]

theorem selection_mean_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (r y potential : Ω→ℝ)
    (hr : Measurable[mΩ] r) (hp : Measurable[mΩ] potential)
    (hir : Integrable r μ) (hip : Integrable potential μ)
    (hirp : Integrable (fun ω=>r ω*potential ω) μ)
    (hconsistency : (fun ω=>r ω*y ω)=ᵐ[μ] fun ω=>r ω*potential ω)
    (hexchangeability : CondIndepFun m hm r potential μ)
    (hpositive : ∀ᵐ ω ∂μ,μ[r|m] ω≠0) :
    (∫ ω,μ[(fun ω=>r ω*y ω)|m] ω/μ[r|m] ω ∂μ)=∫ ω,potential ω ∂μ := by
  let : MeasurableSpace Ω := mΩ
  rw [integral_congr_ae (selection_conditional_identification μ m hm r y potential hr hp hir hip hirp
    hconsistency hexchangeability hpositive),integral_condExp hm]

theorem probabilityMap_comp {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
    (P : ProbabilityMeasure Ω) (T : Ω→Y) (S : Y→Z) (hT : Measurable T) (hS : Measurable S) :
    (P.map T).map S=P.map (S∘T) := by
  apply Subtype.ext
  exact Measure.map_map hS hT

end RoughRegime.Causal
