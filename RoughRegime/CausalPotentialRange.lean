module

public import RoughRegime.CausalConditionalTreatment


@[expose] public section
/-! Positivity and conditional exchangeability inherit the observed outcome
range for the selected potential outcome. No bound on potential outcomes is
assumed. Clipping is used only after this almost-everywhere fact is proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def outsideUnitIndicator (y : ℝ) : ℝ := if y∈Icc (0:ℝ) 1 then 0 else 1

theorem outsideUnitIndicator_measurable : Measurable outsideUnitIndicator :=
  measurable_const.ite measurableSet_Icc measurable_const

theorem outsideUnitIndicator_range (y : ℝ) : outsideUnitIndicator y∈Icc (0:ℝ) 1 := by
  unfold outsideUnitIndicator
  split_ifs <;> norm_num

theorem selected_potential_range {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (A : Ω→Bool) (y p : Ω→ℝ) (j : Bool) (hA : Measurable[mΩ] A) (hp : Measurable[mΩ] p)
    (hyrange : ∀ᵐ ω ∂μ,y ω∈Icc (0:ℝ) 1)
    (hconsistency : ∀ᵐ ω ∂μ,A ω=j→y ω=p ω)
    (hex : CondIndepFun m hm A p μ)
    (hpositive : ∀ᵐ ω ∂μ,μ[binaryIndicator j∘A|m] ω≠0) :
    ∀ᵐ ω ∂μ,p ω∈Icc (0:ℝ) 1 := by
  let : MeasurableSpace Ω := mΩ
  let r := binaryIndicator j∘A
  let b := outsideUnitIndicator∘p
  have hr : Measurable r := (binaryIndicator_measurable j).comp hA
  have hb : Measurable b := outsideUnitIndicator_measurable.comp hp
  have hir : Integrable r μ := Integrable.of_mem_Icc 0 1 hr.aemeasurable
    (Eventually.of_forall (fun ω=>binaryIndicator_range j (A ω)))
  have hib : Integrable b μ := Integrable.of_mem_Icc 0 1 hb.aemeasurable
    (Eventually.of_forall (fun ω=>outsideUnitIndicator_range (p ω)))
  have hrb : Integrable (fun ω=>r ω*b ω) μ := hir.mul_bdd (c:=1) hb.aestronglyMeasurable
    (Eventually.of_forall (fun ω=>by
      change |outsideUnitIndicator (p ω)|≤1
      rw [abs_of_nonneg (outsideUnitIndicator_range (p ω)).1]
      exact (outsideUnitIndicator_range (p ω)).2))
  have hzero : (fun ω=>r ω*b ω)=ᵐ[μ] 0 := by
    filter_upwards [hyrange,hconsistency] with ω hrange hc
    by_cases h:A ω=j
    · have hpunit : p ω∈Icc (0:ℝ) 1 := by rw [←hc h];exact hrange
      simp [r,b,binaryIndicator,outsideUnitIndicator,h,hpunit]
    · simp [r,binaryIndicator,h]
  have hprod := condExp_product_of_condIndep μ m hm r b hr hb hir hib hrb
    (hex.comp (binaryIndicator_measurable j) outsideUnitIndicator_measurable)
  have hzc := condExp_congr_ae hzero (m:=m)
  rw [condExp_zero] at hzc
  have hbc : μ[b|m]=ᵐ[μ] 0 := by
    filter_upwards [hprod,hzc,hpositive] with ω hp hz hpos
    change μ[r|m] ω≠0 at hpos
    change μ[b|m] ω=0
    rw [hz] at hp
    exact (mul_eq_zero.mp hp.symm).resolve_left hpos
  have hbi : (∫ ω,b ω ∂μ)=0 := by
    rw [←integral_condExp hm (f:=b),integral_congr_ae hbc]
    simp
  have hba : b=ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg
    (fun ω=>(outsideUnitIndicator_range (p ω)).1) hib).mp hbi
  filter_upwards [hba] with ω hω
  by_contra h
  simp [b,outsideUnitIndicator,h] at hω

def clipOutcome (y : ℝ) : Applications.MAR.Outcome :=
  ⟨max 0 (min 1 y),le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clipOutcome_measurable : Measurable clipOutcome :=
  (measurable_const.max (measurable_const.min measurable_id)).subtype_mk

theorem clipOutcome_coe_eq (y : ℝ) (hy : y∈Icc (0:ℝ) 1) : (clipOutcome y:ℝ)=y := by
  dsimp only [clipOutcome]
  rw [min_eq_right hy.2,max_eq_right hy.1]

theorem clipOutcome_subtype (y : Applications.MAR.Outcome) : clipOutcome (y:ℝ)=y :=
  Subtype.ext (clipOutcome_coe_eq (y:ℝ) y.property)

end RoughRegime.Causal
