module

public import RoughRegime.ApplicationOverlapProjection


@[expose] public section
/-! A bounded outcome and a genuinely binary treatment imply the sharp
absolute overlap-coefficient bound one, without a causal assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

theorem binary_covariance_abs_le_variance {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (a y : Ω→ℝ) (ha : Measurable[mΩ] a) (hy : Measurable[mΩ] y)
    (haBinary : ∀ x,a x=0 ∨ a x=1) (hyRange : ∀ x,y x∈Icc (0:ℝ) 1) :
    |covarianceMean μ m a y| ≤ varianceMean μ m a := by
  let :MeasurableSpace Ω:=mΩ
  have haRange : ∀ x,a x∈Icc (0:ℝ) 1:=by intro x;rcases haBinary x with h|h <;> simp [h]
  have haL : MemLp a 2 μ:=bounded_memLp μ a ha 1 fun x=>by
    rw [abs_of_nonneg (haRange x).1];exact (haRange x).2
  have hyL : MemLp y 2 μ:=bounded_memLp μ y hy 1 fun x=>by
    rw [abs_of_nonneg (hyRange x).1];exact (hyRange x).2
  have hcompL : MemLp (fun x=>1-a x) 2 μ:=(memLp_const 1).sub haL
  have hprod1 : Integrable (fun x=>a x*y x) μ:=memLp_one_iff_integrable.mp (haL.mul hyL)
  have hprod0 : Integrable (fun x=>(1-a x)*y x) μ:=memLp_one_iff_integrable.mp (hcompL.mul hyL)
  have hw0 : 0 ≤ᵐ[μ] μ[a|m]:=condExp_nonneg (ae_of_all μ fun x=>(haRange x).1)
  have hw1 : ∀ᵐ x ∂μ,μ[a|m] x ≤ 1:=condExp_le_nonneg_const (m:=m) zero_le_one
    (ae_of_all μ fun x=>(haRange x).2)
  have hu0 : 0 ≤ᵐ[μ] μ[(fun x=>a x*y x)|m]:=condExp_nonneg
    (ae_of_all μ fun x=>mul_nonneg (haRange x).1 (hyRange x).1)
  have hu1 : μ[(fun x=>a x*y x)|m] ≤ᵐ[μ] μ[a|m]:=condExp_mono hprod1
    (haL.integrable one_le_two) (ae_of_all μ fun x=>by
      nlinarith [mul_nonneg (haRange x).1 (sub_nonneg.mpr (hyRange x).2)])
  have hv0 : 0 ≤ᵐ[μ] μ[(fun x=>(1-a x)*y x)|m]:=condExp_nonneg
    (ae_of_all μ fun x=>mul_nonneg (sub_nonneg.mpr (haRange x).2) (hyRange x).1)
  have hv1 : μ[(fun x=>(1-a x)*y x)|m] ≤ᵐ[μ] μ[(fun x=>1-a x)|m]:=condExp_mono hprod0
    (hcompL.integrable one_le_two) (ae_of_all μ fun x=>by
      nlinarith [mul_nonneg (sub_nonneg.mpr (haRange x).2) (sub_nonneg.mpr (hyRange x).2)])
  have hcomp : μ[(fun x=>1-a x)|m]=ᵐ[μ] fun x=>1-μ[a|m] x:=by
    have h:=condExp_sub (integrable_const (1:ℝ)) (haL.integrable one_le_two) m
    filter_upwards [h] with x hx
    change μ[(fun _=>1)-a|m] x=_
    rw [hx]
    change μ[(fun _=>(1:ℝ))|m] x-μ[a|m] x=_
    rw [condExp_const hm]
  have hsum : μ[y|m]=ᵐ[μ] fun x=>μ[(fun x=>a x*y x)|m] x+μ[(fun x=>(1-a x)*y x)|m] x:=by
    have h:=condExp_add hprod1 hprod0 m
    have he : ((fun x=>a x*y x)+(fun x=>(1-a x)*y x))=y:=by funext x;dsimp;ring
    rw [he] at h
    exact h
  have hwL := haL.condExp (m:=m) one_le_two
  have hymL := hyL.condExp (m:=m) one_le_two
  have hiD : Integrable (fun x=>μ[a|m] x*(1-μ[a|m] x)) μ:=by
    have he : (fun x=>μ[a|m] x*(1-μ[a|m] x))=fun x=>μ[a|m] x-μ[a|m] x^2:=by funext x;ring
    rw [he];exact (hwL.integrable one_le_two).sub hwL.integrable_sq
  have hiWY : Integrable (fun x=>μ[a|m] x*μ[y|m] x) μ:=memLp_one_iff_integrable.mp (hwL.mul hymL)
  have hiN : Integrable (fun x=>μ[(fun x=>a x*y x)|m] x-μ[a|m] x*μ[y|m] x) μ:=
    integrable_condExp.sub hiWY
  have hN : covarianceMean μ m a y=∫ x,μ[(fun x=>a x*y x)|m] x-μ[a|m] x*μ[y|m] x ∂μ:=by
    unfold covarianceMean
    rw [ConditionalExamples.mean_conditional_covariance hm a y haL hyL,
      ← integral_condExp hm (f:=fun x=>a x*y x),integral_sub integrable_condExp hiWY]
  have hD : varianceMean μ m a=∫ x,μ[a|m] x*(1-μ[a|m] x) ∂μ:=by
    unfold varianceMean
    rw [ConditionalExamples.mean_conditional_variance hm a haL]
    have he : (fun x=>a x^2)=a:=by funext x;rcases haBinary x with h|h <;> simp [h]
    rw [he,← integral_condExp hm (f:=a),← integral_sub (hwL.integrable one_le_two) hwL.integrable_sq]
    congr 1;funext x;ring
  have hpoint : ∀ᵐ x ∂μ,
      -(μ[a|m] x*(1-μ[a|m] x)) ≤ μ[(fun x=>a x*y x)|m] x-μ[a|m] x*μ[y|m] x ∧
      μ[(fun x=>a x*y x)|m] x-μ[a|m] x*μ[y|m] x ≤ μ[a|m] x*(1-μ[a|m] x) := by
    filter_upwards [hw0,hw1,hu0,hu1,hv0,hv1,hcomp,hsum] with x hw0 hw1 hu0 hu1 hv0 hv1 hc hs
    rw [hc] at hv1
    rw [hs]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hw1) hu0,mul_nonneg hw0 (sub_nonneg.mpr hv1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hu1),mul_nonneg hw0 hv0]
  rw [hN,hD]
  apply abs_le.mpr
  constructor
  · have h:=integral_mono_ae hiD.neg hiN (hpoint.mono fun x hx=>hx.1)
    change (∫ x,-(μ[a|m] x*(1-μ[a|m] x)) ∂μ) ≤ _ at h
    rw [integral_neg] at h
    exact h
  · exact integral_mono_ae hiN hiD (hpoint.mono fun x hx=>hx.2)

/-- Sharp source bound on the literal overlap effect. -/
theorem effect_abs_le_one (Q : Model.Parameters) (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2)
    (P : ProbabilityMeasure (Model.Covariate Q.d×Response)) (W : Witness Q ε P) :
    |effect Q.d P| ≤ 1 := by
  have h:=binary_covariance_abs_le_variance (P:Measure (Model.Covariate Q.d×Response))
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    (treatment∘Prod.snd) (outcome∘Prod.snd)
    (treatment_measurable.comp measurable_snd) (outcome_measurable.comp measurable_snd)
    (fun o=>by unfold treatment MAR.armIndicator; simp only [Function.comp_apply];split_ifs <;> simp)
    (fun o=>outcome_range o.2)
  have hd : 0<denominator Q.d P:=
    (mul_pos hε (by linarith : 0<1-ε)).trans_le (denominator_bounds Q ε hε hεhalf P W).1
  change |numerator Q.d P| ≤ denominator Q.d P at h
  rw [effect,abs_div,abs_of_pos hd]
  exact (div_le_one hd).mpr h

end RoughRegime.Applications.Overlap
