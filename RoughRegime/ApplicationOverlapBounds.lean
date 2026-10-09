module

public import RoughRegime.ApplicationOverlapClass


@[expose] public section
/-! The actual conditional-covariance and treatment-variance ranges used in
the overlap ratio reduction, derived from bounded responses and overlap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem residual_energy_le_quarter {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (f : Ω→ℝ) (hf : Measurable f) (hr : ∀ x,f x∈Icc (0:ℝ) 1) :
    (∫ x,(f x-(μ[f|m]) x)^2 ∂μ) ≤ 1/4 := by
  have hL : MemLp f 2 μ := bounded_memLp μ f hf 1 fun x => by
    rw [abs_of_nonneg (hr x).1]; exact (hr x).2
  have he := ConditionalExamples.conditional_variance_is_optimal_prediction_loss hm f (fun _ => (1/2:ℝ))
    hL (memLp_const _) stronglyMeasurable_const
  unfold condVar at he
  rw [integral_condExp hm] at he
  change (∫ x,(f x-(μ[f|m]) x)^2 ∂μ) ≤ _ at he
  refine he.trans ?_
  have hi : Integrable (fun x=>(f x-1/2)^2) μ := (hL.sub (memLp_const _)).integrable_sq
  calc
    _ ≤ ∫ _x,(1/4:ℝ) ∂μ := integral_mono hi (integrable_const _) fun x => by
      have hx := hr x
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    _ = _ := by simp

theorem numerator_bound (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) : |numerator A.d P|≤1/4 := by
  let μ : Measure (Model.Covariate A.d×Response) := P
  have hm : Model.covariateInformation A Response ≤
      (inferInstance : MeasurableSpace (Model.Covariate A.d×Response)) := measurable_fst.comap_le
  let f : Model.Covariate A.d×Response→ℝ := treatment∘Prod.snd
  let g : Model.Covariate A.d×Response→ℝ := outcome∘Prod.snd
  have hf : Measurable f := treatment_measurable.comp measurable_snd
  have hg : Measurable g := outcome_measurable.comp measurable_snd
  have hfl : MemLp f 2 μ := bounded_memLp μ f hf 1 fun x => treatment_bound x.2
  have hgl : MemLp g 2 μ := bounded_memLp μ g hg 1 fun x => outcome_bound x.2
  have hfr : MemLp (f-μ[f|Model.covariateInformation A Response]) 2 μ := hfl.sub (hfl.condExp one_le_two)
  have hgr : MemLp (g-μ[g|Model.covariateInformation A Response]) 2 μ := hgl.sub (hgl.condExp one_le_two)
  have hprod : Integrable (fun x=>(f x-(μ[f|Model.covariateInformation A Response]) x)*(g x-(μ[g|Model.covariateInformation A Response]) x)) μ :=
    memLp_one_iff_integrable.mp (hfr.mul hgr)
  have hef := residual_energy_le_quarter μ hm f hf fun x => treatment_range x.2
  have heg := residual_energy_le_quarter μ hm g hg fun x => outcome_range x.2
  change |∫ x,μ[(f-μ[f|Model.covariateInformation A Response])*(g-μ[g|Model.covariateInformation A Response])|Model.covariateInformation A Response] x ∂μ|≤1/4
  rw [integral_condExp hm]
  change |∫ x,(f x-(μ[f|Model.covariateInformation A Response]) x)*(g x-(μ[g|Model.covariateInformation A Response]) x) ∂μ|≤1/4
  calc
    _ ≤ ∫ x,|(f x-(μ[f|Model.covariateInformation A Response]) x)*(g x-(μ[g|Model.covariateInformation A Response]) x)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x=>(f x-(μ[f|Model.covariateInformation A Response]) x)*(g x-(μ[g|Model.covariateInformation A Response]) x))
    _ ≤ ∫ x,((f x-(μ[f|Model.covariateInformation A Response]) x)^2+(g x-(μ[g|Model.covariateInformation A Response]) x)^2)/2 ∂μ :=
      integral_mono hprod.abs ((hfr.integrable_sq.add hgr.integrable_sq).div_const 2) fun x => by
        rw [abs_mul]
        nlinarith [sq_nonneg (|f x-(μ[f|Model.covariateInformation A Response]) x|-|g x-(μ[g|Model.covariateInformation A Response]) x|),
          sq_abs (f x-(μ[f|Model.covariateInformation A Response]) x),sq_abs (g x-(μ[g|Model.covariateInformation A Response]) x)]
    _ = ((∫ x,(f x-(μ[f|Model.covariateInformation A Response]) x)^2 ∂μ)+(∫ x,(g x-(μ[g|Model.covariateInformation A Response]) x)^2 ∂μ))/2 := by
      rw [integral_div]
      simpa only [Pi.sub_apply] using congrArg (fun r : ℝ=>r/2)
        (integral_add hfr.integrable_sq hgr.integrable_sq)
    _ ≤ _ := by linarith

theorem Witness.overlap_on_observations (A : Model.Parameters) (ε : ℝ)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A ε P) :
    ∀ᵐ o ∂(P:Measure (Model.Covariate A.d×Response)), ε≤W.mU o.1 ∧ W.mU o.1≤1-ε := by
  apply ae_of_ae_map (μ := (P:Measure (Model.Covariate A.d×Response))) (f:=Prod.fst)
    (p:=fun x=>ε≤W.mU x ∧ W.mU x≤1-ε) measurable_fst.aemeasurable
  rw [W.marginal]
  exact W.overlap.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

theorem Witness.denominator_eq (A : Model.Parameters) (ε : ℝ)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A ε P) :
    denominator A.d P=∫ o,W.mU o.1*(1-W.mU o.1) ∂(P:Measure (Model.Covariate A.d×Response)) := by
  have hm : Model.covariateInformation A Response ≤
      (inferInstance : MeasurableSpace (Model.Covariate A.d×Response)) := measurable_fst.comap_le
  have hl : MemLp (treatment∘Prod.snd) 2 (P:Measure (Model.Covariate A.d×Response)) :=
    bounded_memLp (P:Measure (Model.Covariate A.d×Response)) _
      (treatment_measurable.comp measurable_snd) 1 fun o=>treatment_bound o.2
  rw [denominator,ConditionalExamples.mean_conditional_variance hm _ hl]
  simp_rw [Function.comp_apply,treatment_sq]
  have hmean := integral_condExp hm (μ:=(P:Measure (Model.Covariate A.d×Response))) (f:=treatment∘Prod.snd)
  simp only [Function.comp_apply] at hmean
  rw [← hmean]
  rw [← integral_sub integrable_condExp (hl.condExp one_le_two).integrable_sq]
  apply integral_congr_ae
  filter_upwards [W.momentU] with o ho
  change _=W.mU o.1 at ho
  rw [ho]
  ring

theorem denominator_bounds (A : Model.Parameters) (ε : ℝ) (_hε : 0<ε) (_hεhalf : ε<1/2)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A ε P) :
    ε*(1-ε)≤denominator A.d P ∧ denominator A.d P≤1/4 := by
  have hl : MemLp (treatment∘Prod.snd) 2 (P:Measure (Model.Covariate A.d×Response)) :=
    bounded_memLp (P:Measure (Model.Covariate A.d×Response)) _
      (treatment_measurable.comp measurable_snd) 1 fun o=>treatment_bound o.2
  have hw : MemLp (W.mU∘Prod.fst) 2 (P:Measure (Model.Covariate A.d×Response)) :=
    (hl.condExp (m:=Model.covariateInformation A Response) one_le_two).ae_eq W.momentU
  have hi : Integrable (fun o=>W.mU o.1*(1-W.mU o.1)) (P:Measure (Model.Covariate A.d×Response)) := by
    have he : (fun o : Model.Covariate A.d×Response=>W.mU o.1*(1-W.mU o.1))=
        (fun o=>W.mU o.1-(W.mU o.1)^2) := by funext o;ring
    rw [he]
    exact (hw.integrable one_le_two).sub hw.integrable_sq
  rw [W.denominator_eq A ε P]
  constructor
  · have he := integral_mono_ae (integrable_const (ε*(1-ε))) hi
      ((W.overlap_on_observations A ε P).mono fun o ho=>by
        nlinarith [mul_nonneg (sub_nonneg.mpr ho.1) (sub_nonneg.mpr ho.2)])
    simpa using he
  · have he := integral_mono_ae hi (integrable_const (1/4:ℝ))
      (ae_of_all _ fun o=>by nlinarith [sq_nonneg (W.mU o.1-1/2)])
    simpa using he

 theorem effect_range (A : Model.Parameters) (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (hP : P∈modelClass A ε) :
    effect A.d P∈Icc (-(1/(4*(ε*(1-ε))))) (1/(4*(ε*(1-ε)))) := by
  obtain ⟨W⟩:=hP
  have hc : 0<ε*(1-ε):=mul_pos hε (by linarith)
  have hd: ε*(1-ε)≤denominator A.d P:=(denominator_bounds A ε hε hεhalf P W).1
  have hd0:=hc.trans_le hd
  apply abs_le.mp
  rw [effect,abs_div,abs_of_pos hd0]
  have h:=div_le_div₀ (by norm_num : (0:ℝ)≤1/4) (numerator_bound A P) hc hd
  simpa only [div_div] using h

end RoughRegime.Applications.Overlap
