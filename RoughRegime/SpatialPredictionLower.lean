module

public import RoughRegime.SpatialContrastLower
public import RoughRegime.ProductPrediction


@[expose] public section
/-! A genuine root-n lower bound for the excess prediction loss of every
fixed measurable predictor bounded on the source covariate cube. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Products
namespace SineSetup
variable {A : Model.Parameters} (S : SineSetup A)

theorem excessLoss_value (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0)
    (M : ℝ) (hb : ∀x,|f0 x|≤M) (t : ℝ) :
    excessLoss A f0 (S.probabilityLaw t)=
      (clampedParameter t)^2*S.eta^2/2-
        2*clampedParameter t*(∫x,S.phi x*f0 x ∂Model.cubeVolume A.d)+
        ∫x,(f0 x)^2 ∂Model.cubeVolume A.d := by
  have hφ := Applications.bounded_memLp (Model.cubeVolume A.d) S.phi
    S.phi_smooth.continuous.measurable S.eta S.phi_bound
  have hfLp := Applications.bounded_memLp (Model.cubeVolume A.d) f0 hf M hb
  have hcross : Integrable (fun x=>S.phi x*f0 x) (Model.cubeVolume A.d) :=
    memLp_one_iff_integrable.mp (hφ.mul hfLp)
  unfold excessLoss
  have hs := S.conditional_mean t
  have he : (fun o=>((S.probabilityLaw t:Measure (Model.Observation A BoundedResponse))[
      (Subtype.val:BoundedResponse→ℝ)∘Prod.snd | Model.covariateInformation A BoundedResponse] o-f0 o.1)^2)
      =ᵐ[(S.probabilityLaw t:Measure (Model.Observation A BoundedResponse))]
      fun o=>(clampedParameter t*S.phi o.1-f0 o.1)^2 := by
    filter_upwards [hs] with o ho
    rw [ho]
  rw [integral_congr_ae he]
  have hint := SpatialAffine.law_integral_fst diagonalScores (S.field t) (S.field_small t)
    (fun x=>(clampedParameter t*S.phi x-f0 x)^2)
    (((measurable_const.mul S.phi_smooth.continuous.measurable).sub hf).pow_const 2)
    univ MeasurableSet.univ
  simp only [preimage_univ,Measure.restrict_univ] at hint
  change (∫o,(clampedParameter t*S.phi o.1-f0 o.1)^2
      ∂(SpatialAffine.law diagonalScores (S.field t) (S.field_small t)).measure)=
      ∫x,1*(clampedParameter t*S.phi x-f0 x)^2 ∂Model.cubeVolume A.d at hint
  simp only [one_mul] at hint
  change (∫o,(clampedParameter t*S.phi o.1-f0 o.1)^2
      ∂(SpatialAffine.law diagonalScores (S.field t) (S.field_small t)).measure)=_
  rw [hint]
  have hex : (fun x=>(clampedParameter t*S.phi x-f0 x)^2)=
      fun x=>(clampedParameter t)^2*(S.phi x)^2-
        (2*clampedParameter t)*(S.phi x*f0 x)+(f0 x)^2 := by funext x; ring
  rw [hex,integral_add (f := fun x=>(clampedParameter t)^2*(S.phi x)^2-(2*clampedParameter t)*(S.phi x*f0 x))
    (g := fun x=>(f0 x)^2) ((hφ.integrable_sq.const_mul _).sub (hcross.const_mul _)) hfLp.integrable_sq,
    integral_sub (f := fun x=>(clampedParameter t)^2*(S.phi x)^2)
      (g := fun x=>(2*clampedParameter t)*(S.phi x*f0 x))
      (hφ.integrable_sq.const_mul _) (hcross.const_mul _),
    integral_const_mul,integral_const_mul,S.phi_square]
  ring

theorem excessLoss_hasDerivAt (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0)
    (M : ℝ) (hb : ∀x,|f0 x|≤M) (t0 : ℝ) (ht0 : t0∈Ioo (-1) 1) :
    HasDerivAt (fun t=>excessLoss A f0 (S.probabilityLaw t))
      (t0*S.eta^2-2*(∫x,S.phi x*f0 x ∂Model.cubeVolume A.d)) t0 := by
  let B := ∫x,S.phi x*f0 x ∂Model.cubeVolume A.d
  let D := ∫x,(f0 x)^2 ∂Model.cubeVolume A.d
  have hp : HasDerivAt (fun t=>t^2*S.eta^2/2-2*t*B+D) (t0*S.eta^2-2*B) t0 := by
    convert ((((hasDerivAt_id t0).pow 2).mul_const (S.eta^2/2)).sub
      (((hasDerivAt_id t0).const_mul 2).mul_const B)).add_const D using 1 <;> simp <;> (try funext x) <;> ring
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht0.1 ht0.2] with t ht
  rw [S.excessLoss_value f0 hf M hb,clampedParameter_eq t ⟨ht.1.le,ht.2.le⟩]

end SineSetup

theorem excessLoss_parametric_lower (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus)
    (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0)
    (M : ℝ) (hb : ∀x,|f0 x|≤M) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A) := by
  let S:=sineSetup A
  let B:=∫x,S.phi x*f0 x ∂Model.cubeVolume A.d
  have hchoice : ∃t0:ℝ,t0∈Ioo (-1) 1 ∧ t0*S.eta^2-2*B≠0 := by
    by_cases hh : (1/2)*S.eta^2-2*B≠0
    · exact ⟨1/2,by norm_num,hh⟩
    · refine ⟨1/4,by norm_num,?_⟩
      have hη:=S.positive
      have hη2 : 0<S.eta^2 := sq_pos_of_pos hη
      push Not at hh
      intro hz
      nlinarith
  obtain ⟨t0,ht0,hD⟩:=hchoice
  exact S.path_minimax_bound _ _ t0 (t0*S.eta^2-2*B) ht0
    (S.excessLoss_hasDerivAt f0 hf M hb t0 ht0) hD
    (fun t _=>S.quadraticClass_member hab hlo hhi t)

/-- The known predictor needs to be bounded only on the source cube. -/
theorem excessLoss_parametric_lower_cube (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus)
    (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0)
    (M : ℝ) (hM : 0≤M) (hb : ∀x∈Model.cube A.d,|f0 x|≤M) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A) := by
  let f:=(Model.cube A.d).indicator f0
  have hcube:MeasurableSet (Model.cube A.d):=(Model.isCompact_cube A.d).isClosed.measurableSet
  have hfb : ∀x,|f x|≤M := by
    intro x
    by_cases hx:x∈Model.cube A.d
    · simpa only [f,indicator_of_mem hx] using hb x hx
    · simpa only [f,indicator_of_notMem hx,abs_zero] using hM
  obtain ⟨c,hc,he⟩:=excessLoss_parametric_lower A hab hlo hhi f (hf.indicator hcube) M hfb
  refine ⟨c,hc,he.mono (fun n hn=>?_)⟩
  rw [Model.minimaxRMSE_congr_target n (excessLoss A f0) (excessLoss A f) (quadraticClass A) ?_]
  · exact hn
  · intro P hP
    apply integral_congr_ae
    filter_upwards [quadraticClass_covariate_cube A P hP] with o ho
    simp only [f,indicator_of_mem ho]

end RoughRegime.Applications.Products
