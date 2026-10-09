module

public import RoughRegime.SpatialPredictionLower
public import RoughRegime.SmoothBracketTools


@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Products
namespace SineSetup
variable {A : Model.Parameters} (S : SineSetup A)

theorem probabilityLaw_mem_smoothDensityClass (t : ℝ) :
    S.probabilityLaw t∈Model.smoothDensityClass A.d BoundedResponse := by
  refine ⟨fun _=>1,contDiff_const,?_⟩
  exact SpatialAffine.law_marginal diagonalScores (S.field t) (S.field_small t)

end SineSetup

theorem smooth_explained_parametric_lower (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (explainedTarget A) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) := by
  let S:=sineSetup A
  exact S.path_minimax_bound _ _ (1/2) ((1/2)*S.eta^2) (by norm_num)
    (S.explained_hasDerivAt _ (by norm_num))
    (by have:=S.positive; positivity) (fun t _=>⟨S.quadraticClass_member hab hlo hhi t,S.probabilityLaw_mem_smoothDensityClass t⟩)

theorem smooth_determination_parametric_lower (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus)
    (vmin : ℝ) (hv : vmin≤1) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (determinationTarget A) (positiveVarianceClass A vmin ∩ Model.smoothDensityClass A.d BoundedResponse) := by
  let S:=sineSetup A
  apply S.path_minimax_bound _ _ (1/2) ((1/2)*S.eta^2) (by norm_num)
    (S.determination_hasDerivAt _ (by norm_num)) (by have:=S.positive; positivity)
  intro t _
  exact ⟨⟨S.quadraticClass_member hab hlo hhi t,by rw [S.responseVariance_one]; exact hv⟩,
    S.probabilityLaw_mem_smoothDensityClass t⟩

theorem smooth_excessLoss_parametric_lower (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus)
    (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0)
    (M : ℝ) (hb : ∀x,|f0 x|≤M) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) := by
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
    (fun t _=>⟨S.quadraticClass_member hab hlo hhi t,S.probabilityLaw_mem_smoothDensityClass t⟩)

/-- The known predictor needs to be bounded only on the source cube. -/
theorem smooth_excessLoss_parametric_lower_cube (A : Model.Parameters)
    (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus)
    (f0 : Model.Covariate A.d→ℝ) (hf : Measurable f0)
    (M : ℝ) (hM : 0≤M) (hb : ∀x∈Model.cube A.d,|f0 x|≤M) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤
        Model.minimaxRMSE n (excessLoss A f0) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) := by
  let f:=(Model.cube A.d).indicator f0
  have hcube:MeasurableSet (Model.cube A.d):=(Model.isCompact_cube A.d).isClosed.measurableSet
  have hfb : ∀x,|f x|≤M := by
    intro x
    by_cases hx:x∈Model.cube A.d
    · simpa only [f,indicator_of_mem hx] using hb x hx
    · simpa only [f,indicator_of_notMem hx,abs_zero] using hM
  obtain ⟨c,hc,he⟩:=smooth_excessLoss_parametric_lower A hab hlo hhi f (hf.indicator hcube) M hfb
  refine ⟨c,hc,he.mono (fun n hn=>?_)⟩
  rw [Model.minimaxRMSE_congr_target n (excessLoss A f0) (excessLoss A f) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) ?_]
  · exact hn
  · intro P hP
    apply integral_congr_ae
    filter_upwards [quadraticClass_covariate_cube A P hP.1] with o ho
    simp only [f,indicator_of_mem ho]

end RoughRegime.Applications.Products
