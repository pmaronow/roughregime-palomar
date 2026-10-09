module

public import RoughRegime.ApplicationOverlapParametric
public import RoughRegime.SmoothDensityLower


@[expose] public section
/-! The actual correlated overlap-effect path has constant smooth density. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace RoughRegime.Applications.Overlap
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

theorem correlationLaw_mem_smoothDensityClass (A : Model.Parameters) (t : ℝ) :
    (correlationLaw A t).probabilityMeasure∈Model.smoothDensityClass A.d Response := by
  refine ⟨fun _=>1,contDiff_const,?_⟩
  exact law_marginal correlationScores (correlationField A.d t)
    (by norm_num [correlationField,correlationScores])

 theorem smooth_parametric_lower (A : Model.Parameters) (ε : ℝ) (hε : ε<1/2)
    (hM : 1≤A.M0) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1/2<A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤ Model.minimaxRMSE n (effect A.d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response)) ∧
      (1/4:ℝ≥0∞)≤ Model.minimaxTail n (effect A.d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response)) (2*c*(n:ℝ)^(-(1/2:ℝ))) := by
  have he (t : ℝ) (ht : t∈Ioo (-1/4:ℝ) (1/4)) :
      AffineResponseLower.clip (1/4) t=t := AffineResponseLower.clip_eq_of_abs_le (abs_le.mpr ⟨by linarith [ht.1],ht.2.le⟩)
  have htarg : (fun t=>effect A.d (correlationLaw A t).probabilityMeasure)=ᶠ[𝓝 (0:ℝ)] id := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1/4:ℝ)<0) (by norm_num : (0:ℝ)<1/4)] with t ht
    rw [correlationLaw_effect A hM t,he t ht];rfl
  apply LowerMeasure.parametric_path_minimax_bound (correlationLaw A) (fun _=>1)
    (fun o=>correlationScore o.2) (effect A.d) ((modelClass A ε ∩ Model.smoothDensityClass A.d Response))
    (-1/4) (1/4) 0 1 (1/2) 1 (by norm_num)
    ((hasDerivAt_id (0:ℝ)).congr_of_eventuallyEq htarg) (by norm_num) (by norm_num) zero_le_one
  · intro t ht
    exact ae_of_all _ fun o=>by
      change 1*(1+0*0+AffineResponseLower.clip (1/4) t*correlationScore o.2)=1+t*correlationScore o.2
      rw [he t ht];ring
  · intro t ht
    exact ae_of_all _ fun o=>by
      have hq:=correlationScore_bound o.2
      have ht' : |t|≤1/4:=abs_le.mpr ⟨by linarith [ht.1],ht.2.le⟩
      have hprod:=mul_le_mul ht' hq (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)
      rw [← abs_mul] at hprod
      linarith [neg_le_abs (t*correlationScore o.2)]
  · exact ae_of_all _ fun o=>correlationScore_bound o.2
  · intro t _;exact ⟨correlationLaw_mem A ε t hε.le hlo.le hhi.le hH.le,correlationLaw_mem_smoothDensityClass A t⟩

end RoughRegime.Applications.Overlap
