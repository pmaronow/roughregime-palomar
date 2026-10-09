module

public import RoughRegime.SeparatedMARPath
public import RoughRegime.ApplicationSmoothDensity


@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option maxHeartbeats 1500000

theorem smooth_constantAugmentable_parametric_lower (A : Model.Parameters) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1 ∧ 1 ≤ A.gplus) (hH : 1 ≤ A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤
        Model.minimaxRMSE n (target A.d) (constantAugmentableClass A ∩ Model.smoothDensityClass A.d Response) ∧
      (1/4:ℝ≥0∞) ≤ Model.minimaxTail n (target A.d) (constantAugmentableClass A ∩ Model.smoothDensityClass A.d Response)
        (2*c*(n:ℝ)^(-(1/2:ℝ))) := by
  let G := lowerParameters A
  have hG : 1≤G.M0 := le_rfl
  have htarget : Model.target G (MAR.observables G hG) = target A.d :=
    funext (MAR.generic_target_eq_observedMean G hG)
  have hderiv : HasDerivAt (fun t=>target A.d (MAR.parametricLaw G t).probabilityMeasure) 1 0 := by
    rw [←htarget]
    apply ((hasDerivAt_id (0:ℝ)).const_add (1/2)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : -(1/8:ℝ)<0) (by norm_num : (0:ℝ)<1/8)] with t ht
    rw [MAR.parametricLaw_target G hG t,AffineResponseLower.clip_eq ht]
    rfl
  apply LowerMeasure.parametric_path_minimax_bound (MAR.parametricLaw G) (fun _=>1)
    (fun o=>MAR.regressionScore o.2) (target A.d) (constantAugmentableClass A ∩ Model.smoothDensityClass A.d Response)
    (-(1/8)) (1/8) 0 1 (1/2) 2 (by norm_num) hderiv one_ne_zero (by norm_num) (by norm_num)
  · intro t ht
    apply Eventually.of_forall
    intro o
    change 1+0*0+AffineResponseLower.clip (1/8) t*MAR.regressionScore o.2=1+t*MAR.regressionScore o.2
    rw [AffineResponseLower.clip_eq ht]
    ring
  · intro t ht
    apply Eventually.of_forall
    intro o
    have h := AffineResponseLower.affine_density_lower (fun _ : Response=>0) MAR.regressionScore
      0 (1/8) 2 t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun _=>by norm_num) MAR.regressionScore_bound o.2
    simpa only [zero_mul,add_zero,AffineResponseLower.clip_eq ht] using h
  · exact Eventually.of_forall (fun o=>MAR.regressionScore_bound o.2)
  · intro t _
    refine ⟨parametricLaw_mem_constantAugmentable A hδ hg hH t,?_⟩
    rw [MAR.parametricLaw_eq_product]
    exact Model.productLaw_mem_smoothDensityClass G (MAR.responsePath t).probabilityMeasure

end RoughRegime.Applications.SeparatedMAR
