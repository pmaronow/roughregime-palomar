module

public import RoughRegime.SeparatedMARSourceSmooth
public import RoughRegime.SeparatedMARParametricSmooth


@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option maxHeartbeats 1500000

theorem smooth_augmentable_lowerBracket (A : Model.Parameters)
    (hδ : A.δ < 1/2) (hlo : A.gminus < 1) (hhi : 1 < A.gplus) (hH : 1 < A.H) :
    Model.LowerBracket (target A.d) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · obtain ⟨c,hc,n0,hn0,hbound⟩ := smooth_augmentable_rough_lower A hδ hlo hhi hH hrough
    refine ⟨c,hc,n0,hn0,?_⟩
    intro n hn
    have hb := hbound n hn
    refine ⟨?_,fun _=>?_⟩
    · simpa only [Model.lowerBracketScale,Model.Parameters.bracketParameters,ite_true,hrough,mul_assoc] using hb.1
    · have hquarter : (1/4:ℝ≥0∞)≤3/8 := by
        have hh := ENNReal.ofReal_le_ofReal (by norm_num : (1/4:ℝ)≤3/8)
        simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4),
          ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8),ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hh
      simpa only [Model.lowerBracketScale,Model.Parameters.bracketParameters,ite_true,hrough,mul_assoc]
        using hquarter.trans hb.2
  · obtain ⟨c,hc,he⟩ := smooth_constantAugmentable_parametric_lower A hδ.le ⟨hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket A _ _ (le_of_not_gt hrough)
    refine ⟨c,hc,he.mono ?_⟩
    intro n hn
    exact hn.1.trans (Model.minimaxRMSE_mono_class n _ (fun P hP=>⟨constantAugmentable_subset A hP.1,hP.2⟩))

theorem smooth_lowerBracket (A : Model.Parameters)
    (hδ : A.δ < 1/2) (hlo : A.gminus < 1) (hhi : 1 < A.gplus) (hH : 1 < A.H) :
    Model.LowerBracket (target A.d) (modelClass A ∩ Model.smoothDensityClass A.d Response) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,hbound⟩ := smooth_augmentable_lowerBracket A hδ hlo hhi hH
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  exact ⟨(hbound n hn).1.trans (Model.minimaxRMSE_mono_class n _ (fun P hP=>⟨augmentable_subset A hP.1,hP.2⟩)),
    fun hrough=>(hbound n hn).2 hrough |>.trans (Model.minimaxTail_mono_class n _ _ (fun P hP=>⟨augmentable_subset A hP.1,hP.2⟩))⟩

end RoughRegime.Applications.SeparatedMAR
