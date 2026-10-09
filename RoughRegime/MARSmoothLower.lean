module

public import RoughRegime.ApplicationMARUpper
public import RoughRegime.MARSourceSmooth
public import RoughRegime.MARParametricSmooth


@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1500000

theorem smooth_augmentable_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.LowerBracket (Model.target A (observables A hM)) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · obtain ⟨c,hc,n0,hn0,hbound⟩ := smooth_augmentable_rough_lower A hM hlo hhi hH hrough
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
  · obtain ⟨c,hc,he⟩ := smooth_constantAugmentable_parametric_lower A hM
      ((le_max_left _ _).trans hlo.le) ⟨(le_max_right _ _).trans hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket A _ _ (le_of_not_gt hrough)
    refine ⟨c,hc,?_⟩
    filter_upwards [he] with n hn
    exact hn.1.trans (Model.minimaxRMSE_mono_class n _ (fun P hP=>⟨constantAugmentable_subset A hP.1,hP.2⟩))

end RoughRegime.Applications.MAR

namespace RoughRegime.Applications.MAR
open MeasureTheory Set

theorem smooth_mar_lowerBracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.LowerBracket (Model.target A (observables A hM))
      (modelClass A ∩ Model.smoothDensityClass A.d Response) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,hb⟩ := smooth_augmentable_lowerBracket A hM hlo hhi hH
  have hsub : augmentableClass A ∩ Model.smoothDensityClass A.d Response ⊆
      modelClass A ∩ Model.smoothDensityClass A.d Response := by
    rintro P ⟨⟨W,_⟩,hs⟩
    exact ⟨⟨W⟩,hs⟩
  refine ⟨c,hc,n0,hn0,fun n hn=>⟨(hb n hn).1.trans (Model.minimaxRMSE_mono_class n _ hsub),
    fun hrough=>(hb n hn).2 hrough |>.trans (Model.minimaxTail_mono_class n _ _ hsub)⟩⟩

theorem smooth_mar_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.Bracket (observedMean A.d) (modelClass A ∩ Model.smoothDensityClass A.d Response)
      A.bracketParameters (A.nu : ℝ) := by
  have hl := smooth_mar_lowerBracket A hM hlo hhi hH
  have ht : Model.target A (observables A hM)=observedMean A.d := funext (generic_target_eq_observedMean A hM)
  rw [ht] at hl
  exact ⟨hl,Model.upperBracket_mono_class _ _ _ Set.inter_subset_left (mar_upperBracket A hM)⟩

end RoughRegime.Applications.MAR
