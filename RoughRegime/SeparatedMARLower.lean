module

public import RoughRegime.SeparatedMARPath
public import RoughRegime.SourceRoughLower


@[expose] public section
/-! Full separated MAR lower bracket with the unexpanded design interval,
including the actual rough-regime quarter probability clause. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
open RoughRegime.LatticePriors RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem augmentable_dimension_rough_lower (A0 : Model.Parameters) (D : ℕ)
    (hδ : A0.δ < 1/2) (hlo : A0.gminus < 1) (hhi : 1 < A0.gplus) (hH : 1 < A0.H)
    (hrough : (A0.withDimension D).theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n (A0.withDimension D).theta
        (Rates.tau A0.gminus A0.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (target (D+1)) (augmentableClass (A0.withDimension D)) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (target (D+1)) (augmentableClass (A0.withDimension D))
        (2*c*Rates.subcriticalScale n (A0.withDimension D).theta (Rates.tau A0.gminus A0.gplus)*Real.log n) := by
  let A := A0.withDimension D
  let B0 := lowerParameters A0
  let B := B0.withDimension D
  have hloB : max B.δ B.gminus<1/2 := by
    apply max_lt hδ
    change A0.gminus/2<1/2
    linarith
  have hhiB : 1/2<B.gplus := by change 1/2<A0.gplus/2; linarith
  have hHB : 2<B.H := (by norm_num : (2:ℝ)<3).trans_le (le_max_left _ _)
  obtain ⟨F,hF⟩ := nondegenerate_source_model_family_smaller B0 D (MAR.observables B le_rfl) MAR.baseline
    (MAR.baseline_nondegenerate B le_rfl hloB hhiB hHB)
  obtain ⟨G,hG,_hScores,_hVolume,_hThreshold,hExtra⟩ := F.exists_universal_selected_extra_family hF
    (extraConditions A0) (extra_baseline A0 D F hδ (by linarith))
  have hθ : 0<B.theta := B.theta_pos
  have hτ : 0<Rates.tau G.rminus G.rplus := Rates.tau_pos _ _ G.interval.1
    (G.interval.2.1.trans G.interval.2.2)
  have ht : Model.target B (MAR.observables B le_rfl) = target (D+1) :=
    funext (MAR.generic_target_eq_observedMean B le_rfl)
  have hb := G.source_family_rough_lower hG hrough (augmentableClass A) (by
    intro c0
    filter_upwards [hExtra B.theta (Rates.tau G.rminus G.rplus) c0 1 hθ hrough hτ zero_lt_one] with n hn
    obtain ⟨V,hsmall,hconditions⟩ := hn
    refine ⟨V,hsmall,?_⟩
    intro z
    exact source_mem_augmentable A G.scores (MAR.source_scores_positive B0 D le_rfl G)
      ((G.selectedFrame B.theta (Rates.tau G.rminus G.rplus) c0 n V).field z) hsmall (hconditions z).2)
  rw [ht] at hb
  have hta : Rates.tau B0.gminus B0.gplus=Rates.tau A0.gminus A0.gplus := lowerParameters_tau A0
  rw [hta] at hb
  exact hb

theorem augmentable_rough_lower (A : Model.Parameters)
    (hδ : A.δ < 1/2) (hlo : A.gminus < 1) (hhi : 1 < A.gplus) (hH : 1 < A.H)
    (hrough : A.theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (target A.d) (augmentableClass A) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (target A.d) (augmentableClass A)
        (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) := by
  cases A with
  | mk d alpha beta H delta gminus gplus M0 hd ha hb hH0 hdelta hgminus hgplus hM0 =>
    cases d with
    | zero => omega
    | succ D =>
      exact augmentable_dimension_rough_lower
        ⟨D+1,alpha,beta,H,delta,gminus,gplus,M0,hd,ha,hb,hH0,hdelta,hgminus,hgplus,hM0⟩
        D hδ hlo hhi hH hrough

theorem augmentable_lowerBracket (A : Model.Parameters)
    (hδ : A.δ < 1/2) (hlo : A.gminus < 1) (hhi : 1 < A.gplus) (hH : 1 < A.H) :
    Model.LowerBracket (target A.d) (augmentableClass A) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · obtain ⟨c,hc,n0,hn0,hbound⟩ := augmentable_rough_lower A hδ hlo hhi hH hrough
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
  · obtain ⟨c,hc,he⟩ := augmentable_parametric_lower A hδ.le ⟨hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket A _ _ (le_of_not_gt hrough)
    exact ⟨c,hc,he.mono (fun _ hn=>hn.1)⟩

theorem lowerBracket (A : Model.Parameters)
    (hδ : A.δ < 1/2) (hlo : A.gminus < 1) (hhi : 1 < A.gplus) (hH : 1 < A.H) :
    Model.LowerBracket (target A.d) (modelClass A) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,hbound⟩ := augmentable_lowerBracket A hδ hlo hhi hH
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  exact ⟨(hbound n hn).1.trans (Model.minimaxRMSE_mono_class n _ (augmentable_subset A)),
    fun hrough=>(hbound n hn).2 hrough |>.trans (Model.minimaxTail_mono_class n _ _ (augmentable_subset A))⟩

end RoughRegime.Applications.SeparatedMAR
