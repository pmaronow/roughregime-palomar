module

public import RoughRegime.MARSourceMembership
public import RoughRegime.SourceRoughLower
public import RoughRegime.TreatmentParametricLower
public import RoughRegime.ProductBrackets


@[expose] public section
/-! Actual full MAR hard families satisfying both treatment-arm restrictions.
One fixed smaller-weight source family is chosen before every statistical
scale; the genuine finite H/I/W conditions prove its law membership. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace RoughRegime.Applications.MAR
open RoughRegime.LatticePriors RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem augmentable_dimension_rough_lower (A0 : Model.Parameters) (D : ℕ) (hM : 1 ≤ A0.M0)
    (hlo : max A0.δ A0.gminus < 1/2) (hhi : 1/2 < A0.gplus) (hH : 2 < A0.H)
    (hrough : (A0.withDimension D).theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n (A0.withDimension D).theta
        (Rates.tau A0.gminus A0.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (Model.target (A0.withDimension D) (observables (A0.withDimension D) hM))
          (augmentableClass (A0.withDimension D)) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n
        (Model.target (A0.withDimension D) (observables (A0.withDimension D) hM))
        (augmentableClass (A0.withDimension D))
        (2*c*Rates.subcriticalScale n (A0.withDimension D).theta (Rates.tau A0.gminus A0.gplus)*Real.log n) := by
  let A := A0.withDimension D
  obtain ⟨F,hF⟩ := nondegenerate_source_model_family_smaller A0 D (observables A hM) baseline
    (baseline_nondegenerate A hM hlo hhi hH)
  have hδ : A0.δ<1/2 := (le_max_left _ _).trans_lt hlo
  obtain ⟨G,hG,_hScores,_hVolume,_hThreshold,hExtra⟩ := F.exists_universal_selected_extra_family hF
    (treatmentExtraConditions A0) (treatmentExtra_baseline A0 D hM F hδ hH)
  have hθ : 0<A.theta := A.theta_pos
  have hτ : 0<Rates.tau G.rminus G.rplus := Rates.tau_pos _ _ G.interval.1
    (G.interval.2.1.trans G.interval.2.2)
  apply G.source_family_rough_lower hG hrough (augmentableClass A)
  intro c0
  filter_upwards [hExtra A.theta (Rates.tau G.rminus G.rplus) c0 1 hθ hrough hτ zero_lt_one] with n hn
  obtain ⟨V,hsmall,hconditions⟩ := hn
  refine ⟨V,hsmall,?_⟩
  intro z
  exact source_law_mem_augmentable A hM G.scores (source_scores_positive A0 D hM G)
    ((G.selectedFrame A.theta (Rates.tau G.rminus G.rplus) c0 n V).field z) hsmall (hconditions z).2

theorem augmentable_rough_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H)
    (hrough : A.theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (Model.target A (observables A hM)) (augmentableClass A) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (Model.target A (observables A hM)) (augmentableClass A)
        (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) := by
  cases A with
  | mk d alpha beta H delta gminus gplus M0 hd ha hb hH0 hdelta hgminus hgplus hM0 =>
    cases d with
    | zero => omega
    | succ D =>
      exact augmentable_dimension_rough_lower
        ⟨D+1,alpha,beta,H,delta,gminus,gplus,M0,hd,ha,hb,hH0,hdelta,hgminus,hgplus,hM0⟩
        D hM hlo hhi hH hrough

theorem constantAugmentable_subset (A : Model.Parameters) : constantAugmentableClass A ⊆ augmentableClass A := by
  rintro P ⟨W,c,_hc,hInv,hD⟩
  exact ⟨W,hInv,hD⟩

theorem augmentable_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.LowerBracket (Model.target A (observables A hM)) (augmentableClass A) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · obtain ⟨c,hc,n0,hn0,hbound⟩ := augmentable_rough_lower A hM hlo hhi hH hrough
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
  · obtain ⟨c,hc,he⟩ := constantAugmentable_parametric_lower A hM
      ((le_max_left _ _).trans hlo.le) ⟨(le_max_right _ _).trans hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket A _ _ (le_of_not_gt hrough)
    refine ⟨c,hc,?_⟩
    filter_upwards [he] with n hn
    exact hn.1.trans (Model.minimaxRMSE_mono_class n _ (constantAugmentable_subset A))

end RoughRegime.Applications.MAR
