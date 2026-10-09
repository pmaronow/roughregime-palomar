module

public import RoughRegime.SeparatedMARLower
public import RoughRegime.ApplicationSmoothDensity


@[expose] public section
/-! Literal separated MAR hard laws with actual globally smooth design
densities and no uniform density derivative bound. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
open RoughRegime.LatticePriors RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem smooth_augmentable_dimension_rough_lower (A0 : Model.Parameters) (D : ℕ)
    (hδ : A0.δ < 1/2) (hlo : A0.gminus < 1) (hhi : 1 < A0.gplus) (hH : 1 < A0.H)
    (hrough : (A0.withDimension D).theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n (A0.withDimension D).theta
        (Rates.tau A0.gminus A0.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (target (D+1)) (augmentableClass (A0.withDimension D) ∩ Model.smoothDensityClass (D+1) Response) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (target (D+1)) (augmentableClass (A0.withDimension D) ∩ Model.smoothDensityClass (D+1) Response)
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
  have hb := G.source_family_rough_lower hG hrough (augmentableClass A ∩ Model.smoothDensityClass A.d Response) (by
    intro c0
    filter_upwards [hExtra B.theta (Rates.tau G.rminus G.rplus) c0 1 hθ hrough hτ zero_lt_one] with n hn
    obtain ⟨V,hsmall,hconditions⟩ := hn
    refine ⟨V,hsmall,?_⟩
    intro z
    refine ⟨?_, (G.selectedFrame B.theta (Rates.tau G.rminus G.rplus) c0 n V).observationProbability_mem_smoothDensityClass
      MAR.baseline G.scores hsmall z⟩
    exact source_mem_augmentable A G.scores (MAR.source_scores_positive B0 D le_rfl G)
      ((G.selectedFrame B.theta (Rates.tau G.rminus G.rplus) c0 n V).field z) hsmall (hconditions z).2)
  rw [ht] at hb
  have hta : Rates.tau B0.gminus B0.gplus=Rates.tau A0.gminus A0.gplus := lowerParameters_tau A0
  rw [hta] at hb
  exact hb

theorem smooth_augmentable_rough_lower (A : Model.Parameters)
    (hδ : A.δ < 1/2) (hlo : A.gminus < 1) (hhi : 1 < A.gplus) (hH : 1 < A.H)
    (hrough : A.theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (target A.d) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (target A.d) (augmentableClass A ∩ Model.smoothDensityClass A.d Response)
        (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) := by
  cases A with
  | mk d alpha beta H delta gminus gplus M0 hd ha hb hH0 hdelta hgminus hgplus hM0 =>
    cases d with
    | zero => omega
    | succ D =>
      exact smooth_augmentable_dimension_rough_lower
        ⟨D+1,alpha,beta,H,delta,gminus,gplus,M0,hd,ha,hb,hH0,hdelta,hgminus,hgplus,hM0⟩
        D hδ hlo hhi hH hrough

end RoughRegime.Applications.SeparatedMAR
