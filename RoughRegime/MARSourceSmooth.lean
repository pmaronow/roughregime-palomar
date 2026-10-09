module

public import RoughRegime.MARAugmentableLower
public import RoughRegime.ApplicationSmoothDensity


@[expose] public section
/-! The actual MAR hard family has a C-infinity design density for every
realization, while no uniform derivative constraint is added. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace RoughRegime.Applications.MAR
open RoughRegime.LatticePriors RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem smooth_augmentable_dimension_rough_lower (A0 : Model.Parameters) (D : ℕ) (hM : 1 ≤ A0.M0)
    (hlo : max A0.δ A0.gminus < 1/2) (hhi : 1/2 < A0.gplus) (hH : 2 < A0.H)
    (hrough : (A0.withDimension D).theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n (A0.withDimension D).theta
        (Rates.tau A0.gminus A0.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (Model.target (A0.withDimension D) (observables (A0.withDimension D) hM))
          (augmentableClass (A0.withDimension D) ∩ Model.smoothDensityClass (D+1) Response) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n
        (Model.target (A0.withDimension D) (observables (A0.withDimension D) hM))
        (augmentableClass (A0.withDimension D) ∩ Model.smoothDensityClass (D+1) Response)
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
  apply G.source_family_rough_lower hG hrough (augmentableClass A ∩ Model.smoothDensityClass A.d Response)
  intro c0
  filter_upwards [hExtra A.theta (Rates.tau G.rminus G.rplus) c0 1 hθ hrough hτ zero_lt_one] with n hn
  obtain ⟨V,hsmall,hconditions⟩ := hn
  refine ⟨V,hsmall,?_⟩
  intro z
  refine ⟨?_, (G.selectedFrame A.theta (Rates.tau G.rminus G.rplus) c0 n V).observationProbability_mem_smoothDensityClass
    baseline G.scores hsmall z⟩
  exact source_law_mem_augmentable A hM G.scores (source_scores_positive A0 D hM G)
    ((G.selectedFrame A.theta (Rates.tau G.rminus G.rplus) c0 n V).field z) hsmall (hconditions z).2

theorem smooth_augmentable_rough_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H)
    (hrough : A.theta < 1/2) :
    ∃ c : ℝ,0<c ∧ ∃ n0 : ℕ,3≤n0 ∧ ∀ n : ℕ,n0≤n →
      ENNReal.ofReal (c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) ≤
        Model.minimaxRMSE n (Model.target A (observables A hM)) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) ∧
      (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (Model.target A (observables A hM)) (augmentableClass A ∩ Model.smoothDensityClass A.d Response)
        (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n) := by
  cases A with
  | mk d alpha beta H delta gminus gplus M0 hd ha hb hH0 hdelta hgminus hgplus hM0 =>
    cases d with
    | zero => omega
    | succ D =>
      exact smooth_augmentable_dimension_rough_lower
        ⟨D+1,alpha,beta,H,delta,gminus,gplus,M0,hd,ha,hb,hH0,hdelta,hgminus,hgplus,hM0⟩
        D hM hlo hhi hH hrough

end RoughRegime.Applications.MAR
