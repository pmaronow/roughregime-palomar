module

public import RoughRegime.SourceRoughLower
public import RoughRegime.ModelEventualHardness
public import RoughRegime.ModelUpperConsequences


@[expose] public section
/-! The prescribed source priors retain their 3/8 hardness on the full model
class, before the final risk transfer weakens the probability to 1/4. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Model
open RoughRegime.LatticePriors RoughRegime.LatticePriors.SourceModelFamily

 theorem source_model_rough_hardness_dimension (A0 : Parameters) (D : ℕ)
    {Z : Type*} [MeasurableSpace Z] (O : Observables Z (A0.withDimension D))
    (π : ProbabilityMeasure Z) (hnd : Nondegenerate (A0.withDimension D) O π)
    (hrough : (A0.withDimension D).theta < 1/2) :
    ∃c:ℝ,0 < c ∧ ∀ᶠn:ℕ in atTop,
      (3/8:ℝ≥0∞) ≤ minimaxTail n (target (A0.withDimension D) O)
        (modelClass (A0.withDimension D) O)
        (2*c*lowerBracketScale (A0.withDimension D).bracketParameters n) := by
  obtain ⟨F,hF⟩:= nondegenerate_source_model_family A0 D O π hnd
  have hθ:= (A0.withDimension D).theta_pos
  have hτ:= Rates.tau_pos _ _ F.interval.1 (F.interval.2.1.trans F.interval.2.2)
  have hclass : ∀c0:ℝ,F.SelectedClassClaim (A0.withDimension D).theta
      (Rates.tau F.rminus F.rplus) c0 (modelClass (A0.withDimension D) O) := by
    intro c0
    filter_upwards [F.selectedClassClaim_local hF _ _ c0 1 hθ hrough hτ zero_lt_one] with n hn
    obtain ⟨V,hsmall,hm⟩:= hn
    exact ⟨V,hsmall,fun z => localClass_subset (A0.withDimension D) O π 1 (hm z)⟩
  obtain ⟨c,hc,n0,_,hb⟩:= F.source_family_rough_lower hF hrough _ hclass
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  have hs : lowerBracketScale (A0.withDimension D).bracketParameters n =
      Rates.subcriticalScale n (A0.withDimension D).theta (Rates.tau A0.gminus A0.gplus)*Real.log n := by
    unfold lowerBracketScale
    change (if (A0.withDimension D).theta<1/2 then _ else _)=_
    rw [ite_eq_left hrough]
    rfl
  rw [hs]
  convert (hb n hn).2 using 1
  congr 1
  ring

 theorem source_model_rough_hardness (A : Parameters)
    {Z : Type*} [MeasurableSpace Z] (O : Observables Z A)
    (π : ProbabilityMeasure Z) (hnd : Nondegenerate A O π) (hrough : A.theta < 1/2) :
    ∃c:ℝ,0 < c ∧ ∀ᶠn:ℕ in atTop,
      (3/8:ℝ≥0∞) ≤ minimaxTail n (target A O) (modelClass A O)
        (2*c*lowerBracketScale A.bracketParameters n) := by
  cases A with
  | mk d α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0 => cases d with
    | zero => omega
    | succ D =>
      exact source_model_rough_hardness_dimension
        (Parameters.mk (D+1) α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0)
        D O π hnd hrough

end RoughRegime.Model
