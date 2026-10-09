module

public import RoughRegime.SourceFinalScales
public import RoughRegime.SourceSelectedModel
public import RoughRegime.RhoScaling


@[expose] public section
/-! The actual selected source laws have all scale budgets derived from the
original model parameters and therefore satisfy the original local class. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SourceModelFamily

 theorem normalized_tau {A0 : Model.Parameters} {D : ℕ}
     {Z : Type*} [MeasurableSpace Z] {O : Model.Observables Z (A0.withDimension D)}
     {π : ProbabilityMeasure Z} (F : SourceModelFamily A0 D O π) :
     RoughRegime.Rates.tau F.rminus F.rplus = RoughRegime.Rates.tau A0.gminus A0.gplus := by
   have hw : 0 < Model.baselineW (A0.withDimension D) O π :=
     A0.hgminus.trans (lt_of_le_of_lt (le_max_right _ _) F.nondegenerate.2.1)
   exact RoughRegime.Rates.tau_div A0.gminus A0.gplus _ hw

 theorem normalized_rho {A0 : Model.Parameters} {D : ℕ}
     {Z : Type*} [MeasurableSpace Z] {O : Model.Observables Z (A0.withDimension D)}
     {π : ProbabilityMeasure Z} (F : SourceModelFamily A0 D O π) :
     RoughRegime.Rates.rho F.rminus F.rplus = RoughRegime.Rates.rho A0.gminus A0.gplus := by
   have hw : 0 < Model.baselineW (A0.withDimension D) O π :=
     A0.hgminus.trans (lt_of_le_of_lt (le_max_right _ _) F.nondegenerate.2.1)
   exact RoughRegime.Rates.rho_div A0.gminus A0.gplus _ hw

 /-- The literal eventual local-class membership of the fully selected source laws. -/
 def SelectedSourceLawClaim {A0 : Model.Parameters} {D : ℕ}
     {Z : Type*} [MeasurableSpace Z] {O : Model.Observables Z (A0.withDimension D)}
     {π : ProbabilityMeasure Z} (F : SourceModelFamily A0 D O π) (θ τ c0 r : ℝ) : Prop :=
     ∀ᶠ n : ℕ in atTop,
       ∃ (hN : 0 < selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)
         (hm : 0 < selectedSourceMultiplier A0 (D+1) θ τ n)
         (hd : 0 < sourceDensityMargin n) (hmargin : sourceDensityMargin n ≤ F.margin),
       let G := F.frame (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)
         (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ) hN
         (selectedSourceMultiplier A0 (D+1) θ τ n) (sourceDensityMargin n) hm hd hmargin
       ∃ hsmall : (G.Au+G.Av)/F.rminus*F.scores.C ≤ 1/4,
       ∀ z : GridPair D (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) →
         PairState (Fin (selectedSourceLevel A0 (D+1) θ τ n) × Fin (D+1)),
         (SpatialAffine.law F.scores (G.field z) hsmall).probabilityMeasure ∈
           Model.localClass (A0.withDimension D) O π r ∧
         (∀ x, |G.u z x| ≤ (n:ℝ)^(-(A0.α/(D+1:ℕ)))/F.rminus) ∧
         (∀ x, |G.v z x| ≤ (n:ℝ)^(-(A0.β/(D+1:ℕ)))/F.rminus)

 theorem eventually_final_selected_hard_laws {A0 : Model.Parameters} {D : ℕ}
     {Z : Type*} [MeasurableSpace Z] {O : Model.Observables Z (A0.withDimension D)}
     {π : ProbabilityMeasure Z} (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ c0 r : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) (hr : 0 < r) :
     ∀ᶠ n : ℕ in atTop,
       ∃ (hN : 0 < selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)
         (hm : 0 < selectedSourceMultiplier A0 (D+1) θ τ n)
         (hd : 0 < sourceDensityMargin n) (hmargin : sourceDensityMargin n ≤ F.margin),
       let G := F.frame (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)
         (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ) hN
         (selectedSourceMultiplier A0 (D+1) θ τ n) (sourceDensityMargin n) hm hd hmargin
       ∃ hsmall : (G.Au+G.Av)/F.rminus*F.scores.C ≤ 1/4,
       ∀ z : GridPair D (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) →
         PairState (Fin (selectedSourceLevel A0 (D+1) θ τ n) × Fin (D+1)),
         (SpatialAffine.law F.scores (G.field z) hsmall).probabilityMeasure ∈
           Model.localClass (A0.withDimension D) O π r ∧
         (∀ x, |G.u z x| ≤ (n:ℝ)^(-(A0.α/(D+1:ℕ)))/F.rminus) ∧
         (∀ x, |G.v z x| ≤ (n:ℝ)^(-(A0.β/(D+1:ℕ)))/F.rminus) := by
   exact F.eventually_selected_hard_laws hF θ τ c0 r hθ hθhalf hτ hr
     (selectedSourceVolume A0 (D+1) θ τ)
     (Eventually.of_forall (selectedSourceVolume_ge_one A0 (D+1) θ τ))
     (selectedSourceVolume_log_isBigO A0 (D+1) (Nat.succ_pos _) θ τ hθ hθhalf hτ)
     (fun n => selectedSourceLevel A0 (D+1) θ τ n)
     (fun n => selectedSourceMultiplier A0 (D+1) θ τ n)
     (Eventually.of_forall (fun n => (selectedSource_level_budgets A0 (D+1) θ τ n).1))
     (Eventually.of_forall (fun n => (selectedSource_level_budgets A0 (D+1) θ τ n).2.1))
     (Eventually.of_forall (fun n => (selectedSource_level_budgets A0 (D+1) θ τ n).2.2))

 /-- Original-assumption endpoint: the actual source family and every scale
 budget are constructed from nondegeneracy, with the paper's actual θ and τ. -/
 theorem original_selected_hard_laws (A0 : Model.Parameters) (D : ℕ)
     {Z : Type*} [MeasurableSpace Z] (O : Model.Observables Z (A0.withDimension D))
     (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate (A0.withDimension D) O π)
     (hrough : (A0.withDimension D).theta < 1/2) (c0 r : ℝ) (hr : 0 < r) :
     ∃ F : SourceModelFamily A0 D O π, F.Localized ∧
       F.SelectedSourceLawClaim (A0.withDimension D).theta
         (RoughRegime.Rates.tau A0.gminus A0.gplus) c0 r := by
   obtain ⟨F,hF⟩ := nondegenerate_source_model_family A0 D O π hnd
   have hθ : 0 < (A0.withDimension D).theta := by
     change 0 < (A0.α + A0.β)/(D+1 : ℕ)
     exact div_pos (add_pos A0.hα A0.hβ) (Nat.cast_pos.mpr (Nat.succ_pos _))
   have hτ : 0 < RoughRegime.Rates.tau A0.gminus A0.gplus :=
     RoughRegime.Rates.tau_pos _ _ A0.hgminus A0.hgplus
   exact ⟨F,hF,F.eventually_final_selected_hard_laws hF _ _ c0 r hθ hrough hτ hr⟩

end SourceModelFamily
end RoughRegime.LatticePriors
