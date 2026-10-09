module

public import RoughRegime.SeparatedTreatmentRisk
public import RoughRegime.SeparatedTreatmentParametric
public import RoughRegime.SeparatedTreatmentPilot
public import RoughRegime.ModelPilotLower
public import RoughRegime.RoughScaleDecay


@[expose] public section
/-! All original separated treatment lower rows, at the exact unexpanded
interval [pminus,pplus] and original radius H0 > 1. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedTreatment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem selected_true_eq (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1) :
    SeparatedMAR.selectedTreatmentClass (MAR.parametersWithBeta A β1 hβ1) true A.β A.hβ=
      modelClass A β1 hβ1 := by
  cases A
  rfl

theorem ate_lowerBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Model.LowerBracket (MAR.ate A.d) (modelClass A β1 hβ1)
      (MAR.treatmentParameters A β1 hβ1).bracketParameters := by
  by_cases hb : A.β≤β1
  · have hp : MAR.treatmentParameters A β1 hβ1=A := by
      simp only [MAR.treatmentParameters,min_eq_left hb]
    rw [hp]
    exact SeparatedMAR.selected_ate_lowerBracket A false β1 hβ1 hδ hlo hhi hH
  · have hp : MAR.treatmentParameters A β1 hβ1=MAR.parametersWithBeta A β1 hβ1 := by
      simp only [MAR.treatmentParameters,min_eq_right (le_of_not_ge hb)]
    rw [hp]
    have h := SeparatedMAR.selected_ate_lowerBracket (MAR.parametersWithBeta A β1 hβ1) true
      A.β A.hβ hδ hlo hhi hH
    rw [selected_true_eq] at h
    exact h

theorem controlMean_rough_hardness (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n (MAR.armMean A.d false)
      (modelClass A β1 hβ1) (2*c*Model.lowerBracketScale A.bracketParameters n) :=
  SeparatedMAR.selected_armMean_rough_hardness A false β1 hβ1 hδ hlo hhi hH hrough

theorem treatedMean_rough_hardness (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (hrough : (MAR.parametersWithBeta A β1 hβ1).theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n (MAR.armMean A.d true)
      (modelClass A β1 hβ1) (2*c*Model.lowerBracketScale (MAR.parametersWithBeta A β1 hβ1).bracketParameters n) := by
  have h := SeparatedMAR.selected_armMean_rough_hardness (MAR.parametersWithBeta A β1 hβ1) true
    A.β A.hβ hδ hlo hhi hH hrough
  rw [selected_true_eq] at h
  exact h

theorem att_rough_lowerBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) (hrough : A.theta<1/2) :
    Model.LowerBracket (MAR.att A.d) (modelClass A β1 hβ1) A.bracketParameters := by
  apply Model.pilot_rough_lowerBracket A.bracketParameters hrough (MAR.att A.d) (MAR.armMean A.d false)
    (fun _=>modelClass A β1 hβ1) (modelClass A β1 hβ1) (Eventually.of_forall (fun _=>subset_rfl))
    (MAR.effectPilot A.d) (MAR.effectPilot_measurable A.d) (MAR.effectPilot_memLp A.d)
    (fun _=>0) (fun _=>1) (fun _=>zero_le_one) (MAR.effectPilot_mean_range A.d)
    (-1) 1 (by norm_num) MAR.attReconstruct 2 2 (by norm_num) MAR.attReconstruct_lipschitz
  · apply Eventually.of_forall
    intro n
    exact ⟨fun P hP=>conditionalEffect_range A β1 hβ1 hδ.le P hP true,
      fun P hP=>attReconstruct_relation A β1 hβ1 hδ.le P hP,
      fun P _=>MAR.effectPilot_variance A.d P⟩
  · exact controlMean_rough_hardness A β1 hβ1 hδ hlo hhi hH hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough

theorem atu_rough_lowerBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (hrough : (MAR.parametersWithBeta A β1 hβ1).theta<1/2) :
    Model.LowerBracket (MAR.atu A.d) (modelClass A β1 hβ1) (MAR.parametersWithBeta A β1 hβ1).bracketParameters := by
  apply Model.pilot_rough_lowerBracket (MAR.parametersWithBeta A β1 hβ1).bracketParameters hrough
    (MAR.atu A.d) (MAR.armMean A.d true) (fun _=>modelClass A β1 hβ1) (modelClass A β1 hβ1)
    (Eventually.of_forall (fun _=>subset_rfl)) (MAR.effectPilot A.d) (MAR.effectPilot_measurable A.d)
    (MAR.effectPilot_memLp A.d) (fun _=>0) (fun _=>1) (fun _=>zero_le_one) (MAR.effectPilot_mean_range A.d)
    (-1) 1 (by norm_num) MAR.atuReconstruct 3 2 (by norm_num) MAR.atuReconstruct_lipschitz
  · apply Eventually.of_forall
    intro n
    exact ⟨fun P hP=>conditionalEffect_range A β1 hβ1 hδ.le P hP false,
      fun P hP=>atuReconstruct_relation A β1 hβ1 hδ.le P hP,
      fun P _=>MAR.effectPilot_variance A.d P⟩
  · exact treatedMean_rough_hardness A β1 hβ1 hδ hlo hhi hH hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto (MAR.parametersWithBeta A β1 hβ1).bracketParameters hrough

theorem att_lowerBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Model.LowerBracket (MAR.att A.d) (modelClass A β1 hβ1) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · exact att_rough_lowerBracket A β1 hβ1 hδ hlo hhi hH hrough
  · obtain ⟨c,hc,he⟩ := SeparatedMAR.treatment_parametric_lower A β1 hβ1 hδ.le ⟨hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket A _ _ (le_of_not_gt hrough)
    exact ⟨c,hc,he.mono (fun _ hn=>hn.2.1)⟩

theorem atu_lowerBracket (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Model.LowerBracket (MAR.atu A.d) (modelClass A β1 hβ1) (MAR.parametersWithBeta A β1 hβ1).bracketParameters := by
  by_cases hrough : (MAR.parametersWithBeta A β1 hβ1).theta<1/2
  · exact atu_rough_lowerBracket A β1 hβ1 hδ hlo hhi hH hrough
  · obtain ⟨c,hc,he⟩ := SeparatedMAR.treatment_parametric_lower A β1 hβ1 hδ.le ⟨hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket (MAR.parametersWithBeta A β1 hβ1) _ _ (le_of_not_gt hrough)
    exact ⟨c,hc,he.mono (fun _ hn=>hn.2.2)⟩

theorem treatment_lowerBrackets (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Model.LowerBracket (MAR.ate A.d) (modelClass A β1 hβ1) (MAR.treatmentParameters A β1 hβ1).bracketParameters ∧
      Model.LowerBracket (MAR.att A.d) (modelClass A β1 hβ1) A.bracketParameters ∧
      Model.LowerBracket (MAR.atu A.d) (modelClass A β1 hβ1) (MAR.parametersWithBeta A β1 hβ1).bracketParameters :=
  ⟨ate_lowerBracket A β1 hβ1 hδ hlo hhi hH,att_lowerBracket A β1 hβ1 hδ hlo hhi hH,
    atu_lowerBracket A β1 hβ1 hδ hlo hhi hH⟩

end RoughRegime.Applications.SeparatedTreatment
