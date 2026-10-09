module

public import RoughRegime.TreatmentArmHardness
public import RoughRegime.TreatmentReverseRelations
public import RoughRegime.ModelPilotLower
public import RoughRegime.RoughScaleDecay


@[expose] public section
/-! Original full ATT and ATU brackets. The reverse transfer uses the actual
outcome/treatment empirical means from the same sample, with proved variance,
range, reconstruction and Lipschitz bounds. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1500000

theorem att_rough_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) (hrough : A.theta<1/2) :
    Model.LowerBracket (att A.d) (treatmentClass A β1 hβ1) A.bracketParameters := by
  apply Model.pilot_rough_lowerBracket A.bracketParameters hrough (att A.d) (armMean A.d false)
    (fun _=>treatmentClass A β1 hβ1) (treatmentClass A β1 hβ1)
    (Eventually.of_forall (fun _=>subset_rfl)) (effectPilot A.d) (effectPilot_measurable A.d)
    (effectPilot_memLp A.d) (fun _=>0) (fun _=>1) (fun _=>zero_le_one)
    (effectPilot_mean_range A.d) (-1) 1 (by norm_num) attReconstruct 2 2 (by norm_num)
    attReconstruct_lipschitz
  · apply Eventually.of_forall
    intro n
    exact ⟨fun P hP=>conditionalEffect_range A β1 hβ1 P hP true,
      fun P hP=>attReconstruct_relation A β1 hβ1 P hP,fun P _=>effectPilot_variance A.d P⟩
  · exact treatment_controlMean_rough_hardness A hM β1 hβ1 hlo hhi hH hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough

theorem atu_rough_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H)
    (hrough : (parametersWithBeta A β1 hβ1).theta<1/2) :
    Model.LowerBracket (atu A.d) (treatmentClass A β1 hβ1) (parametersWithBeta A β1 hβ1).bracketParameters := by
  apply Model.pilot_rough_lowerBracket (parametersWithBeta A β1 hβ1).bracketParameters hrough
    (atu A.d) (armMean A.d true) (fun _=>treatmentClass A β1 hβ1) (treatmentClass A β1 hβ1)
    (Eventually.of_forall (fun _=>subset_rfl)) (effectPilot A.d) (effectPilot_measurable A.d)
    (effectPilot_memLp A.d) (fun _=>0) (fun _=>1) (fun _=>zero_le_one)
    (effectPilot_mean_range A.d) (-1) 1 (by norm_num) atuReconstruct 3 2 (by norm_num)
    atuReconstruct_lipschitz
  · apply Eventually.of_forall
    intro n
    exact ⟨fun P hP=>conditionalEffect_range A β1 hβ1 P hP false,
      fun P hP=>atuReconstruct_relation A β1 hβ1 P hP,fun P _=>effectPilot_variance A.d P⟩
  · exact treatment_treatedMean_rough_hardness A hM β1 hβ1 hlo hhi hH hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto (parametersWithBeta A β1 hβ1).bracketParameters hrough

theorem att_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.LowerBracket (att A.d) (treatmentClass A β1 hβ1) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · exact att_rough_lowerBracket A hM β1 hβ1 hlo hhi hH hrough
  · exact ((treatment_parametric_brackets A hM β1 hβ1
      ((le_max_left _ _).trans hlo.le) ⟨(le_max_right _ _).trans hlo.le,hhi.le⟩ hH.le).2.1
      (le_of_not_gt hrough)).1

theorem atu_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.LowerBracket (atu A.d) (treatmentClass A β1 hβ1) (parametersWithBeta A β1 hβ1).bracketParameters := by
  by_cases hrough : (parametersWithBeta A β1 hβ1).theta<1/2
  · exact atu_rough_lowerBracket A hM β1 hβ1 hlo hhi hH hrough
  · exact ((treatment_parametric_brackets A hM β1 hβ1
      ((le_max_left _ _).trans hlo.le) ⟨(le_max_right _ _).trans hlo.le,hhi.le⟩ hH.le).2.2
      (le_of_not_gt hrough)).1

theorem treatment_brackets (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.Bracket (ate A.d) (treatmentClass A β1 hβ1)
      (treatmentParameters A β1 hβ1).bracketParameters ((treatmentParameters A β1 hβ1).nu : ℝ) ∧
    Model.Bracket (att A.d) (treatmentClass A β1 hβ1) A.bracketParameters (A.nu : ℝ) ∧
    Model.Bracket (atu A.d) (treatmentClass A β1 hβ1)
      (parametersWithBeta A β1 hβ1).bracketParameters ((parametersWithBeta A β1 hβ1).nu : ℝ) :=
  ⟨ate_bracket A hM β1 hβ1 hlo hhi hH,
    ⟨att_lowerBracket A hM β1 hβ1 hlo hhi hH,att_upperBracket A hM β1 hβ1⟩,
    ⟨atu_lowerBracket A hM β1 hβ1 hlo hhi hH,atu_upperBracket A hM β1 hβ1⟩⟩

end RoughRegime.Applications.MAR
