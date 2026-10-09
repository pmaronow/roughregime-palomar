module

public import RoughRegime.TreatmentSmoothTransfers
public import RoughRegime.TreatmentFullBrackets


@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1500000

theorem smooth_augmentation_ate_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.LowerBracket (ate A.d) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,hbound⟩ := smooth_augmentable_lowerBracket A hM hlo hhi hH
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  have htransfer := smooth_augmentation_ate_risk_transfer A hM j βother hβother (by linarith) n
    (2*c*Model.lowerBracketScale A.bracketParameters n)
  exact ⟨(hbound n hn).1.trans htransfer.2,fun hθ=>((hbound n hn).2 hθ).trans htransfer.1⟩

theorem smooth_ate_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.LowerBracket (ate A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse)
      (treatmentParameters A β1 hβ1).bracketParameters := by
  by_cases hb : A.β ≤ β1
  · have h := smooth_augmentation_ate_lowerBracket A hM false β1 hβ1 hlo hhi hH
    have hp : treatmentParameters A β1 hβ1=A := by
      simp only [treatmentParameters,min_eq_left hb]
    rw [hp]
    exact h
  · have h := smooth_augmentation_ate_lowerBracket (parametersWithBeta A β1 hβ1) hM true A.β A.hβ hlo hhi hH
    have hp : treatmentParameters A β1 hβ1=parametersWithBeta A β1 hβ1 := by
      simp only [treatmentParameters,min_eq_right (le_of_not_ge hb)]
    rw [hp]
    have hc : selectedTreatmentClass (parametersWithBeta A β1 hβ1) true A.β A.hβ=
        treatmentClass A β1 hβ1 := by
      have hr : armClass (parametersWithBeta (parametersWithBeta A β1 hβ1) A.β A.hβ) false = armClass A false := by
        cases A
        rfl
      change armClass (parametersWithBeta A β1 hβ1) true ∩ armClass (parametersWithBeta (parametersWithBeta A β1 hβ1) A.β A.hβ) false =
        armClass A false ∩ armClass (parametersWithBeta A β1 hβ1) true
      rw [hr]
      exact Set.inter_comm _ _
    rw [hc] at h
    exact h

theorem smooth_att_rough_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) (hrough : A.theta<1/2) :
    Model.LowerBracket (att A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) A.bracketParameters := by
  apply Model.pilot_rough_lowerBracket A.bracketParameters hrough (att A.d) (armMean A.d false)
    (fun _=>treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse)
    (Eventually.of_forall (fun _=>subset_rfl)) (effectPilot A.d) (effectPilot_measurable A.d)
    (effectPilot_memLp A.d) (fun _=>0) (fun _=>1) (fun _=>zero_le_one)
    (effectPilot_mean_range A.d) (-1) 1 (by norm_num) attReconstruct 2 2 (by norm_num)
    attReconstruct_lipschitz
  · apply Eventually.of_forall
    intro n
    exact ⟨fun P hP=>conditionalEffect_range A β1 hβ1 P hP.1 true,
      fun P hP=>attReconstruct_relation A β1 hβ1 P hP.1,fun P _=>effectPilot_variance A.d P⟩
  · exact smooth_treatment_controlMean_rough_hardness A hM β1 hβ1 hlo hhi hH hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto A.bracketParameters hrough

theorem smooth_atu_rough_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H)
    (hrough : (parametersWithBeta A β1 hβ1).theta<1/2) :
    Model.LowerBracket (atu A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) (parametersWithBeta A β1 hβ1).bracketParameters := by
  apply Model.pilot_rough_lowerBracket (parametersWithBeta A β1 hβ1).bracketParameters hrough
    (atu A.d) (armMean A.d true) (fun _=>treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse)
    (Eventually.of_forall (fun _=>subset_rfl)) (effectPilot A.d) (effectPilot_measurable A.d)
    (effectPilot_memLp A.d) (fun _=>0) (fun _=>1) (fun _=>zero_le_one)
    (effectPilot_mean_range A.d) (-1) 1 (by norm_num) atuReconstruct 3 2 (by norm_num)
    atuReconstruct_lipschitz
  · apply Eventually.of_forall
    intro n
    exact ⟨fun P hP=>conditionalEffect_range A β1 hβ1 P hP.1 false,
      fun P hP=>atuReconstruct_relation A β1 hβ1 P hP.1,fun P _=>effectPilot_variance A.d P⟩
  · exact smooth_treatment_treatedMean_rough_hardness A hM β1 hβ1 hlo hhi hH hrough
  · exact Model.rough_lowerBracket_squared_sample_tendsto (parametersWithBeta A β1 hβ1).bracketParameters hrough

theorem smooth_att_lowerBracket (A : Model.Parameters) (hM : 1≤A.M0) (β1 : ℝ) (hβ1 : 0<β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.LowerBracket (att A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · exact smooth_att_rough_lowerBracket A hM β1 hβ1 hlo hhi hH hrough
  · obtain ⟨c,hc,he⟩ := smooth_treatment_parametric_lower A hM β1 hβ1
      ((le_max_left _ _).trans hlo.le) ⟨(le_max_right _ _).trans hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket A _ _ (le_of_not_gt hrough)
    exact ⟨c,hc,he.mono (fun _ hn=>hn.2.1)⟩

theorem smooth_atu_lowerBracket (A : Model.Parameters) (hM : 1≤A.M0) (β1 : ℝ) (hβ1 : 0<β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.LowerBracket (atu A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse)
      (parametersWithBeta A β1 hβ1).bracketParameters := by
  by_cases hrough : (parametersWithBeta A β1 hβ1).theta<1/2
  · exact smooth_atu_rough_lowerBracket A hM β1 hβ1 hlo hhi hH hrough
  · obtain ⟨c,hc,he⟩ := smooth_treatment_parametric_lower A hM β1 hβ1
      ((le_max_left _ _).trans hlo.le) ⟨(le_max_right _ _).trans hlo.le,hhi.le⟩ hH.le
    apply Products.parametric_lowerBracket (parametersWithBeta A β1 hβ1) _ _ (le_of_not_gt hrough)
    exact ⟨c,hc,he.mono (fun _ hn=>hn.2.2)⟩

theorem smooth_treatment_brackets (A : Model.Parameters) (hM : 1≤A.M0) (β1 : ℝ) (hβ1 : 0<β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    let C := treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse
    Model.Bracket (ate A.d) C (treatmentParameters A β1 hβ1).bracketParameters ((treatmentParameters A β1 hβ1).nu : ℝ) ∧
    Model.Bracket (att A.d) C A.bracketParameters (A.nu : ℝ) ∧
    Model.Bracket (atu A.d) C (parametersWithBeta A β1 hβ1).bracketParameters ((parametersWithBeta A β1 hβ1).nu : ℝ) :=
  ⟨⟨smooth_ate_lowerBracket A hM β1 hβ1 hlo hhi hH,
      Model.upperBracket_mono_class _ _ _ Set.inter_subset_left (ate_upperBracket A hM β1 hβ1)⟩,
    ⟨smooth_att_lowerBracket A hM β1 hβ1 hlo hhi hH,
      Model.upperBracket_mono_class _ _ _ Set.inter_subset_left (att_upperBracket A hM β1 hβ1)⟩,
    ⟨smooth_atu_lowerBracket A hM β1 hβ1 hlo hhi hH,
      Model.upperBracket_mono_class _ _ _ Set.inter_subset_left (atu_upperBracket A hM β1 hβ1)⟩⟩

end RoughRegime.Applications.MAR
