module

public import RoughRegime.MARAugmentableLower
public import RoughRegime.TreatmentParametricBracket


@[expose] public section
/-! The original ATE lower bracket, with the smaller actual arm smoothness
and the genuine finite-restriction MAR hard family. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000

theorem augmentation_ate_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.LowerBracket (ate A.d) (selectedTreatmentClass A j βother hβother) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,hbound⟩ := augmentable_lowerBracket A hM hlo hhi hH
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  have htransfer := augmentation_ate_risk_transfer A hM j βother hβother (by linarith) n
    (2*c*Model.lowerBracketScale A.bracketParameters n)
  exact ⟨(hbound n hn).1.trans htransfer.2,fun hθ=>((hbound n hn).2 hθ).trans htransfer.1⟩

theorem parametersWithBeta_self (A : Model.Parameters) : parametersWithBeta A A.β A.hβ=A := by
  cases A
  rfl

theorem parametersWithBeta_restore (A : Model.Parameters) (β : ℝ) (hβ : 0 < β) :
    parametersWithBeta (parametersWithBeta A β hβ) A.β A.hβ=A := by
  cases A
  rfl

theorem ate_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.LowerBracket (ate A.d) (treatmentClass A β1 hβ1)
      (treatmentParameters A β1 hβ1).bracketParameters := by
  by_cases hb : A.β ≤ β1
  · have h := augmentation_ate_lowerBracket A hM false β1 hβ1 hlo hhi hH
    have hp : treatmentParameters A β1 hβ1=A := by
      simp only [treatmentParameters,min_eq_left hb]
    rw [hp]
    exact h
  · have h := augmentation_ate_lowerBracket (parametersWithBeta A β1 hβ1) hM true A.β A.hβ hlo hhi hH
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

theorem ate_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.Bracket (ate A.d) (treatmentClass A β1 hβ1)
      (treatmentParameters A β1 hβ1).bracketParameters ((treatmentParameters A β1 hβ1).nu : ℝ) :=
  ⟨ate_lowerBracket A hM β1 hβ1 hlo hhi hH,ate_upperBracket A hM β1 hβ1⟩

end RoughRegime.Applications.MAR
