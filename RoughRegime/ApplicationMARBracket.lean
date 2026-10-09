module

public import RoughRegime.ModelMainLowerConsequences
public import RoughRegime.ApplicationMARUpper
public import RoughRegime.MARLocalized


@[expose] public section
/-! Full literal MAR bracket from the actual finite baseline, genuine local
law inclusion and the proved main lower theorem. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR

theorem mar_lowerBracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.LowerBracket (observedMean A.d) (modelClass A) A.bracketParameters := by
  let r := (1/2-A.δ)/2
  have hr : 0 < r := by
    have hδ := (le_max_left A.δ A.gminus).trans_lt hlo
    dsimp [r]
    linarith
  have hrup : r < 1/2-A.δ := by dsimp [r]; linarith [(le_max_left A.δ A.gminus).trans_lt hlo]
  have h := Model.model_lowerBracket A (observables A hM) baseline r
    (baseline_nondegenerate A hM hlo hhi hH) hr (modelClass A)
    (localized_subset_mar A hM r hrup) (modelClass_subset_generic A hM)
  obtain ⟨c,hc,n0,hn0,hbounds⟩ := h
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  have he : Model.target A (observables A hM) = observedMean A.d := funext (generic_target_eq_observedMean A hM)
  rw [he] at hbounds
  exact hbounds n hn

theorem mar_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1/2) (hhi : 1/2 < A.gplus) (hH : 2 < A.H) :
    Model.Bracket (observedMean A.d) (modelClass A) A.bracketParameters (A.nu : ℝ) :=
  ⟨mar_lowerBracket A hM hlo hhi hH,mar_upperBracket A hM⟩

end RoughRegime.Applications.MAR
