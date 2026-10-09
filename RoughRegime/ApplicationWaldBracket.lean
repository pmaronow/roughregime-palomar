module

public import RoughRegime.ApplicationWaldEmbedding
public import RoughRegime.TreatmentATELower


@[expose] public section
/-! The full Wald-ratio bracket from the true bounded-response treatment
embedding and the actual projected ratio estimators. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Wald

theorem wald_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (cW : ℝ) (hc : 0<cW) (hc1 : cW≤1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.Bracket (target A) (modelClass A cW) A.bracketParameters (A.nu : ℝ) := by
  have hLower := MAR.ate_lowerBracket A hM A.β A.hβ hlo hhi hH
  rw [same_treatment_parameters] at hLower
  exact ⟨lowerBracket_of_treatment A cW hc1 (by linarith) hLower,
    wald_upperBracket A hM cW hc hc1⟩

end RoughRegime.Applications.Wald
