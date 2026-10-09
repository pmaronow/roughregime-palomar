module

public import RoughRegime.ApplicationConditionalWaldEmbedding
public import RoughRegime.ApplicationMARBracket


@[expose] public section
/-! The complete bracket for the actual average conditional Wald ratio. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.ConditionalWald

theorem conditionalWald_lowerBracket (A : Model.Parameters) (hM : 2≤A.M0)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.LowerBracket (target A.d) (modelClass A) A.bracketParameters := by
  apply lowerBracket_of_MAR A hM
  have he : Model.target A (MAR.observables A (by linarith)) = MAR.observedMean A.d :=
    funext (MAR.generic_target_eq_observedMean A (by linarith))
  rw [he]
  exact MAR.mar_lowerBracket A (by linarith) hlo hhi hH

theorem conditionalWald_bracket (A : Model.Parameters) (hM : 2≤A.M0)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) :
    Model.Bracket (target A.d) (modelClass A) A.bracketParameters (A.nu:ℝ) :=
  ⟨conditionalWald_lowerBracket A hM hlo hhi hH,conditionalWald_upperBracket A hM⟩

def etaParameters (d : ℕ) (α β H η : ℝ) (hd : 1≤d)
    (hα : 0<α) (hβ : 0<β) (hH : 2<H) (hη : 0<η) (hηquarter : η<1/4) :
    Model.Parameters where
  d := d
  α := α
  β := β
  H := H
  δ := η
  gminus := η
  gplus := η⁻¹
  M0 := 2
  hd := hd
  hα := hα
  hβ := hβ
  hH := by linarith
  hδ := hη
  hgminus := hη
  hgplus := by
    rw [←one_div]
    apply (lt_div_iff₀ hη).mpr
    nlinarith
  hM0 := by norm_num

/-- The J_eta row with the original eta and radius assumptions. -/
theorem eta_conditionalWald_bracket (d : ℕ) (α β H η : ℝ) (hd : 1≤d)
    (hα : 0<α) (hβ : 0<β) (hH : 2<H) (hη : 0<η) (hηquarter : η<1/4) :
    let A := etaParameters d α β H η hd hα hβ hH hη hηquarter
    Model.Bracket (target d) (modelClass A) A.bracketParameters (A.nu:ℝ) := by
  dsimp only
  apply conditionalWald_bracket _ le_rfl
  · change max η η<1/2
    rw [max_self]
    linarith
  · change 1/2<η⁻¹
    rw [←one_div]
    apply (lt_div_iff₀ hη).mpr
    nlinarith
  · exact hH

end RoughRegime.Applications.ConditionalWald
