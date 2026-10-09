module

public import RoughRegime.ApplicationWaldBracket


@[expose] public section
/-! The literal eta Wald ratio row of the applications corollary. -/
noncomputable section
namespace RoughRegime.Applications.Wald

abbrev etaWaldClass (d : ℕ) (α β H η cW : ℝ) (hd : 1≤d) (hα : 0<α)
    (hβ : 0<β) (hH : 0<H) (hη : 0<η) (hηquarter : η<1/4) :=
  modelClass (MAR.etaParameters d α β H η hd hα hβ hH hη hηquarter) cW

theorem eta_wald_bracket (d : ℕ) (α β H η cW : ℝ) (hd : 1≤d) (hα : 0<α)
    (hβ : 0<β) (hH : 2<H) (hη : 0<η) (hηquarter : η<1/4) (hc : 0<cW) (hc1 : cW≤1) :
    let hH0 := (by norm_num : (0:ℝ)<2).trans hH
    let A := MAR.etaParameters d α β H η hd hα hβ hH0 hη hηquarter
    Model.Bracket (target A) (etaWaldClass d α β H η cW hd hα hβ hH0 hη hηquarter)
      A.bracketParameters (A.nu : ℝ) := by
  dsimp only
  apply wald_bracket _ le_rfl cW hc hc1
  · change max η η<1/2
    rw [max_self]
    linarith
  · change 1/2<η⁻¹
    rw [←one_div]
    apply (lt_div_iff₀ hη).mpr
    nlinarith
  · exact hH

end RoughRegime.Applications.Wald
