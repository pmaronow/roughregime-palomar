module

public import RoughRegime.ApplicationMARBracket
public import RoughRegime.ApplicationTreatmentUpper


@[expose] public section
/-! The literal eta missing-data row with exactly the source H>2 assumption. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR

abbrev etaMARClass (d : ℕ) (α β H η : ℝ) (hd : 1 ≤ d)
    (hα : 0 < α) (hβ : 0 < β) (hH : 0 < H) (hη : 0 < η) (hηquarter : η < 1/4) :=
  modelClass (etaParameters d α β H η hd hα hβ hH hη hηquarter)

theorem eta_mar_bracket (d : ℕ) (α β H η : ℝ) (hd : 1 ≤ d)
    (hα : 0 < α) (hβ : 0 < β) (hH : 2 < H) (hη : 0 < η) (hηquarter : η < 1/4) :
    let A := etaParameters d α β H η hd hα hβ ((by norm_num : (0:ℝ)<2).trans hH) hη hηquarter
    Model.Bracket (observedMean d) (etaMARClass d α β H η hd hα hβ
      ((by norm_num : (0:ℝ)<2).trans hH) hη hηquarter) A.bracketParameters (A.nu : ℝ) := by
  dsimp only
  apply mar_bracket _ le_rfl
  · change max η η < 1/2
    rw [max_self]
    linarith
  · change 1/2 < η⁻¹
    rw [← one_div]
    apply (lt_div_iff₀ hη).mpr
    nlinarith
  · exact hH

end RoughRegime.Applications.MAR
