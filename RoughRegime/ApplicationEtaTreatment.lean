module

public import RoughRegime.TreatmentFullBrackets


@[expose] public section
/-! The original three treatment rows with precisely H > 2. -/
noncomputable section
namespace RoughRegime.Applications.MAR

theorem eta_treatment_brackets (d : ℕ) (α β0 β1 H η : ℝ) (hd : 1 ≤ d)
    (hα : 0 < α) (hβ0 : 0 < β0) (hβ1 : 0 < β1) (hH : 2 < H)
    (hη : 0 < η) (hηquarter : η < 1/4) :
    let hH0 := (by norm_num : (0:ℝ)<2).trans hH
    let A := etaParameters d α β0 H η hd hα hβ0 hH0 hη hηquarter
    let A1 := parametersWithBeta A β1 hβ1
    let As := treatmentParameters A β1 hβ1
    let C := etaTreatmentClass d α β0 β1 H η hd hα hβ0 hβ1 hH0 hη hηquarter
    Model.Bracket (ate d) C As.bracketParameters (As.nu : ℝ) ∧
      Model.Bracket (att d) C A.bracketParameters (A.nu : ℝ) ∧
      Model.Bracket (atu d) C A1.bracketParameters (A1.nu : ℝ) := by
  dsimp only
  apply treatment_brackets _ le_rfl β1 hβ1
  · change max η η < 1/2
    rw [max_self]
    linarith
  · change 1/2 < η⁻¹
    rw [← one_div]
    apply (lt_div_iff₀ hη).mpr
    nlinarith
  · exact hH

end RoughRegime.Applications.MAR
