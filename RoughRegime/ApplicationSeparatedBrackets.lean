module

public import RoughRegime.ApplicationSeparatedUpper
public import RoughRegime.SeparatedMARLower
public import RoughRegime.ApplicationSeparatedTreatmentUpper
public import RoughRegime.SeparatedTreatmentLower


@[expose] public section
/-! The exact qualified separated-density rows of Corollary 3(a). -/
noncomputable section
namespace RoughRegime.Applications.SeparatedMAR

theorem qualified_bracket (A : Model.Parameters) (hδ : A.δ<1/2)
    (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Model.LowerBracket (target A.d) (modelClass A) A.bracketParameters ∧
      ∀ (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1),
        Model.UpperBracket (target A.d) (modelClass A)
          (enlargedBracketParameters A ζ hζ hζ1) (A.nu:ℝ) :=
  ⟨lowerBracket A hδ hlo hhi hH,separated_upperBracket A⟩

end RoughRegime.Applications.SeparatedMAR
namespace RoughRegime.Applications.SeparatedTreatment

theorem qualified_treatment_brackets (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    (Model.LowerBracket (MAR.ate A.d) (modelClass A β1 hβ1)
        (MAR.treatmentParameters A β1 hβ1).bracketParameters ∧
      ∀ (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1),
        Model.UpperBracket (MAR.ate A.d) (modelClass A β1 hβ1)
          (SeparatedMAR.enlargedBracketParameters (MAR.treatmentParameters A β1 hβ1) ζ hζ hζ1)
          ((MAR.treatmentParameters A β1 hβ1).nu:ℝ)) ∧
    (Model.LowerBracket (MAR.att A.d) (modelClass A β1 hβ1) A.bracketParameters ∧
      ∀ (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1),
        Model.UpperBracket (MAR.att A.d) (modelClass A β1 hβ1)
          (SeparatedMAR.enlargedBracketParameters A ζ hζ hζ1) (A.nu:ℝ)) ∧
    (Model.LowerBracket (MAR.atu A.d) (modelClass A β1 hβ1)
        (MAR.parametersWithBeta A β1 hβ1).bracketParameters ∧
      ∀ (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1),
        Model.UpperBracket (MAR.atu A.d) (modelClass A β1 hβ1)
          (SeparatedMAR.enlargedBracketParameters (MAR.parametersWithBeta A β1 hβ1) ζ hζ hζ1)
          ((MAR.parametersWithBeta A β1 hβ1).nu:ℝ)) :=
  ⟨⟨ate_lowerBracket A β1 hβ1 hδ hlo hhi hH,ate_upperBracket A β1 hβ1⟩,
    ⟨att_lowerBracket A β1 hβ1 hδ hlo hhi hH,att_upperBracket A β1 hβ1⟩,
    ⟨atu_lowerBracket A β1 hβ1 hδ hlo hhi hH,atu_upperBracket A β1 hβ1⟩⟩

end RoughRegime.Applications.SeparatedTreatment
