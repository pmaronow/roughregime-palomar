module

public import RoughRegime.TreatmentParametricLower
public import RoughRegime.ProductBrackets


@[expose] public section
/-! Full treatment brackets in each target's parametric regime, using the
actual common bounded affine path and the target-specific proved upper rate. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR

theorem treatment_parametric_brackets (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) :
    (1/2 ≤ (treatmentParameters A β1 hβ1).theta →
      Model.Bracket (ate A.d) (treatmentClass A β1 hβ1)
        (treatmentParameters A β1 hβ1).bracketParameters ((treatmentParameters A β1 hβ1).nu : ℝ)) ∧
    (1/2 ≤ A.theta → Model.Bracket (att A.d) (treatmentClass A β1 hβ1)
      A.bracketParameters (A.nu : ℝ)) ∧
    (1/2 ≤ (parametersWithBeta A β1 hβ1).theta →
      Model.Bracket (atu A.d) (treatmentClass A β1 hβ1)
        (parametersWithBeta A β1 hβ1).bracketParameters ((parametersWithBeta A β1 hβ1).nu : ℝ)) := by
  obtain ⟨c,hc,he⟩ := treatment_parametric_lower A hM β1 hβ1 hδ hg hH
  refine ⟨?_,?_,?_⟩
  · intro hθ
    exact ⟨Products.parametric_lowerBracket (treatmentParameters A β1 hβ1) _ _ hθ
      ⟨c,hc,he.mono (fun _ hn=>hn.1)⟩,ate_upperBracket A hM β1 hβ1⟩
  · intro hθ
    exact ⟨Products.parametric_lowerBracket A _ _ hθ ⟨c,hc,he.mono (fun _ hn=>hn.2.1)⟩,
      att_upperBracket A hM β1 hβ1⟩
  · intro hθ
    exact ⟨Products.parametric_lowerBracket (parametersWithBeta A β1 hβ1) _ _ hθ
      ⟨c,hc,he.mono (fun _ hn=>hn.2.2)⟩,atu_upperBracket A hM β1 hβ1⟩

end RoughRegime.Applications.MAR
