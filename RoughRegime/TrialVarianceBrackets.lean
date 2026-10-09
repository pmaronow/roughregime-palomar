module

public import RoughRegime.TrialVarianceUpper
public import RoughRegime.ProductDerivedLower


@[expose] public section
/-! The full literal CATE-variance bracket, including the source rough tail
clause, transported by the actual fair-coin response kernel. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Trial

 theorem cateVariance_lowerBracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) :
    Model.LowerBracket (cateVariance A) (modelClass A) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,he⟩:=(Products.explained_bracket A hM hlo hhi hab).1
  apply Model.lowerBracket_congr_target _ (fun P=>Products.explainedTarget A (forwardLaw A P))
    _ _ (cateVariance_eq A)
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  rw [(transformed_risks_eq A hab n (Products.explainedTarget A) 0).2,
    (transformed_risks_eq A hab n (Products.explainedTarget A) _).1]
  exact he n hn

 theorem cateVariance_bracket (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) :
    Model.Bracket (cateVariance A) (modelClass A) A.bracketParameters (A.nu:ℝ) :=
  ⟨cateVariance_lowerBracket A hM hlo hhi hab,
    cateVariance_upperBracket A hM ((le_max_left _ _).trans hlo.le) hab⟩

end RoughRegime.Applications.Trial
