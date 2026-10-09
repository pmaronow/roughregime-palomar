module

public import RoughRegime.ModelLower
public import RoughRegime.ModelUpperConsequences


@[expose] public section
/-! The proved main theorem in the original bracket convention. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RoughRegime.Model
universe u

 theorem model_lowerBracket (A : Parameters) {Z : Type u} [MeasurableSpace Z]
     (F : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ)
     (hnd : Nondegenerate A F π) (hr : 0<r)
     (C : Set (ProbabilityMeasure (Observation A Z)))
     (hC : localClass A F π r⊆C) (hCM : C⊆modelClass A F) :
     LowerBracket (target A F) C A.bracketParameters := by
   obtain ⟨c,hc,n0,hn0,hbound⟩ := mainLowerClaim A F π r hnd hr
   refine ⟨c,hc,n0,hn0,?_⟩
   intro n hn
   have hb := hbound C hC hCM n hn
   by_cases ht : A.theta<1/2
   · have hs := hb.2 ⟨A.theta_pos,ht⟩
     refine ⟨?_,fun _=>?_⟩
     · simpa only [lowerBracketScale,Parameters.bracketParameters,ite_true,ht,mul_assoc] using hs.1
     · simpa only [lowerBracketScale,Parameters.bracketParameters,ite_true,ht,mul_assoc] using hs.2
   · refine ⟨?_,?_⟩
     · simpa only [lowerBracketScale,Parameters.bracketParameters,ite_false,ht] using hb.1 (le_of_not_gt ht)
     · intro hh
       exact False.elim (ht hh)

 theorem model_bracket (A : Parameters) {Z : Type u} [MeasurableSpace Z]
     (F : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ)
     (hnd : Nondegenerate A F π) (hr : 0<r)
     (C : Set (ProbabilityMeasure (Observation A Z)))
     (hC : localClass A F π r⊆C) (hCM : C⊆modelClass A F) :
     Bracket (target A F) C A.bracketParameters (A.nu:ℝ) :=
   ⟨model_lowerBracket A F π r hnd hr C hC hCM,
     upperBracket_mono_class (target A F) A.bracketParameters (A.nu:ℝ) hCM (model_upperBracket A F)⟩

end RoughRegime.Model
