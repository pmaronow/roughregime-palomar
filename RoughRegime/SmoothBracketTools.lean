module

public import RoughRegime.ApplicationSmoothDensity


@[expose] public section
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

theorem lowerBracket_mono_class {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (S : BracketParameters)
    {C D : Set (ProbabilityMeasure Ω)} (hsub : C⊆D) (h : LowerBracket T C S) :
    LowerBracket T D S := by
  obtain ⟨c,hc,n0,hn0,hb⟩ := h
  exact ⟨c,hc,n0,hn0,fun n hn=>⟨(hb n hn).1.trans (minimaxRMSE_mono_class n T hsub),
    fun hrough=>(hb n hn).2 hrough |>.trans (minimaxTail_mono_class n T _ hsub)⟩⟩

end RoughRegime.Model

namespace RoughRegime.Model
open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem smooth_model_bracket (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (O : Observables Z A) (π : ProbabilityMeasure Z) (hnd : Nondegenerate A O π) :
    Bracket (target A O) (modelClass A O ∩ smoothDensityClass A.d Z) A.bracketParameters (A.nu : ℝ) :=
  ⟨lowerBracket_mono_class _ _
    (fun _ h=>⟨localClass_subset A O π 1 h.1,h.2⟩)
    (smooth_localClass_lowerBracket A O π hnd 1 zero_lt_one),
    upperBracket_mono_class _ _ _ Set.inter_subset_left (model_upperBracket A O)⟩

theorem smooth_model_rough_hardness (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (O : Observables Z A) (π : ProbabilityMeasure Z) (hnd : Nondegenerate A O π) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,(3/8:ℝ≥0∞)≤ minimaxTail n (target A O)
      (modelClass A O ∩ smoothDensityClass A.d Z) (2*c*lowerBracketScale A.bracketParameters n) := by
  obtain ⟨c,hc,he⟩ := smooth_localClass_rough_hardness A O π hnd 1 zero_lt_one hrough
  exact ⟨c,hc,he.mono (fun n hn=>hn.trans (minimaxTail_mono_class n _ _
    (fun _ h=>⟨localClass_subset A O π 1 h.1,h.2⟩)))⟩

end RoughRegime.Model
