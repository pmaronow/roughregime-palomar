module

public import RoughRegime.ModelUpperConsequences


@[expose] public section
/-! The actual randomized minimax tail and full brackets depend only on
target values on the statistical class. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

 theorem minimaxTail_congr_target {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T U : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (t : ℝ) (hTU : ∀P∈C,T P=U P) : minimaxTail n T C t=minimaxTail n U C t := by
  unfold minimaxTail
  apply iInf_congr
  intro E
  apply iSup_congr
  intro P
  apply iSup_congr
  intro hP
  rw [hTU P hP]

 theorem lowerBracket_congr_target {Ω : Type*} [MeasurableSpace Ω]
    (T U : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (hTU : ∀P∈C,T P=U P) (hU : LowerBracket U C S) :
    LowerBracket T C S := by
  obtain ⟨c,hc,n0,hn0,he⟩:=hU
  refine ⟨c,hc,n0,hn0,fun n hn=>?_⟩
  rw [minimaxRMSE_congr_target n T U C hTU,minimaxTail_congr_target n T U C _ hTU]
  exact he n hn

 theorem bracket_congr_target {Ω : Type*} [MeasurableSpace Ω]
    (T U : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (nu : ℝ) (hTU : ∀P∈C,T P=U P) (hU : Bracket U C S nu) :
    Bracket T C S nu :=
  ⟨lowerBracket_congr_target T U C S hTU hU.1,upperBracket_congr_target T U C S nu hTU hU.2⟩

end RoughRegime.Model
