module

public import RoughRegime.ModelPredicates


@[expose] public section
/-! Eventual actual fixed-size hard tails imply the original lower bracket,
including arbitrary behavior of the first finitely many sample sizes. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace RoughRegime.Model

 theorem lowerBracketScale_nonneg (S : BracketParameters) (n : ℕ) : 0≤lowerBracketScale S n := by
  unfold lowerBracketScale Rates.subcriticalScale
  split_ifs <;> positivity
 theorem lowerBracket_of_eventual_hardTail {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (Cn : ℕ→Set (ProbabilityMeasure Ω))
    (C : Set (ProbabilityMeasure Ω)) (S : BracketParameters) (c : ℝ) (hc : 0<c)
    (hC : ∀ᶠ n in atTop,Cn n⊆C)
    (hT : ∀ᶠ n in atTop,(3/8:ℝ≥0∞)≤ minimaxTail n T (Cn n) (c*lowerBracketScale S n)) :
    LowerBracket T C S := by
  have h := hardness_to_risk T Cn C (fun n=>c*lowerBracketScale S n)
    (fun n=>mul_nonneg hc.le (lowerBracketScale_nonneg S n)) hC (le_liminf_of_le (by isBoundedDefault) hT)
  have he : ∀ᶠ n in atTop,
      ENNReal.ofReal ((c/2)*lowerBracketScale S n)≤ minimaxRMSE n T C ∧
      (S.theta<1/2 → (1/4:ℝ≥0∞)≤ minimaxTail n T C (2*(c/2)*lowerBracketScale S n)) := by
    filter_upwards [h] with n hn
    have h1 : c*lowerBracketScale S n/2=(c/2)*lowerBracketScale S n := by ring
    have h2 : 2*(c/2)*lowerBracketScale S n=c*lowerBracketScale S n := by ring
    exact ⟨by simpa only [h1] using hn.2,fun _=>by simpa only [h2] using hn.1⟩
  obtain ⟨n0,hn0⟩:=eventually_atTop.mp he
  exact ⟨c/2,by positivity,max 3 n0,le_max_left _ _,fun n hn=>hn0 n ((le_max_right _ _).trans hn)⟩

end RoughRegime.Model
