module

public import RoughRegime.ModelPredicates
public import RoughRegime.KernelSeedBridge


@[expose] public section
/-! Consequences of genuine fixed-kernel reductions for the paper's full
lower bracket, including its probability clause. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace RoughRegime.Model

theorem lowerBracket_kernel {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (K : Kernel Ω Ξ) [IsMarkovKernel K]
    (T0 : ProbabilityMeasure Ω → ℝ) (T1 : ProbabilityMeasure Ξ → ℝ)
    (C0 : Set (ProbabilityMeasure Ω)) (C1 : Set (ProbabilityMeasure Ξ))
    (hclass : ∀ P ∈ C0, kernelLaw K P ∈ C1)
    (htarget : ∀ P ∈ C0, T1 (kernelLaw K P) = T0 P)
    (S : BracketParameters) (hlower : LowerBracket T0 C0 S) :
    LowerBracket T1 C1 S := by
  obtain ⟨c,hc,n0,hn0,hbound⟩ := hlower
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  have hr := kernel_reduction n K T0 T1 C0 C1 hclass htarget
    (2*c*lowerBracketScale S n)
  exact ⟨(hbound n hn).1.trans hr.2, fun hθ => ((hbound n hn).2 hθ).trans hr.1⟩

end RoughRegime.Model
