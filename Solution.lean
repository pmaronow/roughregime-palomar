module

public import RoughRegime.ModelUpper
public import RoughRegime.ModelLower

@[expose] public section

/-! Proofs of the two selected generic minimax targets. The proof development
supplies the same concrete definitions used by the standalone Challenge. -/

noncomputable section
open MeasureTheory

namespace RoughRegimeSubmission
universe u

theorem mainUpper (A : RoughRegime.Model.Parameters) (L MW : ℝ) :
    RoughRegime.Model.UniformUpperClaim.{u} A L MW := by
  exact RoughRegime.Model.uniformUpperClaim.{u} A L MW

theorem mainLower (A : RoughRegime.Model.Parameters) {Z : Type u} [MeasurableSpace Z]
    (F : RoughRegime.Model.Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ) :
    RoughRegime.Model.MainLowerClaim A F π r := by
  exact RoughRegime.Model.mainLowerClaim A F π r

end RoughRegimeSubmission
