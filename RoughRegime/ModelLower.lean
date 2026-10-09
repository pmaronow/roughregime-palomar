module

public import RoughRegime.MainLowerAssembly
public import RoughRegime.SourceRoughLower


@[expose] public section
/-! The complete main lower theorem in the original statistical model,
 including every positive dimension and either ordering of the exponents.
 The rough branch uses the actual constructed priors and fixed-size testing
 experiment; the parametric branch uses the actual baseline affine path. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.Model
universe u

 theorem mainLowerClaim (A : Parameters) {Z : Type u} [MeasurableSpace Z]
     (O : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ) : MainLowerClaim A O π r := by
   apply mainLowerClaim_of_dimension_rough_lower (fun A0 D {Z} _ O π r hnd hr htheta =>
     source_rough_minimax_lower A0 D O π r hnd hr htheta) A O π r

end RoughRegime.Model
