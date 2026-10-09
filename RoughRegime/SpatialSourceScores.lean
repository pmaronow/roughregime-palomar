module

public import RoughRegime.SpatialInteraction


@[expose] public section
/-! Source-score existence preserving the diagonal smoothness condition. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.SpatialAffine

 theorem nondegenerate_equal_exponent_of_diagonal (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z A) (π : ProbabilityMeasure Z)
     (hnd : Model.Nondegenerate A O π) (hUV : O.U=O.V) : A.α=A.β := by
   have hab : Model.baselineA A O π=Model.baselineB A O π := by
     unfold Model.baselineA Model.baselineB
     rw [hUV]
   have he := hnd.2.2.2.2.2
   dsimp only at he
   rw [← hUV,← hab] at he
   rcases he with hpos | hdiag
   · have hmul : (∫ z, (O.U z-Model.baselineA A O π*O.D z)*(O.U z-Model.baselineA A O π*O.D z) ∂(π:Measure Z)) =
         ∫ z, (O.U z-Model.baselineA A O π*O.D z)^2 ∂(π:Measure Z) := by
       congr 1
       funext z
       ring
     rw [hmul] at hpos
     nlinarith only [hpos.2]
   · exact hdiag.2.1

 theorem nondegenerate_exists_source_scores (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate A O π) :
     ∃ S : Scores (π:Measure Z),
       ((residualMomentU A O π S true=1 ∧ residualMomentU A O π S false=0 ∧
         residualMomentV A O π S true=0 ∧ residualMomentV A O π S false=1) ∨
        (O.U=O.V ∧ A.α=A.β ∧ S.su=S.sv ∧ residualMomentU A O π S true=1)) := by
   obtain ⟨S,hS⟩ := nondegenerate_exists_spatial_scores A O π hnd
   refine ⟨S,?_⟩
   rcases hS with hpos | hdiag
   · exact Or.inl hpos
   · exact Or.inr ⟨hdiag.1,nondegenerate_equal_exponent_of_diagonal A O π hnd hdiag.1,hdiag.2⟩

end RoughRegime.SpatialAffine
