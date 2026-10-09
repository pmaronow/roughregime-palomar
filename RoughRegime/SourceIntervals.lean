module

public import RoughRegime.SourceFrame
public import RoughRegime.SpatialInteraction


@[expose] public section
/-! The source density interval and a genuine fixed grid-volume margin are
forced by the paper's nondegenerate baseline assumptions. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors

 theorem nondegenerate_source_interval (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate A O π) :
     let w0 := Model.baselineW A O π
     0 < A.gminus/w0 ∧ A.gminus/w0 < 1 ∧ 1 < A.gplus/w0 ∧
       w0*(A.gminus/w0)=A.gminus ∧ w0*(A.gplus/w0)=A.gplus := by
   dsimp only
   have hg : A.gminus < Model.baselineW A O π :=
     (le_max_right A.δ A.gminus).trans_lt hnd.2.1
   have hw : 0 < Model.baselineW A O π := A.hgminus.trans hg
   refine ⟨div_pos A.hgminus hw,(div_lt_one hw).mpr hg,
     (one_lt_div hw).mpr hnd.2.2.1,?_,?_⟩ <;> field_simp

 theorem nondegenerate_source_volume (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate A O π) :
     ∃ v0 : ℝ, 0 < v0 ∧ v0 ≤ 1/2 ∧
       0 < 1-v0*sourceOuterIntegral A.d ∧
       0 < sourceMarginBound A.d v0 (A.gminus/Model.baselineW A O π) (A.gplus/Model.baselineW A O π) := by
   obtain ⟨_,hlo,hhi,_,_⟩ := nondegenerate_source_interval A O π hnd
   exact exists_source_fixed_volume A.d _ _ hlo hhi

end RoughRegime.LatticePriors
