module

public import RoughRegime.SpatialAffineLaw
public import Mathlib.Probability.Kernel.Composition.WithDensity


@[expose] public section
/-! Exact conditional-law representation of the hard observation measure,
on arbitrary measurable response spaces. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  {η : Measure X} {π : Measure Z} [IsProbabilityMeasure η] [IsProbabilityMeasure π]

 def conditionalKernel (S : Scores π) (F : Field η) : Kernel X Z :=
   (Kernel.const X π).withDensity (fun x z => ENNReal.ofReal (responseFactor S F x z))

 omit [IsProbabilityMeasure η] in
 theorem conditionalKernel_apply (S : Scores π) (F : Field η)
     (hsmall : F.epsilon*S.C ≤ 1/4) (x : X) :
     conditionalKernel S F x = (conditionalLaw S F hsmall x).measure := by
   unfold conditionalKernel
   rw [Kernel.withDensity_apply _ (responseFactor_measurable S F).ennreal_ofReal]
   rfl

 omit [IsProbabilityMeasure η] in
 theorem conditionalKernel_markov (S : Scores π) (F : Field η)
     (hsmall : F.epsilon*S.C ≤ 1/4) : IsMarkovKernel (conditionalKernel S F) where
   isProbabilityMeasure x := by
     rw [conditionalKernel_apply S F hsmall x]
     exact (conditionalLaw S F hsmall x).isProbabilityMeasure

 theorem law_eq_conditional_joint (S : Scores π) (F : Field η)
     (hsmall : F.epsilon*S.C ≤ 1/4) :
     (law S F hsmall).measure =
       (η.withDensity (fun x => ENNReal.ofReal (F.p x))) ⊗ₘ conditionalKernel S F := by
   haveI : IsMarkovKernel ((Kernel.const X π).withDensity
     (fun x z => ENNReal.ofReal (responseFactor S F x z))) := conditionalKernel_markov S F hsmall
   change (η.prod π).withDensity (fun o => ENNReal.ofReal (F.p o.1*responseFactor S F o.1 o.2)) = _
   unfold conditionalKernel
   rw [Measure.withDensity_compProd_withDensity F.measurableP.ennreal_ofReal
     (responseFactor_measurable S F).ennreal_ofReal,Measure.compProd_const]
   congr 1
   funext o
   exact ENNReal.ofReal_mul (F.densityBounds o.1).1

end RoughRegime.SpatialAffine
