module

public import RoughRegime.SpatialScores


@[expose] public section
/-! The true target of the actual spatial affine observation law is a
measurable function of its latent source parameter. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

 theorem affineIntegrand_measurable (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (S : Scores (π : Measure Z)) :
     Measurable (fun p : ℝ×ℝ => affineIntegrand A O π S p.1 p.2) := by
   have hm (f : Z → ℝ) : Measurable (fun p : ℝ×ℝ => affineMean π S f p.1 p.2) :=
     (affineMean_smooth π S f).continuous.measurable
   unfold affineIntegrand
   exact (hm O.W).add (measurable_const.mul (((hm O.U).mul (hm O.V)).div (hm O.D)))

 theorem model_target_measurable (A : Model.Parameters) {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
     (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (S : Scores (π : Measure Z))
     (F : W → Field (Model.cubeVolume A.d)) (hsmall : ∀ z, (F z).epsilon*S.C ≤ 1/4)
     (hp : Measurable (fun zx : W×Model.Covariate A.d => (F zx.1).p zx.2))
     (hu : Measurable (fun zx : W×Model.Covariate A.d => (F zx.1).u zx.2))
     (hv : Measurable (fun zx : W×Model.Covariate A.d => (F zx.1).v zx.2))
     (hbase : 0 < Model.baselineW A O π) :
     Measurable (fun z => Model.target A O (law S (F z) (hsmall z)).probabilityMeasure) := by
   have hm : Measurable (fun zx : W×Model.Covariate A.d =>
       (F zx.1).p zx.2*affineIntegrand A O π S ((F zx.1).u zx.2) ((F zx.1).v zx.2)) :=
     hp.mul ((affineIntegrand_measurable A O π S).comp (hu.prodMk hv))
   have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := Model.cubeVolume A.d)).measurable
   have he : (fun z => Model.target A O (law S (F z) (hsmall z)).probabilityMeasure) =
       fun z => ∫ x, (F z).p x*affineIntegrand A O π S ((F z).u x) ((F z).v x) ∂Model.cubeVolume A.d := by
     funext z
     exact model_target_integral A O π S (F z) (hsmall z) hbase
   rw [he]
   exact hi

end RoughRegime.SpatialAffine
