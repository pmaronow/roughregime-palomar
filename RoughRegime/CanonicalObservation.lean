module

public import RoughRegime.CanonicalAdmissibility
public import RoughRegime.SpatialModel


@[expose] public section
/-! Every literal canonical lattice state produces a genuine normalized
observation law and a measurable observation Markov kernel. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.LatticePriors

 structure CanonicalFrame (D N : ℕ) (ι : Type*) [Fintype ι] where
   U : SmoothStep
   Q : ℕ
   M : ℕ
   a : ι → ℕ
   q : ι → Fin (D+1)
   gamma : ι → ℝ
   eta : ι → ℝ
   lambda : ι → ℝ
   gamma_pos : ∀ i, 0 < gamma i
   gamma_le : ∀ i, gamma i ≤ 1/4
   offset : ℝ
   ell : ℝ
   p0 : ℝ
   rminus : ℝ
   rplus : ℝ
   delta : ℝ
   Au : ℝ
   Av : ℝ
   ell_pos : 0 < ell
   offset_nonneg : 0 ≤ offset
   size_bound : offset+ell*(2*N : ℕ) ≤ 1
   rminus_pos : 0 < rminus
   interval : rminus < rplus
   delta_pos : 0 < delta
   delta_r : delta ≤ ((rminus+rplus)/2-rminus)/2
   delta_p0 : delta ≤ (p0-rminus)/2
   delta_p1 : delta ≤ (rplus-p0)/2
   Au_nonneg : 0 ≤ Au
   Av_nonneg : 0 ≤ Av
   inner : Model.Covariate (D+1) → ℝ
   outer : Model.Covariate (D+1) → ℝ
   inner_smooth : ContDiff ℝ ∞ inner
   outer_smooth : ContDiff ℝ ∞ outer
   inner_zero : ∀ y, y∉unitCubeOpen (D+1) → inner y=0
   outer_zero : ∀ y, y∉unitCubeOpen (D+1) → outer y=0
   inner_bound : ∀ y, |inner y| ≤ 1
   outer_bound : ∀ y, 0 ≤ outer y ∧ outer y ≤ 1
   denominator_ne : 1-(ell*(2*N : ℕ))^(D+1)*(∫ y, outer y ∂Model.cubeVolume (D+1)) ≠ 0
   baseline_eq : p0=sourceBaseline ((ell*(2*N : ℕ))^(D+1))
     (∫ y, outer y ∂Model.cubeVolume (D+1)) ((rminus+rplus)/2)

namespace CanonicalFrame
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

 def p (z : GridPair D N → PairState ι) : Model.Covariate (D+1) → ℝ :=
   globalDensity F.offset F.ell F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
     F.outer (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
 def u (z : GridPair D N → PairState ι) : Model.Covariate (D+1) → ℝ :=
   globalProfile F.offset F.ell F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
     F.Au F.inner F.outer (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
     (stateSignU z) (stateGates F.Q F.M F.eta F.lambda z)
 def v (z : GridPair D N → PairState ι) : Model.Covariate (D+1) → ℝ :=
   globalProfile F.offset F.ell F.p0 ((F.rminus+F.rplus)/2) ((F.rplus-F.rminus)/2-F.delta)
     F.Av F.inner F.outer (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
     (stateSignV z) (stateGates F.Q F.M F.eta F.lambda z)

 theorem realization (z : GridPair D N → PairState ι) :
     RealizationProperties (F.p z) (F.u z) (F.v z) F.rminus F.rplus F.delta F.Au F.Av
       (gridRegion (D+1) N F.offset F.ell) :=
   canonical_realization_properties F.U F.Q F.M F.a F.q F.gamma F.eta F.lambda F.gamma_pos F.gamma_le
     F.offset F.ell F.p0 F.rminus F.rplus F.delta F.Au F.Av F.ell_pos F.offset_nonneg F.size_bound
     F.rminus_pos F.interval F.delta_pos F.delta_r F.delta_p0 F.delta_p1 F.Au_nonneg F.Av_nonneg
     F.inner F.outer F.inner_smooth F.outer_smooth F.inner_zero F.outer_zero F.inner_bound F.outer_bound
     F.denominator_ne F.baseline_eq z

 def field (z : GridPair D N → PairState ι) : SpatialAffine.Field (Model.cubeVolume (D+1)) where
   p := F.p z
   u := F.u z
   v := F.v z
   measurableP := (F.realization z).density_smooth.continuous.measurable
   measurableU := (F.realization z).u_smooth.continuous.measurable
   measurableV := (F.realization z).v_smooth.continuous.measurable
   P := F.rplus
   nonnegativeP := F.rminus_pos.le.trans F.interval.le
   densityBounds x := by
     have hb := (F.realization z).margins x
     have hr := F.rminus_pos
     have hd := F.delta_pos
     constructor <;> linarith
   integralP := (F.realization z).normalized
   epsilon := (F.Au+F.Av)/F.rminus
   nonnegativeEpsilon := div_nonneg (add_nonneg F.Au_nonneg F.Av_nonneg) F.rminus_pos.le
   boundU x := (F.realization z).u_bound x |>.trans
     (div_le_div_of_nonneg_right (le_add_of_nonneg_right F.Av_nonneg) F.rminus_pos.le)
   boundV x := (F.realization z).v_bound x |>.trans
     (div_le_div_of_nonneg_right (le_add_of_nonneg_left F.Au_nonneg) F.rminus_pos.le)

 theorem field_p_measurable :
     Measurable (fun zx : (GridPair D N → PairState ι) × Model.Covariate (D+1) => (F.field zx.1).p zx.2) :=
   canonicalDensity_joint_measurable F.U F.M F.a F.q F.gamma F.gamma_pos F.gamma_le
     F.offset F.ell F.p0 _ _ F.outer F.outer_smooth.continuous.measurable
 theorem field_u_measurable :
     Measurable (fun zx : (GridPair D N → PairState ι) × Model.Covariate (D+1) => (F.field zx.1).u zx.2) := by
   simpa [field,u] using canonicalProfile_joint_measurable F.U F.Q F.M F.a F.q F.gamma F.eta F.lambda
     F.gamma_pos F.gamma_le F.offset F.ell F.p0 _ _ F.Au F.inner F.outer
     F.inner_smooth.continuous.measurable F.outer_smooth.continuous.measurable true
 theorem field_v_measurable :
     Measurable (fun zx : (GridPair D N → PairState ι) × Model.Covariate (D+1) => (F.field zx.1).v zx.2) := by
   simpa [field,v] using canonicalProfile_joint_measurable F.U F.Q F.M F.a F.q F.gamma F.eta F.lambda
     F.gamma_pos F.gamma_le F.offset F.ell F.p0 _ _ F.Av F.inner F.outer
     F.inner_smooth.continuous.measurable F.outer_smooth.continuous.measurable false

 def observationKernel {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
     (S : SpatialAffine.Scores (π : Measure Z)) (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) :
     ProbabilityTheory.Kernel (GridPair D N → PairState ι) (Model.Covariate (D+1)×Z) :=
   SpatialAffine.observationKernel S F.field (fun _ => hsmall) F.field_p_measurable F.field_u_measurable F.field_v_measurable

 instance observationKernel_markov {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
     (S : SpatialAffine.Scores (π : Measure Z)) (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) :
     ProbabilityTheory.IsMarkovKernel (F.observationKernel π S hsmall) := by
   exact SpatialAffine.observationKernel_markov S F.field (fun _ => hsmall)
     F.field_p_measurable F.field_u_measurable F.field_v_measurable

 theorem observationKernel_density {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
     (S : SpatialAffine.Scores (π : Measure Z)) (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
     (z : GridPair D N → PairState ι) :
     F.observationKernel π S hsmall z =
       ((Model.cubeVolume (D+1)).prod (π : Measure Z)).withDensity
         (fun o => ENNReal.ofReal (F.p z o.1*(1+F.u z o.1*S.su o.2+F.v z o.1*S.sv o.2))) := rfl

end CanonicalFrame
end RoughRegime.LatticePriors
