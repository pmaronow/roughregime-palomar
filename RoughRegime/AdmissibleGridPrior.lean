module

public import RoughRegime.AdmissibleSelectedData
public import RoughRegime.AdmissibleProductTargets
public import RoughRegime.AdmissibleGridChoice


@[expose] public section
/-! The original universal grid-prior hypothesis. This raw prior data contains
neither a statistical distance assumption nor a small-response assumption.
The latter is supplied automatically by the selected amplitudes. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissibleReduction
open ReductionScales AdmissibleTargets
universe uH uX uZ uY
set_option backward.isDefEq.respectTransparency false

structure GridPrior {X : Type uX} {Z : Type uZ} {Y : Type uY}
    [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (π : ProbabilityMeasure Z)
    (A : AbstractScaleParameters) (S : NaturalScaleChoice A)
    (C0 c2 : ℝ) (n B : ℕ) where
  H : Type uH
  [measurableH : MeasurableSpace H]
  p : ℕ
  [positivePairs : NeZero p]
  blocks_eq : B=2*p
  barp : ℝ
  barp_pos : 0<barp
  pair_mass_budget : A.v0*barp ≤ 1
  pairs : Fin p→AdmissiblePhasePair (H:=H) μ A.lo A.hi barp C0
  prior : Fin p→ProbabilityMeasure H
  outside : ProbabilityMeasure Y
  placement : Fin p→X×Z→Y
  placement_measurable : ∀i,Measurable (placement i)
  coefficient : ∀i j,frequency n A.theta A.tau ≤ j→
    (pairs i).field.gammaNorm (prior i:Measure H) ((2:ENNReal)•μ)
      (amplitude A.epsilonU B (S.R n) A.a (S.m n))
      (amplitude A.epsilonV B (S.R n) A.b (S.m n)) (frequency n A.theta A.tau) j ≤
      A.CΓ^(j+1)*(amplitude A.epsilonU B (S.R n) A.a (S.m n))^2*
        (amplitude A.epsilonV B (S.R n) A.b (S.m n))^2*
        Real.exp (A.CE*frequency n A.theta A.tau)*
        LatticePriors.gammaSpatialFactor (S.R n) (frequency n A.theta A.tau) j
  bilinear : c2*(amplitude A.epsilonU B (S.R n) A.a (S.m n))*
      (amplitude A.epsilonV B (S.R n) A.b (S.m n))*
      Upper.narrowedRho A.lo A.hi ((Real.log n)^(-2:ℝ))^(frequency n A.theta A.tau) ≤
    |(∫q,independentTarget pairs (fun x=>x.1*x.2) (A.v0/(p:ℝ))
          (amplitude A.epsilonU B (S.R n) A.a (S.m n))
          (amplitude A.epsilonV B (S.R n) A.b (S.m n)) q
        ∂independentPrior (fun i=>(prior i:Measure H)) (frequency n A.theta A.tau) true)-
      (∫q,independentTarget pairs (fun x=>x.1*x.2) (A.v0/(p:ℝ))
          (amplitude A.epsilonU B (S.R n) A.a (S.m n))
          (amplitude A.epsilonV B (S.R n) A.b (S.m n)) q
        ∂independentPrior (fun i=>(prior i:Measure H)) (frequency n A.theta A.tau) false)|

namespace GridPrior
variable {X : Type uX} {Z : Type uZ} {Y : Type uY}
    [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : ProbabilityMeasure Z}
    {A : AbstractScaleParameters} {S : NaturalScaleChoice A} {C0 c2 : ℝ} {n : ℕ}

attribute [instance] GridPrior.measurableH GridPrior.positivePairs

 def experiment (G : GridPrior (Y:=Y) μ π A S C0 c2 n (S.B n))
     (scores : SpatialAffine.Scores (π:Measure Z)) (hC0 : 0 ≤ C0)
     (hAu : 0 ≤ S.Au n) (hAv : 0 ≤ S.Av n)
     (hsmall : C0*(S.Au n+S.Av n)*scores.C ≤ 1/4) :
     AdmissiblePhaseExperiment (H:=G.H) (Y:=Y) G.p μ π where
   lo := A.lo
   hi := A.hi
   barp := G.barp
   C0 := C0
   v0 := A.v0
   Au := S.Au n
   Av := S.Av n
   lo_pos := A.hlo
   hi_nonneg := A.hlo.le.trans A.hlt.le
   barp_pos := G.barp_pos
   C0_nonneg := hC0
   volume_nonneg := A.hv.le
   pair_mass_budget := G.pair_mass_budget
   amplitudeU_nonneg := hAu
   amplitudeV_nonneg := hAv
   scores := scores
   small := hsmall
   pairs := G.pairs
   outside := G.outside
   placement := G.placement
   placement_measurable := G.placement_measurable

 theorem experiment_coefficient (G : GridPrior (Y:=Y) μ π A S C0 c2 n (S.B n))
     (scores : SpatialAffine.Scores (π:Measure Z)) (hC0 : 0 ≤ C0)
     (hAu : 0 ≤ S.Au n) (hAv : 0 ≤ S.Av n)
     (hsmall : C0*(S.Au n+S.Av n)*scores.C ≤ 1/4) :
     ∀i j,frequency n A.theta A.tau ≤ j→
       ((G.experiment scores hC0 hAu hAv hsmall).pairs i).field.gammaNorm
         (G.prior i:Measure G.H) ((2:ENNReal)•μ) (S.Au n) (S.Av n) (frequency n A.theta A.tau) j ≤
       A.CΓ^(j+1)*(S.Au n)^2*(S.Av n)^2*Real.exp (A.CE*frequency n A.theta A.tau)*
         LatticePriors.gammaSpatialFactor (S.R n) (frequency n A.theta A.tau) j := by
   intro i j hj
   simpa only [←S.Au_eq n,←S.Av_eq n,experiment] using G.coefficient i j hj

 theorem experiment_bilinear (G : GridPrior (Y:=Y) μ π A S C0 c2 n (S.B n))
     (scores : SpatialAffine.Scores (π:Measure Z)) (hC0 : 0 ≤ C0)
     (hAu : 0 ≤ S.Au n) (hAv : 0 ≤ S.Av n)
     (hsmall : C0*(S.Au n+S.Av n)*scores.C ≤ 1/4) :
     c2*S.gap n ≤
       |(∫q,(G.experiment scores hC0 hAu hAv hsmall).targetFunctional (fun x=>x.1*x.2) q
           ∂AdmissiblePhaseExperiment.parameterPrior (fun i=>(G.prior i:Measure G.H)) (frequency n A.theta A.tau) true)-
        (∫q,(G.experiment scores hC0 hAu hAv hsmall).targetFunctional (fun x=>x.1*x.2) q
           ∂AdmissiblePhaseExperiment.parameterPrior (fun i=>(G.prior i:Measure G.H)) (frequency n A.theta A.tau) false)| := by
   simpa only [←S.Au_eq n,←S.Av_eq n,S.gap_eq,mul_assoc,experiment,
     AdmissiblePhaseExperiment.targetFunctional,independentTarget,
     AdmissiblePhaseExperiment.parameterPrior,independentPrior] using G.bilinear

end GridPrior
end RoughRegime.PoissonMeasure.AdmissibleReduction
