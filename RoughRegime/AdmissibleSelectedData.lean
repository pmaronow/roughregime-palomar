module

public import RoughRegime.AdmissibleReductionNumerics
public import RoughRegime.AdmissibleExperimentTarget
public import RoughRegime.AdmissibleExperimentKernel


@[expose] public section
/-! Selected genuine admissible-prior data. Latent spaces and pair counts
may change with the sample size. Only original coefficient, bilinear target,
class membership and target-identification hypotheses are recorded. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissibleReduction
open ReductionScales
universe uH uX uZ uY

structure SelectedData {X : Type uX} {Z : Type uZ} {Y : Type uY}
    [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (π : ProbabilityMeasure Z)
    (A : AbstractScaleParameters) (S : NaturalScaleChoice A)
    (C0 c2 : ℝ) (scores : SpatialAffine.Scores (π:Measure Z))
    (Phi : ℝ×ℝ→ℝ) (T : ProbabilityMeasure Y→ℝ) (Cls : Set (ProbabilityMeasure Y)) (n : ℕ) where
  H : Type uH
  [measurableH : MeasurableSpace H]
  p : ℕ
  [positivePairs : NeZero p]
  E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π
  prior : Fin p→ProbabilityMeasure H
  blocks_eq : S.B n=2*p
  lo_eq : E.lo=A.lo
  hi_eq : E.hi=A.hi
  C0_eq : E.C0=C0
  volume_eq : E.v0=A.v0
  amplitudeU_eq : E.Au=S.Au n
  amplitudeV_eq : E.Av=S.Av n
  scores_eq : E.scores=scores
  coefficient : ∀i j,frequency n A.theta A.tau ≤ j→
    (E.pairs i).field.gammaNorm (prior i:Measure H) ((2:ENNReal)•μ)
      E.Au E.Av (frequency n A.theta A.tau) j ≤
      A.CΓ^(j+1)*E.Au^2*E.Av^2*Real.exp (A.CE*frequency n A.theta A.tau)*
        LatticePriors.gammaSpatialFactor (S.R n) (frequency n A.theta A.tau) j
  bilinear : c2*S.gap n ≤
    |(∫ q,E.targetFunctional (fun x=>x.1*x.2) q
       ∂AdmissiblePhaseExperiment.parameterPrior (fun i=>(prior i:Measure H)) (frequency n A.theta A.tau) true)-
     (∫ q,E.targetFunctional (fun x=>x.1*x.2) q
       ∂AdmissiblePhaseExperiment.parameterPrior (fun i=>(prior i:Measure H)) (frequency n A.theta A.tau) false)|
  target_eq : ∀ q,T (E.observationProbability q)=E.targetFunctional Phi q
  class_mem : ∀ q,E.observationProbability q∈Cls

end RoughRegime.PoissonMeasure.AdmissibleReduction
