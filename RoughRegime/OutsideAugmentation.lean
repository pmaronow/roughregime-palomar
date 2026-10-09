module

public import RoughRegime.CanonicalOutside
public import RoughRegime.CanonicalPairMarks
public import RoughRegime.HeterogeneousKernels
public import RoughRegime.PoissonMarkMaps


@[expose] public section
/-! A common Markov kernel independently adds the fixed outside Poisson
process to the physical pair processes and reconstructs the full observation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]

 def outsideAugmentationKernel (Q : Measure A) [IsProbabilityMeasure Q] :
    Kernel (ι → A) (Option ι → A) :=
  (Kernel.id ×ₖ Kernel.const (ι → A) Q).map
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => A)).symm

 instance outsideAugmentationKernel_markov (Q : Measure A) [IsProbabilityMeasure Q] :
    IsMarkovKernel (outsideAugmentationKernel (ι := ι) Q) := by
  unfold outsideAugmentationKernel
  exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => A)).symm.measurable

 theorem outsideAugmentationKernel_law (μ : Option ι → Measure A)
    [∀ i, IsProbabilityMeasure (μ i)] :
    outsideAugmentationKernel (μ none) ∘ₘ Measure.pi (fun i => μ (some i)) = Measure.pi μ := by
  unfold outsideAugmentationKernel
  rw [← Measure.map_comp _ _ (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => A)).symm.measurable,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  exact Measure.pi_map_piOptionEquivProd μ

end RoughRegime.PoissonMeasure

namespace RoughRegime.LatticePriors.CanonicalFrame
open RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

 def outsideProcess {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) :
    Measure (PointConfiguration (Model.Covariate (D+1) × Z)) :=
  referenceProcess (F.componentProbability π S hsmall F.defaultState none :
    Measure (Model.Covariate (D+1) × Z)) (rate*F.componentWeights π S hsmall none)

 instance outsideProcess_isProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) :
    IsProbabilityMeasure (F.outsideProcess π S hsmall rate) := by
  unfold outsideProcess
  infer_instance

 def pairObservationKernel {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) :
    Kernel (GridPair D N → PointConfiguration ((Model.Covariate (D+1) × Bool) × Z))
      (PointConfiguration (Model.Covariate (D+1) × Z)) :=
  PoissonSuperposition.superpositionKernel ∘ₖ
    (outsideAugmentationKernel (F.outsideProcess π S hsmall rate) ∘ₖ
      Kernel.deterministic (componentPointMap (F.localPairEmbedding (Z := Z)))
        (measurable_componentPointMap _ (F.localPairEmbedding_measurable)))

 instance pairObservationKernel_markov {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4) (rate : ℝ≥0) :
    IsMarkovKernel (F.pairObservationKernel π S hsmall rate) := by
  unfold pairObservationKernel
  infer_instance

 def pairProcessLaw {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (z : GridPair D N → PairState ι) (rate : ℝ≥0) :
    Measure (GridPair D N → PointConfiguration ((Model.Covariate (D+1) × Bool) × Z)) :=
  Measure.pi (fun k => referenceProcess (F.localPairLaw π S hsmall (z k)).measure
    (rate*F.componentWeights π S hsmall (some k)))

 instance pairProcessLaw_isProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (z : GridPair D N → PairState ι) (rate : ℝ≥0) :
    IsProbabilityMeasure (F.pairProcessLaw π S hsmall z rate) := by
  unfold pairProcessLaw
  infer_instance

 theorem pairObservationKernel_law {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C ≤ 1/4)
    (z : GridPair D N → PairState ι) (rate : ℝ≥0) (hr : 0 < rate) :
    F.pairObservationKernel π S hsmall rate ∘ₘ F.pairProcessLaw π S hsmall z rate =
      referenceProcess (F.observationProbability π S hsmall z : Measure (Model.Covariate (D+1) × Z)) rate := by
  unfold pairObservationKernel
  rw [← Measure.comp_assoc, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
  rw [pairProcessLaw, referenceProcess_product_map _ _ _ (F.localPairEmbedding_measurable)]
  simp_rw [F.localPairLaw_map_componentLaw π S hsmall z]
  change PoissonSuperposition.superpositionKernel ∘ₘ
    (outsideAugmentationKernel (referenceProcess
      (F.componentProbability π S hsmall z none : Measure (Model.Covariate (D+1) × Z))
      (rate*F.componentWeights π S hsmall none)) ∘ₘ
      Measure.pi (fun k => referenceProcess
        (F.componentProbability π S hsmall z (some k) : Measure (Model.Covariate (D+1) × Z))
        (rate*F.componentWeights π S hsmall (some k)))) = _
  rw [outsideAugmentationKernel_law (fun i => referenceProcess
    (F.componentProbability π S hsmall z i : Measure (Model.Covariate (D+1) × Z))
      (rate*F.componentWeights π S hsmall i))]
  exact F.component_superposition π S hsmall z rate hr

end RoughRegime.LatticePriors.CanonicalFrame
