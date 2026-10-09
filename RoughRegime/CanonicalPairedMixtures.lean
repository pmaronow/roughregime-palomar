module

public import RoughRegime.CanonicalPoissonMixtures
public import RoughRegime.OutsideAugmentation
public import RoughRegime.ProductDensityFintype


@[expose] public section
/-! The actual independent native priors, their observation density products,
and the common placement kernel for the full canonical experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.LatticePriors.CanonicalFrame
open RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

def pairWeight : ℝ≥0 := ⟨F.pairMass,F.pairMass_positive.le⟩
def pairPoissonRate (rate : ℝ≥0) : ℝ≥0 := rate*F.pairWeight

theorem componentWeights_pairWeight {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (k : GridPair D N) :
    F.componentWeights π S hsmall (some k)=F.pairWeight := by
  apply ENNReal.coe_inj.mp
  rw [F.componentWeights_pair π S hsmall k]
  change ENNReal.ofReal (F.pairWeight : ℝ)=(F.pairWeight : ℝ≥0∞)
  exact ENNReal.ofReal_coe_nnreal

def physicalPairProductKernel {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) :
    Kernel (GridPair D N→PairState ι)
      (GridPair D N→PointConfiguration ((Model.Covariate (D+1)×Bool)×Z)) :=
  KernelTransfers.productKernel (fun _ : GridPair D N=>F.physicalPairKernel π S hsmall rate)

instance physicalPairProductKernel_markov {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) :
    IsMarkovKernel (F.physicalPairProductKernel π S hsmall rate) := by
  unfold physicalPairProductKernel
  infer_instance

def canonicalPairedMixture {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) (positive : Bool) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : GridPair D N=>referenceProcess (F.localPairBase π) rate)) :=
  LowerMeasure.fintypeProductDensityLaw (fun _ : GridPair D N=>F.canonicalPairMixture ν π S hsmall rate positive)

/-- The full pair-data mixture is the actual observation marginal of the
independent native parameter prior, with no product-law assumption. -/
theorem physicalPairProductKernel_marginal {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) (positive : Bool) :
    (Measure.pi (fun _ : GridPair D N=>blockPrior ν F.M positive) ⊗ₘ
      F.physicalPairProductKernel π S hsmall rate).snd =
      (F.canonicalPairedMixture ν π S hsmall rate positive).measure := by
  rw [canonicalPairedMixture,LowerMeasure.fintypeProductDensityLaw_measure]
  exact KernelTransfers.productKernel_marginal_eq
    (fun _ : GridPair D N=>F.physicalPairKernel π S hsmall rate)
    (fun _ : GridPair D N=>blockPrior ν F.M positive)
    (fun _ : GridPair D N=>(F.canonicalPairMixture ν π S hsmall rate positive).measure)
    (fun _=>F.physicalPairKernel_marginal ν π S hsmall rate positive)

theorem physicalPairProductKernel_apply {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0)
    (z : GridPair D N→PairState ι) :
    F.physicalPairProductKernel π S hsmall (F.pairPoissonRate rate) z=
      F.pairProcessLaw π S hsmall z rate := by
  change Measure.pi (fun k=>F.physicalPairKernel π S hsmall (F.pairPoissonRate rate) (z k))=_
  simp_rw [F.physicalPairKernel_apply π S hsmall]
  unfold pairProcessLaw
  simp_rw [F.componentWeights_pairWeight π S hsmall]
  rfl

/-- A fixed Markov placement kernel reconstructs the literal full
observation PPP from the conditional pair-data experiment. -/
theorem physicalPairProductKernel_placement {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) (hr : 0<rate)
    (z : GridPair D N→PairState ι) :
    F.pairObservationKernel π S hsmall rate ∘ₘ
      F.physicalPairProductKernel π S hsmall (F.pairPoissonRate rate) z =
      referenceProcess (F.observationProbability π S hsmall z :
        Measure (Model.Covariate (D+1)×Z)) rate := by
  rw [F.physicalPairProductKernel_apply π S hsmall rate z]
  exact F.pairObservationKernel_law π S hsmall z rate hr

theorem canonicalPairedMixture_hellinger_le {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) :
    GeneralTesting.hellingerSquared (F.canonicalPairedMixture ν π S hsmall rate true)
      (F.canonicalPairedMixture ν π S hsmall rate false) ≤
      (Fintype.card (GridPair D N):ℝ)*GeneralTesting.hellingerSquared
        (F.canonicalPairMixture ν π S hsmall rate true) (F.canonicalPairMixture ν π S hsmall rate false) := by
  have hh:=LowerMeasure.hellinger_fintypeProduct_le
    (fun _ : GridPair D N=>F.canonicalPairMixture ν π S hsmall rate true)
    (fun _ : GridPair D N=>F.canonicalPairMixture ν π S hsmall rate false)
  simpa only [canonicalPairedMixture,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh

end RoughRegime.LatticePriors.CanonicalFrame
