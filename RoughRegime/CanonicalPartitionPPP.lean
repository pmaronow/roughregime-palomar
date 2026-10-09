module

public import RoughRegime.CanonicalPoissonData
public import RoughRegime.GridBoundary


@[expose] public section
/-! The actual canonical observation law splits into its physical pairs and
outside component and is reconstructed by the genuine common Poisson kernel. -/
noncomputable section
open MeasureTheory Set Function ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace RoughRegime.LatticePriors.CanonicalFrame
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

def observedPairSet {Z : Type*} (k : GridPair D N) : Set (Model.Covariate (D + 1) × Z) :=
  Prod.fst ⁻¹' gridPairOpen F.offset F.ell k

def observedPieceSet {Z : Type*} : Option (GridPair D N) → Set (Model.Covariate (D + 1) × Z) :=
  PartitionPoisson.partitionPiece (F.observedPairSet (Z := Z))

theorem observedPairSet_measurable {Z : Type*} [MeasurableSpace Z] (k : GridPair D N) :
    MeasurableSet (F.observedPairSet (Z := Z) k) :=
  (gridPairOpen_measurable F.offset F.ell F.ell_pos k).preimage measurable_fst

theorem observedPairSet_disjoint {Z : Type*} :
    Pairwise (Disjoint on F.observedPairSet (Z := Z)) := by
  intro a b hab
  exact (gridPairOpen_pairwiseDisjoint F.offset F.ell F.ell_pos hab).preimage _

theorem observedPieceSet_measurable {Z : Type*} [MeasurableSpace Z] :
    ∀ i, MeasurableSet (F.observedPieceSet (Z := Z) i) :=
  PartitionPoisson.partitionPiece_measurable _ (F.observedPairSet_measurable)

theorem observedPieceSet_disjoint {Z : Type*} [MeasurableSpace Z] :
    Pairwise (Disjoint on F.observedPieceSet (Z := Z)) :=
  PartitionPoisson.partitionPiece_disjoint _ F.observedPairSet_disjoint

theorem observedPieceSet_cover {Z : Type*} [MeasurableSpace Z] :
    (⋃ i, F.observedPieceSet (Z := Z) i) = univ :=
  PartitionPoisson.partitionPiece_cover _

def covariateDensityLaw (z : GridPair D N → PairState ι) :
    GeneralTesting.DensityLaw (Model.cubeVolume (D + 1)) where
  density := F.p z
  measurable := (F.field z).measurableP
  integrable := (F.realization z).density_smooth.continuous.continuousOn.integrableOn_compact
    (Model.isCompact_cube _)
  nonneg := Filter.Eventually.of_forall fun x => ((F.field z).densityBounds x).1
  integral_one := (F.field z).integralP

theorem observationProbability_marginal {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) (z : GridPair D N → PairState ι) :
    (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)).map Prod.fst =
      (F.covariateDensityLaw z).measure :=
  SpatialAffine.law_marginal S (F.field z) hsmall

theorem covariateDensityLaw_pairMass (z : GridPair D N → PairState ι) (k : GridPair D N) :
    (F.covariateDensityLaw z).measure.real (gridPairOpen F.offset F.ell k) = F.pairMass := by
  have hac : (F.covariateDensityLaw z).measure ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have he := congrArg ENNReal.toReal (measure_congr
    (gridPairClosed_ae_eq_open_of_ac F.offset F.ell F.ell_pos _ hac k))
  change (F.covariateDensityLaw z).measure.real (gridPairClosed F.offset F.ell k) =
    (F.covariateDensityLaw z).measure.real (gridPairOpen F.offset F.ell k) at he
  rw [← he, GeneralTesting.DensityLaw.measureReal_eq_setIntegral _ _
    (gridPairClosed_measurable F.offset F.ell k)]
  have hsub : gridPairClosed F.offset F.ell k ⊆ Model.cube (D + 1) :=
    union_subset (gridBlockClosed_subset_cube F.offset F.ell (k, false) F.ell_pos F.offset_nonneg F.size_bound)
      (gridBlockClosed_subset_cube F.offset F.ell (k, true) F.ell_pos F.offset_nonneg F.size_bound)
  change (∫ x in gridPairClosed F.offset F.ell k, F.p z x
    ∂volume.restrict (Model.cube (D + 1))) = F.pairMass
  rw [Measure.restrict_restrict (gridPairClosed_measurable F.offset F.ell k),
    inter_eq_left.mpr hsub]
  exact globalDensity_geometric_pair_mass F.offset F.ell F.p0 ((F.rminus + F.rplus) / 2)
    ((F.rplus - F.rminus) / 2 - F.delta) F.ell_pos F.offset_nonneg F.size_bound F.outer
    F.outer_smooth F.outer_zero (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
    (fun k => blockPhase_smooth F.U F.M F.a F.q F.gamma _ F.gamma_pos F.gamma_le) k

theorem observationProbability_pairMass {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) (z : GridPair D N → PairState ι)
    (k : GridPair D N) :
    (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)).real
      (F.observedPairSet k) = F.pairMass := by
  unfold Measure.real observedPairSet
  rw [← Measure.map_apply measurable_fst (gridPairOpen_measurable F.offset F.ell F.ell_pos k),
    F.observationProbability_marginal π S hsmall z]
  exact F.covariateDensityLaw_pairMass z k

theorem observationProbability_superposition {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) (z : GridPair D N → PairState ι)
    (rate : ℝ≥0) (hr : 0 < rate) :
    PoissonSuperposition.superpositionKernel ∘ₘ
      Measure.pi (fun i : Option (GridPair D N) => PoissonMeasure.referenceProcess
        (PartitionPoisson.componentLaw (F.observationProbability π S hsmall z) (F.observedPieceSet i) :
          Measure (Model.Covariate (D + 1) × Z))
        (rate * PartitionPoisson.componentMass (F.observationProbability π S hsmall z) (F.observedPieceSet i))) =
      PoissonMeasure.referenceProcess
        (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)) rate :=
  PartitionPoisson.partition_superposition _ _ F.observedPieceSet_measurable
    F.observedPieceSet_disjoint F.observedPieceSet_cover rate hr

end RoughRegime.LatticePriors.CanonicalFrame
