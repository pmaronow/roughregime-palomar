module

public import RoughRegime.CanonicalPartitionPPP


@[expose] public section
/-! The actual outside observation restriction and component rates are common
to every canonical prior realization. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.LatticePriors.CanonicalFrame
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

def defaultState (_F : CanonicalFrame D N ι) : GridPair D N → PairState ι :=
  fun _ => (fun _ => 0, 0, false, false)

theorem outside_not_block {Z : Type*} (o : Model.Covariate (D + 1) × Z)
    (ho : o ∈ F.observedPieceSet none) :
    ∀ b : GridBlock D N, o.1 ∉ gridBlockOpen F.offset F.ell b := by
  change o ∉ ⋃ k : GridPair D N, F.observedPairSet k at ho
  rintro ⟨k, label⟩ hb
  apply ho
  refine mem_iUnion.mpr ⟨k, ?_⟩
  change o.1 ∈ gridPairOpen F.offset F.ell k
  cases label
  · exact Or.inl hb
  · exact Or.inr hb

theorem spatialDensity_outside {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) (z : GridPair D N → PairState ι)
    (o : Model.Covariate (D + 1) × Z) (ho : o ∈ F.observedPieceSet none) :
    (SpatialAffine.law S (F.field z) hsmall).density o = F.p0 := by
  have hb := F.outside_not_block o ho
  have hp : F.p z o.1 = F.p0 :=
    globalDensity_outside F.offset F.ell F.p0 _ _ F.outer F.outer_zero _ _ o.1 hb
  have hu : F.u z o.1 = 0 :=
    globalProfile_outside F.offset F.ell F.p0 _ _ F.Au F.inner F.outer F.inner_zero _ _ _ _ o.1 hb
  have hv : F.v z o.1 = 0 :=
    globalProfile_outside F.offset F.ell F.p0 _ _ F.Av F.inner F.outer F.inner_zero _ _ _ _ o.1 hb
  change F.p z o.1 * (1 + F.u z o.1 * S.su o.2 + F.v z o.1 * S.sv o.2) = _
  rw [hp, hu, hv]
  ring

theorem outside_restriction_common {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4)
    (z z' : GridPair D N → PairState ι) :
    (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)).restrict
      (F.observedPieceSet none) =
    (F.observationProbability π S hsmall z' : Measure (Model.Covariate (D + 1) × Z)).restrict
      (F.observedPieceSet none) := by
  rw [F.observationProbability_measure, F.observationProbability_measure,
    GeneralTesting.DensityLaw.measure, GeneralTesting.DensityLaw.measure,
    restrict_withDensity (F.observedPieceSet_measurable none),
    restrict_withDensity (F.observedPieceSet_measurable none)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (F.observedPieceSet_measurable none)] with o ho
  rw [F.spatialDensity_outside π S hsmall z o ho, F.spatialDensity_outside π S hsmall z' o ho]

theorem componentMass_common {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4)
    (z z' : GridPair D N → PairState ι) (i : Option (GridPair D N)) :
    PartitionPoisson.componentMass (F.observationProbability π S hsmall z) (F.observedPieceSet i) =
      PartitionPoisson.componentMass (F.observationProbability π S hsmall z') (F.observedPieceSet i) := by
  cases i with
  | none =>
    unfold PartitionPoisson.componentMass
    apply congrArg ENNReal.toNNReal
    have he := congrArg (fun μ : Measure (Model.Covariate (D + 1) × Z) => μ univ)
      (F.outside_restriction_common π S hsmall z z')
    simpa only [Measure.restrict_apply_univ] using he
  | some k =>
    apply Subtype.ext
    change (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)).real
      (F.observedPairSet k) =
      (F.observationProbability π S hsmall z' : Measure (Model.Covariate (D + 1) × Z)).real
      (F.observedPairSet k)
    rw [F.observationProbability_pairMass, F.observationProbability_pairMass]

def componentWeights {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) : Option (GridPair D N) → ℝ≥0 :=
  fun i => PartitionPoisson.componentMass (F.observationProbability π S hsmall F.defaultState)
    (F.observedPieceSet i)

def componentProbability {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4)
    (z : GridPair D N → PairState ι) : Option (GridPair D N) →
      ProbabilityMeasure (Model.Covariate (D + 1) × Z)
  | none => PartitionPoisson.componentLaw (F.observationProbability π S hsmall F.defaultState)
      (F.observedPieceSet none)
  | some k => PartitionPoisson.componentLaw (F.observationProbability π S hsmall z)
      (F.observedPairSet k)

theorem componentWeights_sum {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) :
    (∑ i, F.componentWeights π S hsmall i) = 1 :=
  PartitionPoisson.componentMass_sum _ _ F.observedPieceSet_measurable
    F.observedPieceSet_disjoint F.observedPieceSet_cover

theorem component_markMixture {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) (z : GridPair D N → PairState ι) :
    PoissonSuperposition.markMixture (F.componentWeights π S hsmall)
      (fun i => (F.componentProbability π S hsmall z i : Measure (Model.Covariate (D + 1) × Z))) =
      (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)) := by
  unfold PoissonSuperposition.markMixture
  calc
    _ = ∑ i : Option (GridPair D N),
        (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)).restrict
          (F.observedPieceSet i) := by
      apply Finset.sum_congr rfl
      intro i _
      cases i with
      | none =>
        exact (PartitionPoisson.componentMass_smul_componentLaw _ _).trans
          (F.outside_restriction_common π S hsmall F.defaultState z)
      | some k =>
        change (PartitionPoisson.componentMass (F.observationProbability π S hsmall F.defaultState)
          (F.observedPieceSet (some k)) : ℝ≥0∞) •
          (PartitionPoisson.componentLaw (F.observationProbability π S hsmall z) (F.observedPairSet k) :
            Measure (Model.Covariate (D + 1) × Z)) = _
        rw [← F.componentMass_common π S hsmall z F.defaultState (some k)]
        exact PartitionPoisson.componentMass_smul_componentLaw _ _
    _ = _ := PartitionPoisson.partition_restriction_sum _ _ F.observedPieceSet_measurable
      F.observedPieceSet_disjoint F.observedPieceSet_cover

theorem componentWeights_pair {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4) (k : GridPair D N) :
    (F.componentWeights π S hsmall (some k) : ℝ≥0∞) = ENNReal.ofReal F.pairMass := by
  rw [componentWeights, PartitionPoisson.componentMass_coe]
  calc
    _ = ENNReal.ofReal ((F.observationProbability π S hsmall F.defaultState :
        Measure (Model.Covariate (D + 1) × Z)).real (F.observedPairSet k)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := congrArg ENNReal.ofReal (F.observationProbability_pairMass π S hsmall F.defaultState k)

/-- Full actual canonical observation law reconstructed from independent pair
processes and one common outside process, with rates fixed before realizations. -/
theorem component_superposition {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4)
    (z : GridPair D N → PairState ι) (rate : ℝ≥0) (hr : 0 < rate) :
    PoissonSuperposition.superpositionKernel ∘ₘ
      Measure.pi (fun i : Option (GridPair D N) => PoissonMeasure.referenceProcess
        (F.componentProbability π S hsmall z i : Measure (Model.Covariate (D + 1) × Z))
        (rate * F.componentWeights π S hsmall i)) =
      PoissonMeasure.referenceProcess
        (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)) rate := by
  classical
  have hs : (∑ i, rate * F.componentWeights π S hsmall i) = rate := by
    rw [← Finset.mul_sum, F.componentWeights_sum π S hsmall, mul_one]
  rw [PoissonSuperposition.superpositionKernel_comp _ _ (hs.symm ▸ hr), hs]
  have hw : PoissonSuperposition.rateWeights (fun i => rate * F.componentWeights π S hsmall i) =
      F.componentWeights π S hsmall := by
    funext i
    unfold PoissonSuperposition.rateWeights
    rw [hs, mul_div_cancel_left₀ _ hr.ne']
  rw [hw, F.component_markMixture π S hsmall z]

end RoughRegime.LatticePriors.CanonicalFrame
