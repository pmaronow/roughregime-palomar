module

public import RoughRegime.CanonicalObservation
public import RoughRegime.OptionPartition
public import RoughRegime.GlobalAffine


@[expose] public section
/-! Literal observation laws and deterministic pair mass constants for the
canonical source frame. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.LatticePriors.CanonicalFrame
open RoughRegime.LatticeFourier
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

def pairBarDensity : ℝ :=
  F.p0 + (∫ x, F.outer x ∂Model.cubeVolume (D + 1)) * ((F.rminus + F.rplus) / 2 - F.p0)

def pairMass : ℝ := 2 * F.ell ^ (D + 1) * F.pairBarDensity

def observationProbability {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4)
    (z : GridPair D N → PairState ι) : ProbabilityMeasure (Model.Covariate (D + 1) × Z) :=
  (SpatialAffine.law S (F.field z) hsmall).probabilityMeasure

theorem observationProbability_measure {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (hsmall : (F.Au + F.Av) / F.rminus * S.C ≤ 1 / 4)
    (z : GridPair D N → PairState ι) :
    (F.observationProbability π S hsmall z : Measure (Model.Covariate (D + 1) × Z)) =
      (SpatialAffine.law S (F.field z) hsmall).measure := rfl

def localPairDensity {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π : Measure Z)) (w : PairState ι)
    (o : (Model.Covariate (D + 1) × Bool) × Z) : ℝ :=
  (blockDensity F.p0 ((F.rminus + F.rplus) / 2) ((F.rplus - F.rminus) / 2 - F.delta)
    w.2.1 (blockPhase F.U F.M F.a F.q F.gamma w.1) F.outer (RoughRegime.Lower.sign o.1.2) o.1.1 +
    F.Au * RoughRegime.Lower.sign w.2.2.1 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner o.1.1 * S.su o.2 +
    F.Av * RoughRegime.Lower.sign w.2.2.2 * jointGate F.Q F.M F.eta F.lambda w.1 * F.inner o.1.1 * S.sv o.2) /
    F.pairBarDensity

def localPairEmbedding {Z : Type*} (k : GridPair D N)
    (o : (Model.Covariate (D + 1) × Bool) × Z) : Model.Covariate (D + 1) × Z :=
  (gridEmbed F.offset F.ell (k, o.1.2) o.1.1, o.2)

theorem localPairEmbedding_measurable {Z : Type*} [MeasurableSpace Z] (k : GridPair D N) :
    Measurable (F.localPairEmbedding (Z := Z) k) := by
  unfold localPairEmbedding gridEmbed gridOrigin
  fun_prop

theorem pairBarDensity_positive : 0 < F.pairBarDensity := by
  have hp0 : F.rminus ≤ F.p0 := by linarith [F.delta_p0, F.delta_pos]
  have hI0 : 0 ≤ ∫ x, F.outer x ∂Model.cubeVolume (D + 1) :=
    integral_nonneg (fun x => (F.outer_bound x).1)
  have hI1 : (∫ x, F.outer x ∂Model.cubeVolume (D + 1)) ≤ 1 := by
    calc
      _ ≤ ∫ _x, (1 : ℝ) ∂Model.cubeVolume (D + 1) :=
        integral_mono ((F.outer_smooth.continuous.continuousOn.integrableOn_compact
          (Model.isCompact_cube _))) (integrable_const _) (fun x => (F.outer_bound x).2)
      _ = _ := by simp
  have hr0 : F.rminus ≤ (F.rminus + F.rplus) / 2 := by linarith [F.interval]
  unfold pairBarDensity
  nlinarith [mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr hI1),
    mul_nonneg (sub_nonneg.mpr hr0) hI0, F.rminus_pos]

theorem pairMass_positive : 0 < F.pairMass := by
  unfold pairMass
  exact mul_pos (mul_pos (by norm_num) (pow_pos F.ell_pos _)) F.pairBarDensity_positive

end RoughRegime.LatticePriors.CanonicalFrame
