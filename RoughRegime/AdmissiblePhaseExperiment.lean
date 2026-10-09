module

public import RoughRegime.AdmissiblePhaseLikelihood
public import RoughRegime.FinitePairPlacement


@[expose] public section
/-! Actual physical experiments for arbitrary admissible phase pairs. Equal
pair masses and a fixed outside law give a true normalized observation law;
one fixed Markov kernel reconstructs its full Poisson observation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 def uniformPairWeights (p : ℕ) (mass : ℝ≥0) : Option (Fin p)→ℝ≥0
  | none=>1-mass
  | some _=>mass/(p:ℝ≥0)
 theorem uniformPairWeights_sum (p : ℕ) [NeZero p] (mass : ℝ≥0) (hm : mass≤1) :
    ∑ i,uniformPairWeights p mass i=1 := by
  have hp : (p:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne p
  simp only [Fintype.sum_option,uniformPairWeights,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul]
  rw [mul_comm (p:ℝ≥0) (mass/(p:ℝ≥0)),div_mul_cancel₀ mass hp,tsub_add_cancel_of_le hm]

structure AdmissiblePhaseExperiment {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Y] (p : ℕ) (μ : Measure X) (π : ProbabilityMeasure Z) where
  lo : ℝ
  hi : ℝ
  barp : ℝ
  C0 : ℝ
  v0 : ℝ
  Au : ℝ
  Av : ℝ
  lo_pos : 0<lo
  hi_nonneg : 0≤hi
  barp_pos : 0<barp
  C0_nonneg : 0≤C0
  volume_nonneg : 0≤v0
  pair_mass_budget : v0*barp≤1
  amplitudeU_nonneg : 0≤Au
  amplitudeV_nonneg : 0≤Av
  scores : SpatialAffine.Scores (π:Measure Z)
  small : C0*(Au+Av)*scores.C≤1/4
  pairs : Fin p→AdmissiblePhasePair (H:=H) μ lo hi barp C0
  outside : ProbabilityMeasure Y
  placement : Fin p→X×Z→Y
  placement_measurable : ∀ i,Measurable (placement i)

namespace AdmissiblePhaseExperiment
variable {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Y] {p : ℕ} [NeZero p]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : ProbabilityMeasure Z}
    (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)

 def pairMass : ℝ≥0 := ⟨E.v0*E.barp,mul_nonneg E.volume_nonneg E.barp_pos.le⟩
 def weights : Option (Fin p)→ℝ≥0 := uniformPairWeights p E.pairMass
 omit [IsProbabilityMeasure μ] in
 theorem weights_sum : ∑ i,E.weights i=1 :=
  uniformPairWeights_sum p E.pairMass (by exact_mod_cast E.pair_mass_budget)
 def pairProbability (i : Fin p) (q : PhaseParameter H) : ProbabilityMeasure (X×Z) :=
  (SpatialAffine.law E.scores ((E.pairs i).spatialField E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
    E.Au E.Av E.amplitudeU_nonneg E.amplitudeV_nonneg q) E.small).probabilityMeasure
 def observationProbability (q : Fin p→PhaseParameter H) : ProbabilityMeasure Y :=
  placementObservation E.weights E.weights_sum E.outside (fun i=>E.pairProbability i (q i))
    E.placement E.placement_measurable
 def pairProcess (q : Fin p→PhaseParameter H) (rate : ℝ≥0) :
    Measure (Fin p→PointConfiguration (X×Z)) :=
  placementPairProcess E.weights (fun i=>E.pairProbability i (q i)) rate
 instance pairProcess_probability (q : Fin p→PhaseParameter H) (rate : ℝ≥0) :
    IsProbabilityMeasure (E.pairProcess q rate) := by unfold pairProcess;infer_instance
 def poissonPlacementKernel (rate : ℝ≥0) : Kernel (Fin p→PointConfiguration (X×Z)) (PointConfiguration Y) :=
  placementKernel E.weights E.outside E.placement E.placement_measurable rate
 instance poissonPlacementKernel_markov (rate : ℝ≥0) : IsMarkovKernel (E.poissonPlacementKernel rate) := by
  unfold poissonPlacementKernel;infer_instance
 theorem poissonPlacementKernel_law (q : Fin p→PhaseParameter H) (rate : ℝ≥0) (hr : 0<rate) :
    E.poissonPlacementKernel rate ∘ₘ E.pairProcess q rate=referenceProcess (E.observationProbability q:Measure Y) rate :=
  placementKernel_law E.weights E.weights_sum E.outside _ E.placement E.placement_measurable rate hr

 omit [NeZero p] [IsProbabilityMeasure μ] in
 theorem pair_rate (i : Fin p) (rate : ℝ≥0) :
    (rate*E.weights (some i):ℝ≥0)=rate*(E.pairMass/(p:ℝ≥0)) := rfl
 omit [NeZero p] [IsProbabilityMeasure μ] in
 theorem pair_rate_physical (i : Fin p) (rate : ℝ≥0) :
    ((rate*E.weights (some i):ℝ≥0):ℝ)=(rate:ℝ)*2*E.v0*E.barp/(2*p:ℕ) := by
  simp only [weights,uniformPairWeights,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_natCast]
  change (rate:ℝ)*((E.v0*E.barp)/(p:ℝ))=(rate:ℝ)*2*E.v0*E.barp/((2*p:ℕ):ℝ)
  push_cast
  field_simp
 omit [NeZero p] [IsProbabilityMeasure μ] in
 theorem outside_weight : (E.weights none:ℝ)=1-E.v0*E.barp := by
  have hm : E.pairMass≤1 := by exact_mod_cast E.pair_mass_budget
  change ((1-E.pairMass:ℝ≥0):ℝ)=1-E.v0*E.barp
  rw [NNReal.coe_sub hm,NNReal.coe_one]
  rfl

 omit [NeZero p] in
 theorem pair_density_eq (i : Fin p) (q : PhaseParameter H) (o : X×Z) :
    (SpatialAffine.law E.scores ((E.pairs i).spatialField E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
      E.Au E.Av E.amplitudeU_nonneg E.amplitudeV_nonneg q) E.small).density o=
      1+((E.pairs i).field.scale (1/E.barp)).markedFactor E.Au E.Av
        (AdmissiblePhasePair.phaseScores E.scores) q o :=
  (E.pairs i).spatialLaw_density_eq E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
    E.Au E.Av E.amplitudeU_nonneg E.amplitudeV_nonneg E.small q o

end AdmissiblePhaseExperiment
end RoughRegime.PoissonMeasure
