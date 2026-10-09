module

public import RoughRegime.AdmissiblePhaseExperiment
public import RoughRegime.AdmissiblePhaseComparison
public import RoughRegime.HeterogeneousKernels


@[expose] public section
/-! The genuine global observation kernel and its mixture marginal for
arbitrary admissible phase pairs. Pair independence is derived from the
actual product prior and product observation kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissiblePhaseExperiment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Y] {p : ℕ} [NeZero p]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : ProbabilityMeasure Z}
    (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)

 def productPhaseKernel (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1) (rate : ℝ≥0) :
    Kernel (Fin p→PhaseParameter H) (Fin p→PointConfiguration (X×Z)) := by
  letI : ∀ i,IsMarkovKernel ((E.pairs i).poissonKernel E.scores E.Au E.Av (rate*E.weights (some i))) :=
    fun i=>(E.pairs i).poissonKernel_markov E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
      E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small _
  exact KernelTransfers.productKernel (fun i=>(E.pairs i).poissonKernel E.scores E.Au E.Av (rate*E.weights (some i)))
 instance productPhaseKernel_markov (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1) (rate : ℝ≥0) :
    IsMarkovKernel (E.productPhaseKernel hAu1 hAv1 rate) := by unfold productPhaseKernel;infer_instance

 omit [NeZero p] in
 theorem productPhaseKernel_apply (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1) (rate : ℝ≥0)
    (q : Fin p→PhaseParameter H) : E.productPhaseKernel hAu1 hAv1 rate q=E.pairProcess q rate := by
  unfold productPhaseKernel
  rw [KernelTransfers.productKernel_apply]
  unfold pairProcess placementPairProcess
  congr 1
  funext i
  rw [(E.pairs i).poissonKernel_apply E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
    E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small _ (q i)]
  simp_rw [LowerMeasure.iidDensityLaw_measure]
  rfl

 def globalKernel (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1) (rate : ℝ≥0) :
    Kernel (Fin p→PhaseParameter H) (PointConfiguration Y) :=
  E.poissonPlacementKernel rate ∘ₖ E.productPhaseKernel hAu1 hAv1 rate
 instance globalKernel_markov (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1) (rate : ℝ≥0) :
    IsMarkovKernel (E.globalKernel hAu1 hAv1 rate) := by unfold globalKernel;infer_instance
 theorem globalKernel_apply (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1) (rate : ℝ≥0)
    (hr : 0<rate) (q : Fin p→PhaseParameter H) :
    E.globalKernel hAu1 hAv1 rate q=referenceProcess (E.observationProbability q:Measure Y) rate := by
  rw [globalKernel,Kernel.comp_apply,E.productPhaseKernel_apply]
  exact E.poissonPlacementKernel_law q rate hr

 def parameterPrior (ν : Fin p→Measure H) [∀ i,IsProbabilityMeasure (ν i)] (M : ℕ) (positive : Bool) :
    Measure (Fin p→PhaseParameter H) :=
  Measure.pi (fun i=>(phasePrior (ν i) M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure)
 instance parameterPrior_probability (ν : Fin p→Measure H) [∀ i,IsProbabilityMeasure (ν i)] (M : ℕ) (positive : Bool) :
    IsProbabilityMeasure (parameterPrior ν M positive) := by unfold parameterPrior;infer_instance
 def pairMixture (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1)
    (ν : Fin p→Measure H) [∀ i,IsProbabilityMeasure (ν i)] (M : ℕ) (rate : ℝ≥0) (positive : Bool)
    (i : Fin p) : GeneralTesting.DensityLaw (referenceProcess (μ.prod (π:Measure Z)) (rate*E.weights (some i))) :=
  (E.pairs i).poissonMixture (ν i) E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
    E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small M (rate*E.weights (some i)) positive

 omit [NeZero p] in
 theorem productPhaseKernel_marginal (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1)
    (ν : Fin p→Measure H) [∀ i,IsProbabilityMeasure (ν i)] (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    (parameterPrior ν M positive ⊗ₘ E.productPhaseKernel hAu1 hAv1 rate).snd=
      Measure.pi (fun i=>(E.pairMixture hAu1 hAv1 ν M rate positive i).measure) := by
  unfold productPhaseKernel parameterPrior
  rw [KernelTransfers.productKernel_marginal]
  congr 1
  funext i
  exact (E.pairs i).poissonKernel_marginal (ν i) E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
    E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small M _ positive

omit [NeZero p] in
/-- The actual global data marginal is obtained from the actual independent
pair-mixture laws by the one fixed outside-and-placement kernel. -/
 theorem globalKernel_marginal (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1)
    (ν : Fin p→Measure H) [∀ i,IsProbabilityMeasure (ν i)] (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    (parameterPrior ν M positive ⊗ₘ E.globalKernel hAu1 hAv1 rate).snd=
      E.poissonPlacementKernel rate ∘ₘ
        Measure.pi (fun i=>(E.pairMixture hAu1 hAv1 ν M rate positive i).measure) := by
  have h:=E.productPhaseKernel_marginal hAu1 hAv1 ν M rate positive
  rw [Measure.snd_compProd] at h
  rw [Measure.snd_compProd,globalKernel,←Measure.comp_assoc,h]

end RoughRegime.PoissonMeasure.AdmissiblePhaseExperiment
