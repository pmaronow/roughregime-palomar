module

public import RoughRegime.CanonicalPhaseField
public import RoughRegime.SourcePriorReindex
public import RoughRegime.PoissonKernelMixtures
public import RoughRegime.HeterogeneousKernels


@[expose] public section
/-! The actual canonical native-state prior observation marginals are the
marked-Poisson density mixtures used in the comparison theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RoughRegime.GeneralTesting.DensityLaw

theorem ext_density {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : RoughRegime.GeneralTesting.DensityLaw μ) (h : L.density=R.density) : L=R := by
  cases L
  cases R
  cases h
  rfl

end RoughRegime.GeneralTesting.DensityLaw

namespace RoughRegime.LatticePriors.CanonicalFrame
open RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

def pairLikelihoodBound {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)
    (S : SpatialAffine.Scores (π:Measure Z)) : ℝ :=
  (F.rplus+(F.Au+F.Av)*S.C)/F.pairBarDensity

theorem pairLikelihoodBound_nonnegative {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z)) :
    0≤F.pairLikelihoodBound π S := by
  have hr := F.rminus_pos.trans F.interval
  unfold pairLikelihoodBound
  exact div_nonneg (add_nonneg hr.le (mul_nonneg
    (add_nonneg F.Au_nonneg F.Av_nonneg) S.nonnegativeC)) F.pairBarDensity_positive.le

def canonicalPairMixture {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) (positive : Bool) :
    GeneralTesting.DensityLaw (referenceProcess (F.localPairBase π) rate) :=
  markedMixtureLaw (F.localPairBase π) (phaseBase ν)
    (phasePrior ν F.M (if positive then 1 else -1) (by cases positive <;> norm_num))
    (F.canonicalLikelihood π S) (F.canonicalLikelihood_measurable π S)
    2 (F.pairLikelihoodBound π S) (by norm_num) (F.pairLikelihoodBound_nonnegative π S)
    (fun q => (phaseDensity_bound F.M _ (by cases positive <;> norm_num) q).2)
    (F.canonicalLikelihood_bound π S) (F.canonicalLikelihood_nonnegative π S hsmall)
    (F.canonicalLikelihood_integral π S) rate

theorem canonicalPoissonKernel_marginal {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) (positive : Bool) :
    ((phasePrior ν F.M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure
      ⊗ₘ F.canonicalPoissonKernel π S rate).snd =
      (F.canonicalPairMixture ν π S hsmall rate positive).measure := by
  exact observationKernel_marginal (F.localPairBase π) (phaseBase ν)
    (phasePrior ν F.M (if positive then 1 else -1) (by cases positive <;> norm_num))
    (F.canonicalLikelihood π S) (F.canonicalLikelihood_measurable π S)
    2 (F.pairLikelihoodBound π S) (by norm_num) (F.pairLikelihoodBound_nonnegative π S)
    (fun q => (phaseDensity_bound F.M _ (by cases positive <;> norm_num) q).2)
    (F.canonicalLikelihood_bound π S) (F.canonicalLikelihood_nonnegative π S hsmall)
    (F.canonicalLikelihood_integral π S) rate

theorem physicalPairKernel_comp_blockPrior {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) (positive : Bool) :
    F.physicalPairKernel π S hsmall rate ∘ₘ blockPrior ν F.M positive =
      F.canonicalPoissonKernel π S rate ∘ₘ
        (phasePrior ν F.M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure := by
  unfold blockPrior
  rw [← phasePrior_assoc ν F.M positive]
  ext s hs
  rw [Measure.bind_apply hs (F.physicalPairKernel π S hsmall rate).aemeasurable,
    Measure.bind_apply hs (F.canonicalPoissonKernel π S rate).aemeasurable]
  rw [lintegral_map ((F.physicalPairKernel π S hsmall rate).measurable_coe hs)
    (MeasurableEquiv.prodAssoc.measurable)]
  apply lintegral_congr
  intro q
  change (F.canonicalPoissonKernel π S rate (F.phaseStateEquiv.symm (F.phaseStateEquiv q))) s = _
  rw [MeasurableEquiv.symm_apply_apply]

/-- Exact native-prior marginal; no assumed mixture or posterior law. -/
theorem physicalPairKernel_marginal {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*S.C≤1/4) (rate : ℝ≥0) (positive : Bool) :
    (blockPrior ν F.M positive ⊗ₘ F.physicalPairKernel π S hsmall rate).snd =
      (F.canonicalPairMixture ν π S hsmall rate positive).measure := by
  rw [Measure.snd_compProd,F.physicalPairKernel_comp_blockPrior ν π S hsmall rate positive]
  haveI := F.canonicalPoissonKernel_isMarkov π S hsmall rate
  rw [← Measure.snd_compProd]
  exact F.canonicalPoissonKernel_marginal ν π S hsmall rate positive

end RoughRegime.LatticePriors.CanonicalFrame
