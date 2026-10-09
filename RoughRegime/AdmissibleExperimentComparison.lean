module

public import RoughRegime.AdmissibleExperimentKernel
public import RoughRegime.AdmissibleProductPoisson


@[expose] public section
/-! The full genuine product-prior observation comparison for arbitrary
admissible phase experiments, with their actual physical pair Poisson rates. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace RoughRegime.PoissonMeasure.AdmissiblePhaseExperiment
set_option backward.isDefEq.respectTransparency false
variable {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Y] {p : ℕ} [NeZero p]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : ProbabilityMeasure Z}
    (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)

 def productMixture (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1)
    (ν : Fin p→Measure H) [∀i,IsProbabilityMeasure (ν i)] (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin p=>referenceProcess (μ.prod (π:Measure Z))
      (rate*(E.pairMass/(p:ℝ≥0))))) :=
  LowerMeasure.fintypeProductDensityLaw (μ := referenceProcess (μ.prod (π:Measure Z))
    (rate*(E.pairMass/(p:ℝ≥0)))) (fun i=>E.pairMixture hAu1 hAv1 ν M rate positive i)

 theorem productMixture_marginal (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1)
    (ν : Fin p→Measure H) [∀i,IsProbabilityMeasure (ν i)] (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    (parameterPrior ν M positive ⊗ₘ E.productPhaseKernel hAu1 hAv1 rate).snd=
      (E.productMixture hAu1 hAv1 ν M rate positive).measure := by
  rw [productMixture,LowerMeasure.fintypeProductDensityLaw_measure]
  exact E.productPhaseKernel_marginal hAu1 hAv1 ν M rate positive

 theorem physical_mixture_hellinger_le (hAu1 : E.Au ≤ 1) (hAv1 : E.Av ≤ 1)
    (ν : Fin p→Measure H) [∀i,IsProbabilityMeasure (ν i)] (M : ℕ) (rate : ℝ≥0)
    (Λ CG CE R : ℝ) (hΛ : 0 ≤ Λ)
    (hrate : ((rate*(E.pairMass/(p:ℝ≥0)):ℝ≥0):ℝ) ≤ 1)
    (hscale : ((rate*(E.pairMass/(p:ℝ≥0)):ℝ≥0):ℝ) ≤ 2*E.barp*Λ)
    (hCG : 0 ≤ CG) (hR : 0<R)
    (hΓ : ∀i j,M ≤ j→(E.pairs i).field.gammaNorm (ν i) ((2:ENNReal)•μ) E.Au E.Av M j ≤
      CG^(j+1)*E.Au^2*E.Av^2*Real.exp (CE*M)*LatticePriors.gammaSpatialFactor R M j) :
    let Cstar:=AdmissiblePhasePair.comparisonStar E.lo E.hi E.barp E.C0 E.scores.C
    1 ≤ Cstar ∧ GeneralTesting.hellingerSquared
      (E.productMixture hAu1 hAv1 ν M rate true) (E.productMixture hAu1 hAv1 ν M rate false) ≤
      (p:ℝ)*LatticePriors.canonicalPoissonMajorant Cstar CG CE R Λ E.Au E.Av M := by
  refine ⟨AdmissiblePhasePair.comparisonStar_ge_one E.lo_pos E.barp_pos E.scores.C,?_⟩
  apply (LowerMeasure.hellinger_fintypeProduct_le
    (μ := referenceProcess (μ.prod (π:Measure Z)) (rate*(E.pairMass/(p:ℝ≥0))))
    (fun i=>E.pairMixture hAu1 hAv1 ν M rate true i) (fun i=>E.pairMixture hAu1 hAv1 ν M rate false i)).trans
  have hs:=Finset.sum_le_sum (s := (Finset.univ:Finset (Fin p))) (fun i _=>
    (E.pairs i).physical_comparison_coefficient (ν i) E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
      E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small M
      (rate*E.weights (some i)) Λ CG CE R hΛ
      (by simpa only [E.pair_rate i rate] using hrate)
      (by simpa only [E.pair_rate i rate] using hscale) hCG hR (hΓ i))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,pairMixture] using hs

end RoughRegime.PoissonMeasure.AdmissiblePhaseExperiment
