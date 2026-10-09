module

public import RoughRegime.AdmissiblePhaseComparison
public import RoughRegime.ProductDensityFintype


@[expose] public section
/-! The original physical comparison for heterogeneous independent finite
phase pairs; each pair may have its own actual latent prior and affine field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
variable {I H X Z : Type*} [Fintype I] [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : Measure Z} [IsProbabilityMeasure π]
    {lo hi barp C0 : ℝ}

 def productPoissonMixture (A : I→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (ν : I→Measure H) [∀i,IsProbabilityMeasure (ν i)] (S : SpatialAffine.Scores π)
    (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : I=>referenceProcess (μ.prod π) rate)) :=
  LowerMeasure.fintypeProductDensityLaw (fun i=>
    (A i).poissonMixture (ν i) S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate positive)

 theorem product_physical_comparison_coefficient
    (A : I→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (ν : I→Measure H) [∀i,IsProbabilityMeasure (ν i)] (S : SpatialAffine.Scores π)
    (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (M : ℕ) (rate : ℝ≥0) (Λ CG CE R : ℝ)
    (hΛ : 0 ≤ Λ) (hrate : (rate:ℝ) ≤ 1) (hscale : (rate:ℝ) ≤ 2*barp*Λ)
    (hCG : 0 ≤ CG) (hR : 0<R)
    (hΓ : ∀i j,M ≤ j→(A i).field.gammaNorm (ν i) ((2:ENNReal)•μ) Au Av M j ≤
      CG^(j+1)*Au^2*Av^2*Real.exp (CE*M)*LatticePriors.gammaSpatialFactor R M j) :
    let Cstar:=comparisonStar lo hi barp C0 S.C
    1 ≤ Cstar ∧ GeneralTesting.hellingerSquared
      (productPoissonMixture A ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate true)
      (productPoissonMixture A ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate false) ≤
        (Fintype.card I:ℝ)*LatticePriors.canonicalPoissonMajorant Cstar CG CE R Λ Au Av M := by
  refine ⟨comparisonStar_ge_one hlo hbarp S.C,?_⟩
  apply (LowerMeasure.hellinger_fintypeProduct_le
    (fun i=>(A i).poissonMixture (ν i) S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate true)
    (fun i=>(A i).poissonMixture (ν i) S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate false)).trans
  have hs:=Finset.sum_le_sum (s := (Finset.univ:Finset I)) (fun i _=>
    (A i).physical_comparison_coefficient (ν i) S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall
      M rate Λ CG CE R hΛ hrate hscale hCG hR (hΓ i))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs

end RoughRegime.PoissonMeasure.AdmissiblePhasePair
