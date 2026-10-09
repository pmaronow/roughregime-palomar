module

public import RoughRegime.CanonicalPoissonMixtures
public import RoughRegime.SourceLatticePriors
public import RoughRegime.PoissonPhysicalComparison
public import RoughRegime.GammaSeriesBound


@[expose] public section
/-! Uniform physical marked-Poisson comparison for the literal canonical
source experiment, under its actual native priors. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace RoughRegime.LatticePriors
open RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 theorem product_hellinger_one {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    (L R : GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared (LowerMeasure.productDensityLaw (fun _ : Fin 1=>L))
      (LowerMeasure.productDensityLaw (fun _ : Fin 1=>R)) = GeneralTesting.hellingerSquared L R := by
  rw [LowerMeasure.hellinger_integral_eq,LowerMeasure.densityAffinity_product,Fin.prod_univ_one,
    LowerMeasure.hellinger_integral_eq]

def canonicalComparisonConstant (lo hi scoreBound : ℝ) : ℝ :=
  physicalComparisonConstant
    (comparisonConstant ((1+2*hi)/lo) (max 1 scoreBound) (3*lo/(4*hi)) 1)
    (1/lo^2) (2*hi)

namespace CanonicalFrame
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

 theorem canonicalPairMixture_physical_comparison {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ι→ℤ)) [IsProbabilityMeasure ν]
    (π : ProbabilityMeasure Z) (scores : SpatialAffine.Scores (π:Measure Z))
    (hsmall : (F.Au+F.Av)/F.rminus*scores.C≤1/4) (hAu1 : F.Au≤1) (hAv1 : F.Av≤1)
    (rate : ℝ≥0) (Λ : ℝ) (hΛ : 0 ≤ Λ) (hrate : (rate:ℝ)≤1) (hrscale : (rate:ℝ)≤2*F.rplus*Λ) :
    let Cstar := canonicalComparisonConstant F.rminus F.rplus scores.C
    1≤Cstar ∧ GeneralTesting.hellingerSquared
      (F.canonicalPairMixture ν π scores hsmall rate true)
      (F.canonicalPairMixture ν π scores hsmall rate false) ≤
      Cstar*Λ^2*(∑' j, if F.M≤j then (Cstar*Λ)^j/j.factorial*
        F.canonicalPhaseField.gammaNorm ν
          ((2:ENNReal) • ((Model.cubeVolume (D+1)).prod uniformBlockLabel)) F.Au F.Av F.M j else 0)+
      Cstar*Λ^4*F.Au^2*F.Av^2*(F.Au^2+F.Av^2)^2*((Cstar*Λ)^F.M/F.M.factorial) := by
  let μ := (Model.cubeVolume (D+1)).prod uniformBlockLabel
  let Craw := 1+2*F.rplus
  let C := Craw/F.rminus
  let a := 1/F.pairBarDensity
  let A := 1/F.rminus^2
  let T := 2*F.rplus
  let c := 3*F.rminus/(4*F.rplus)
  have hlo := F.rminus_pos
  have hhi := F.rminus_pos.trans F.interval
  have hCr : 0 ≤ Craw := by dsimp [Craw]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ha0 : 0 ≤ a := by dsimp [a]; exact div_nonneg (by norm_num) F.pairBarDensity_positive.le
  have hdiv : a≤1/F.rminus := one_div_le_one_div_of_le F.rminus_pos F.pairBarDensity_bounds.1
  have ha : a^2≤A := by
    calc
      _ ≤ (1/F.rminus)^2 := pow_le_pow_left₀ ha0 hdiv 2
      _ = A := by dsimp [A]; rw [div_pow,one_pow]
  have hscale : |a| * Craw ≤ C := by
    rw [abs_of_nonneg ha0]
    exact (mul_le_mul_of_nonneg_right hdiv hCr).trans_eq (by dsimp [C]; ring)
  have hh := AffinePhaseField.physical_pair_comparison (fun _ : Fin 1=>ν) μ (π:Measure Z)
    (fun _ : Fin 1=>F.canonicalPhaseField) (fun _=>F.canonicalPhaseField_measurable)
    F.Au F.Av Craw C (max 1 scores.C) a A T Λ F.Au_nonneg hAu1 F.Av_nonneg hAv1
    hCr hC (zero_le_one.trans (le_max_left _ _)) hA ha hT hΛ
    (fun _=>F.canonicalPhaseField_bounded) hscale (F.phaseScores π scores)
    (F.phaseScores_measurable π scores) (F.phaseScores_bound π scores)
    (fun _ q=>F.canonicalPhaseField_markedFactor_integral_zero π scores q)
    c hc (fun _ q y=>F.canonicalLikelihood_lower π scores hsmall q y) F.M rate 1 hrate hrscale
  dsimp only at hh
  rw [product_hellinger_one] at hh
  change 1≤canonicalComparisonConstant F.rminus F.rplus scores.C ∧
    GeneralTesting.hellingerSquared (F.canonicalPairMixture ν π scores hsmall rate true)
      (F.canonicalPairMixture ν π scores hsmall rate false) ≤ _ at hh
  simpa only [AffinePhaseField.physicalGammaMaximum,finiteMaximum,Finset.sup'_const,
    Nat.cast_one,mul_one,canonicalComparisonConstant,C,Craw,c,A,T,μ] using hh

end CanonicalFrame
theorem canonicalComparisonConstant_ge_one (lo hi scoreBound : ℝ) (hlo : 0<lo) (hhi : 0<hi) :
    1≤canonicalComparisonConstant lo hi scoreBound := by
  let K := comparisonConstant ((1+2*hi)/lo) (max 1 scoreBound) (3*lo/(4*hi)) 1
  have hc : 0<3*lo/(4*hi) := by positivity
  have hK : 0 ≤ K := zero_le_one.trans (comparisonConstant_bounds _ _ _ _ hc).1
  change 1≤physicalComparisonConstant K (1/lo^2) (2*hi)
  unfold physicalComparisonConstant
  have hh : 0 ≤ K*(2*hi)+K*(1/lo^2)*(2*hi)+K*(2*hi)^2*(1/lo^2)^2+K*(2*hi)^4 := by positivity
  linarith

def canonicalPoissonMajorant (Cstar CG CE R Λ Au Av : ℝ) (M : ℕ) : ℝ :=
  Cstar*Λ^2*(CG*Au^2*Av^2*Real.exp (CE*M)*R^(1-(M:ℝ))*
    ((CG*Cstar*Λ)^M/M.factorial)*Real.exp (CG*Cstar*Λ*R^Real.sqrt M))+
  Cstar*Λ^4*Au^2*Av^2*(Au^2+Av^2)^2*((Cstar*Λ)^M/M.factorial)

namespace SourceLatticeSetup
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)

 theorem canonical_physical_gammaNorm_eq (N J M j : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (heU1 : epsilonU ≤ 1) (heV1 : epsilonV ≤ 1) :
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    F.canonicalPhaseField.gammaNorm (S.coefficientPrior J M hM hscale)
      ((2:ENNReal) • ((Model.cubeVolume (D+1)).prod uniformBlockLabel)) F.Au F.Av M j =
      S.gammaL2Squared J M j delta F.Au F.Av hM hscale := by
  obtain ⟨hAu1,hAv1⟩:=S.frame_amplitudes_le_one N J M hN epsilonU epsilonV delta heU heV hd hmargin heU1 heV1
  dsimp only
  rw [((S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin).canonicalPhaseField).gammaNorm_two_smul
    (S.coefficientPrior J M hM hscale) ((Model.cubeVolume (D+1)).prod uniformBlockLabel)
    (S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin).Au
    (S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin).Av M j]
  exact S.canonical_gammaNorm_eq N J M j hN epsilonU epsilonV delta heU heV hd hmargin hM hscale hAu1 hAv1

 theorem uniform_canonical_pair_comparison (C CG CE : ℝ) (H : SourceLatticeConclusions S C CG CE)
    {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z) (scores : SpatialAffine.Scores (π:Measure Z)) :
    ∃ Cstar : ℝ, 1≤Cstar ∧
      ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
        (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
        (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) (hM : 0 < M)
        (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M),
      epsilonU ≤ 1 → epsilonV ≤ 1 →
      let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      ∀ (hsmall : (F.Au+F.Av)/F.rminus*scores.C≤1/4) (rate : ℝ≥0) (Λ : ℝ),
      0 ≤ Λ → (rate:ℝ)≤1 → (rate:ℝ)≤2*rplus*Λ →
      GeneralTesting.hellingerSquared
        (F.canonicalPairMixture (S.coefficientPrior J M hM hscale) π scores hsmall rate true)
        (F.canonicalPairMixture (S.coefficientPrior J M hM hscale) π scores hsmall rate false) ≤
        canonicalPoissonMajorant Cstar CG CE ((2:ℝ)^((D+1)*J)) Λ F.Au F.Av M := by
  let Cstar := canonicalComparisonConstant rminus rplus scores.C
  have hstar : 1≤Cstar := canonicalComparisonConstant_ge_one _ _ _ S.lower_pos (S.lower_pos.trans S.interval)
  refine ⟨Cstar,hstar,?_⟩
  intro N J M hN epsilonU epsilonV delta heU heV hd hmargin hM hscale heU1 heV1
  dsimp only
  let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
  intro hsmall rate Λ hΛ hrate hrscale
  obtain ⟨hAu1,hAv1⟩:=S.frame_amplitudes_le_one N J M hN epsilonU epsilonV delta heU heV hd hmargin heU1 heV1
  have hhis : F.rplus=rplus := rfl
  have hrscaleF : (rate:ℝ)≤2*F.rplus*Λ := by simpa only [hhis] using hrscale
  have hp := F.canonicalPairMixture_physical_comparison (S.coefficientPrior J M hM hscale)
    π scores hsmall hAu1 hAv1 rate Λ hΛ hrate hrscaleF
  have hconstant : canonicalComparisonConstant F.rminus F.rplus scores.C=Cstar := rfl
  have hms : F.M=M := rfl
  rw [hconstant,hms] at hp
  have hΓ (j : ℕ) : 0 ≤ S.gammaL2Squared J M j delta F.Au F.Av hM hscale :=
    integral_nonneg fun _=>sq_nonneg _
  have hb (j : ℕ) (hj : M≤j) : S.gammaL2Squared J M j delta F.Au F.Av hM hscale ≤
      CG^(j+1)*(F.Au^2*F.Av^2)*Real.exp (CE*M)*gammaSpatialFactor ((2:ℝ)^((D+1)*J)) M j := by
    have he := H.coefficients J M j delta F.Au F.Av hM hscale hd hmargin
    rw [ite_eq_left hj] at he
    simpa only [mul_assoc] using he
  have hs := spatial_gamma_series_bound (fun j=>S.gammaL2Squared J M j delta F.Au F.Av hM hscale)
    hΓ CG (F.Au^2*F.Av^2) CE ((2:ℝ)^((D+1)*J)) (Cstar*Λ)
    (zero_le_one.trans H.gamma_constant_ge_one) (by positivity) (by positivity)
    (mul_nonneg (zero_le_one.trans hstar) hΛ) M hb
  have heq (j : ℕ) : F.canonicalPhaseField.gammaNorm (S.coefficientPrior J M hM hscale)
      ((2:ENNReal) • ((Model.cubeVolume (D+1)).prod uniformBlockLabel)) F.Au F.Av M j =
      S.gammaL2Squared J M j delta F.Au F.Av hM hscale :=
    S.canonical_physical_gammaNorm_eq N J M j hN epsilonU epsilonV delta
      heU heV hd hmargin hM hscale heU1 heV1
  dsimp only at hp
  simp_rw [heq] at hp
  have hsum := mul_le_mul_of_nonneg_left hs.2 (mul_nonneg (zero_le_one.trans hstar) (sq_nonneg Λ))
  exact hp.2.trans (by
    unfold canonicalPoissonMajorant
    convert add_le_add_right hsum
      (Cstar*Λ^4*F.Au^2*F.Av^2*(F.Au^2+F.Av^2)^2*((Cstar*Λ)^M/M.factorial)) using 1 <;>
      dsimp only [F] <;> first | rfl | ring)

end SourceLatticeSetup
end RoughRegime.LatticePriors
