module

public import RoughRegime.AdmissiblePhaseLikelihood
public import RoughRegime.CanonicalPoissonComparison


@[expose] public section
/-! The original abstract affine-phase assumptions yield a genuine common
marked-Poisson experiment and its physical-coefficient Hellinger comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
set_option backward.isDefEq.respectTransparency false
variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : Measure Z} [IsProbabilityMeasure π]
    {lo hi barp C0 : ℝ}

 def normalizedBound (lo hi barp C0 : ℝ) : ℝ:=rawBound lo hi barp C0/barp

 theorem normalizedBound_nonneg (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0) :
    0 ≤ normalizedBound lo hi barp C0 := div_nonneg (rawBound_nonneg hhi hbarp.le hC0) hbarp.le

 theorem normalized_field_bounded (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0) :
    (A.field.scale (1/barp)).Bounded (normalizedBound lo hi barp C0) := by
  have hb:=A.field.scale_bounded (1/barp) (rawBound lo hi barp C0) (A.field_bounded hlo hhi hbarp.le hC0)
  have he:|1/barp| *rawBound lo hi barp C0=normalizedBound lo hi barp C0 := by
    rw [abs_of_pos (one_div_pos.mpr hbarp)]
    unfold normalizedBound
    ring
  rw [he] at hb
  exact hb

 def likelihood (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (Au Av : ℝ) : PhaseParameter H→X×Z→ℝ :=
    fun q y=>1+(A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q y

 theorem likelihood_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (Au Av : ℝ) : Measurable (Function.uncurry (A.likelihood S Au Av)) :=
    ((A.field.scale (1/barp)).markedFactor_measurable (A.field.scale_isMeasurable A.measurable _)
      Au Av (phaseScores S) (phaseScores_measurable S)).const_add 1

 theorem likelihood_abs_bound (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (q : PhaseParameter H) (y : X×Z) :
    |A.likelihood S Au Av q y| ≤ 1+9*normalizedBound lo hi barp C0*(max 1 S.C) := by
  have hb:=(A.field.scale (1/barp)).markedFactor_bound Au Av (normalizedBound lo hi barp C0)
    (max 1 S.C) hAu hAu1 hAv hAv1 (normalizedBound_nonneg hhi hbarp hC0)
    (zero_le_one.trans (le_max_left _ _)) (A.normalized_field_bounded hlo hhi hbarp hC0)
    (phaseScores S) (phaseScores_bound S) q y
  exact (abs_add_le 1 _).trans (by rw [abs_one]; linarith)

 theorem likelihood_integral (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) :
    ∀q,(∫y,A.likelihood S Au Av q y ∂μ.prod π)=1 :=
  (A.field.scale (1/barp)).pointDensity_mean μ π (A.field.scale_isMeasurable A.measurable _)
    Au Av (normalizedBound lo hi barp C0) (max 1 S.C) hAu hAu1 hAv hAv1
    (normalizedBound_nonneg hhi hbarp hC0) (zero_le_one.trans (le_max_left _ _))
    (A.normalized_field_bounded hlo hhi hbarp hC0) (phaseScores S) (phaseScores_measurable S)
    (phaseScores_bound S) (A.markedFactor_integral_zero S hlo hhi hbarp hC0 Au Av hAu hAv hsmall)

 def poissonMixture (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (ν : Measure H) [IsProbabilityMeasure ν]
    (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    GeneralTesting.DensityLaw (referenceProcess (μ.prod π) rate) :=
  (A.field.scale (1/barp)).poissonLaw ν μ π (A.field.scale_isMeasurable A.measurable _)
    Au Av (normalizedBound lo hi barp C0) (max 1 S.C) hAu hAu1 hAv hAv1
    (normalizedBound_nonneg hhi hbarp hC0) (zero_le_one.trans (le_max_left _ _))
    (A.normalized_field_bounded hlo hhi hbarp hC0) (phaseScores S) (phaseScores_measurable S)
    (phaseScores_bound S) (A.markedFactor_integral_zero S hlo hhi hbarp hC0 Au Av hAu hAv hsmall)
    (lo/(2*barp)) (by positivity) (A.likelihood_lower S hlo hhi hbarp hC0 Au Av hAu hAv hsmall) M rate positive

 def poissonKernel (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (Au Av : ℝ) (rate : ℝ≥0) : Kernel (PhaseParameter H) (PointConfiguration (X×Z)) :=
  observationKernel (μ.prod π) (A.likelihood S Au Av) (A.likelihood_measurable S Au Av) rate

 theorem poissonKernel_markov (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (rate : ℝ≥0) : IsMarkovKernel (A.poissonKernel S Au Av rate) :=
  observationKernel_isMarkov (μ.prod π) (A.likelihood S Au Av) (A.likelihood_measurable S Au Av)
    (1+9*normalizedBound lo hi barp C0*(max 1 S.C))
    (A.likelihood_abs_bound S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1)
    (fun q y=> (by positivity : (0:ℝ) ≤ lo/(2*barp)).trans
      (A.likelihood_lower S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q y))
    (A.likelihood_integral S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall) rate

 theorem poissonKernel_marginal (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (ν : Measure H) [IsProbabilityMeasure ν] (S : SpatialAffine.Scores π)
    (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    ((phasePrior ν M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure
      ⊗ₘ A.poissonKernel S Au Av rate).snd=
        (A.poissonMixture ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate positive).measure := by
  exact observationKernel_marginal (μ.prod π) (phaseBase ν)
    (phasePrior ν M (if positive then 1 else -1) (by cases positive <;> norm_num))
    (A.likelihood S Au Av) (A.likelihood_measurable S Au Av) 2
    (1+9*normalizedBound lo hi barp C0*(max 1 S.C)) (by norm_num)
    (by have:=normalizedBound_nonneg (lo:=lo) hhi hbarp hC0; have:=zero_le_one.trans (le_max_left 1 S.C); positivity)
    (fun q=>(phaseDensity_bound M _ (by cases positive <;> norm_num) q).2)
    (A.likelihood_abs_bound S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1)
    (fun q y=> (by positivity : (0:ℝ) ≤ lo/(2*barp)).trans
      (A.likelihood_lower S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q y))
    (A.likelihood_integral S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall) rate

 theorem poissonKernel_apply (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (rate : ℝ≥0) (q : PhaseParameter H) :
    A.poissonKernel S Au Av rate q=Measure.sum (fun n=>
      ENNReal.ofReal (Lower.poissonMass rate n) •
        ((LowerMeasure.iidDensityLaw (A.markLaw S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q) n).measure).map
          (@Sigma.mk ℕ (fun k=>Fin k→X×Z) n)) := by
  let Cψ:=1+9*normalizedBound lo hi barp C0*(max 1 S.C)
  have hb:=A.likelihood_abs_bound S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1
  have hzero : ∀q y,0 ≤ A.likelihood S Au Av q y := fun q y=>
    (by positivity : (0:ℝ) ≤ lo/(2*barp)).trans
      (A.likelihood_lower S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q y)
  have hmean:=A.likelihood_integral S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall
  have hpoint (q:PhaseParameter H) : pointLaw (μ.prod π) (A.likelihood S Au Av)
      (A.likelihood_measurable S Au Av) Cψ hb hzero hmean q=
      A.markLaw S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q := by
    apply GeneralTesting.DensityLaw.ext_density
    funext y
    exact (A.markLaw_density_eq S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q y).symm
  rw [poissonKernel,observationKernel_apply (μ.prod π) (A.likelihood S Au Av)
    (A.likelihood_measurable S Au Av) Cψ hb hzero hmean]
  simp_rw [hpoint]

 def comparisonStar (lo hi barp C0 scoreBound : ℝ) : ℝ :=
  physicalComparisonConstant (comparisonConstant (normalizedBound lo hi barp C0) (max 1 scoreBound)
    (lo/(2*barp)) 1) (1/barp^2) (2*barp)

 theorem physical_comparison (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (ν : Measure H) [IsProbabilityMeasure ν] (S : SpatialAffine.Scores π)
    (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (M : ℕ) (rate : ℝ≥0) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hrate : (rate:ℝ) ≤ 1) (hscale : (rate:ℝ) ≤ 2*barp*Λ) :
    let Cstar:=comparisonStar lo hi barp C0 S.C
    1 ≤ Cstar ∧ GeneralTesting.hellingerSquared
      (A.poissonMixture ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate true)
      (A.poissonMixture ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate false) ≤ 
      Cstar*Λ^2*(∑'j,if M ≤ j then (Cstar*Λ)^j/j.factorial*
        A.field.gammaNorm ν ((2:ENNReal)•μ) Au Av M j else 0)+
      Cstar*Λ^4*Au^2*Av^2*(Au^2+Av^2)^2*((Cstar*Λ)^M/M.factorial) := by
  have hCr:=rawBound_nonneg (lo:=lo) hhi hbarp.le hC0
  have hC:=normalizedBound_nonneg (lo:=lo) hhi hbarp hC0
  have ha : (1/barp)^2 ≤ 1/barp^2 := by rw [div_pow,one_pow]
  have hnorm : |1/barp| *rawBound lo hi barp C0 ≤ normalizedBound lo hi barp C0 := by
    rw [abs_of_pos (one_div_pos.mpr hbarp)]
    unfold normalizedBound
    exact le_of_eq (by ring)
  have he:=AffinePhaseField.physical_pair_comparison (fun _ : Fin 1=>ν) μ π
    (fun _=>A.field) (fun _=>A.measurable) Au Av (rawBound lo hi barp C0)
    (normalizedBound lo hi barp C0) (max 1 S.C) (1/barp) (1/barp^2) (2*barp) Λ
    hAu hAu1 hAv hAv1 hCr hC (zero_le_one.trans (le_max_left _ _)) (by positivity) ha
    (by positivity) hΛ (fun _=>A.field_bounded hlo hhi hbarp.le hC0) hnorm
    (phaseScores S) (phaseScores_measurable S) (phaseScores_bound S)
    (fun _=>A.markedFactor_integral_zero S hlo hhi hbarp hC0 Au Av hAu hAv hsmall)
    (lo/(2*barp)) (by positivity)
    (fun _=>A.likelihood_lower S hlo hhi hbarp hC0 Au Av hAu hAv hsmall) M rate 1 hrate hscale
  dsimp only at he
  rw [LatticePriors.product_hellinger_one] at he
  change 1 ≤ comparisonStar lo hi barp C0 S.C ∧ GeneralTesting.hellingerSquared
    (A.poissonMixture ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate true)
    (A.poissonMixture ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate false) ≤ _ at he
  simpa only [AffinePhaseField.physicalGammaMaximum,finiteMaximum,Finset.sup'_const,
    Nat.cast_one,mul_one,comparisonStar] using he

 theorem comparisonStar_ge_one (hlo : 0<lo) (hbarp : 0<barp) (scoreBound : ℝ) :
    1 ≤ comparisonStar lo hi barp C0 scoreBound := by
  have hK : 0 ≤ comparisonConstant (normalizedBound lo hi barp C0) (max 1 scoreBound)
      (lo/(2*barp)) 1 := zero_le_one.trans (comparisonConstant_bounds _ _ _ _ (by positivity)).1
  unfold comparisonStar physicalComparisonConstant
  have hs : 0 ≤ comparisonConstant (normalizedBound lo hi barp C0) (max 1 scoreBound)
    (lo/(2*barp)) 1*(2*barp) + comparisonConstant (normalizedBound lo hi barp C0) (max 1 scoreBound)
    (lo/(2*barp)) 1*(1/barp^2)*(2*barp) + comparisonConstant (normalizedBound lo hi barp C0) (max 1 scoreBound)
    (lo/(2*barp)) 1*(2*barp)^2*(1/barp^2)^2 + comparisonConstant (normalizedBound lo hi barp C0) (max 1 scoreBound)
    (lo/(2*barp)) 1*(2*barp)^4 := by positivity
  linarith

/-- An original physical Gamma estimate yields the explicit factorial and
exponential two-term majorant for the actual phase-prior mixture laws. -/
 theorem physical_comparison_coefficient (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (ν : Measure H) [IsProbabilityMeasure ν] (S : SpatialAffine.Scores π)
    (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hsmall : C0*(Au+Av)*S.C ≤ 1/4) (M : ℕ) (rate : ℝ≥0) (Λ CG CE R : ℝ)
    (hΛ : 0 ≤ Λ) (hrate : (rate:ℝ) ≤ 1) (hscale : (rate:ℝ) ≤ 2*barp*Λ)
    (hCG : 0 ≤ CG) (hR : 0<R)
    (hΓ : ∀j,M ≤ j→A.field.gammaNorm ν ((2:ENNReal)•μ) Au Av M j ≤
      CG^(j+1)*Au^2*Av^2*Real.exp (CE*M)*LatticePriors.gammaSpatialFactor R M j) :
    let Cstar:=comparisonStar lo hi barp C0 S.C
    GeneralTesting.hellingerSquared
      (A.poissonMixture ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate true)
      (A.poissonMixture ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate false) ≤
      LatticePriors.canonicalPoissonMajorant Cstar CG CE R Λ Au Av M := by
  let Cstar:=comparisonStar lo hi barp C0 S.C
  have hp:=A.physical_comparison ν S hlo hhi hbarp hC0 Au Av hAu hAu1 hAv hAv1 hsmall M rate Λ hΛ hrate hscale
  have hCstar:0 ≤ Cstar:=zero_le_one.trans hp.1
  have hg (j:ℕ) : 0 ≤ A.field.gammaNorm ν ((2:ENNReal)•μ) Au Av M j :=
    A.field.gammaNorm_nonneg ν ((2:ENNReal)•μ) Au Av M j
  have hs:=spatial_gamma_series_bound (fun j=>A.field.gammaNorm ν ((2:ENNReal)•μ) Au Av M j) hg
    CG (Au^2*Av^2) CE R (Cstar*Λ) hCG (by positivity) hR (mul_nonneg hCstar hΛ) M (by
      intro j hj
      convert hΓ j hj using 1 <;> ring)
  have hsum:=mul_le_mul_of_nonneg_left hs.2 (mul_nonneg hCstar (sq_nonneg Λ))
  exact hp.2.trans (by
    unfold LatticePriors.canonicalPoissonMajorant
    convert add_le_add_right hsum
      (Cstar*Λ^4*Au^2*Av^2*(Au^2+Av^2)^2*((Cstar*Λ)^M/M.factorial)) using 1 <;>
        dsimp only [Cstar] <;> ring)

end RoughRegime.PoissonMeasure.AdmissiblePhasePair
