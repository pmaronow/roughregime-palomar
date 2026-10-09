module

public import RoughRegime.AdmissibleIntegrandGerm
public import RoughRegime.AdmissibleReductionNumerics
public import RoughRegime.AdmissibleComparisonUniform


@[expose] public section
/-! Proposition 12's full numerical and statistical reduction for arbitrary
resolution/multiplier sequences. The eventual sample threshold precedes
all latent spaces, pair counts, admissible fields, priors and model classes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace RoughRegime.PoissonMeasure.AdmissibleReduction
open ReductionScales AdmissiblePhasePair AdmissiblePhaseExperiment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

structure PhysicalScaleIdentification {H X Z Y : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    {p : ℕ} {μ : Measure X} {π : ProbabilityMeasure Z}
    (A : AbstractScaleParameters) (S : NaturalScaleChoice A) (n : ℕ)
    (C0 scoreBound : ℝ) (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π) : Prop where
  blocks : 2*p=S.B n
  lo : E.lo=A.lo
  hi : E.hi=A.hi
  C0 : E.C0=C0
  volume : E.v0=A.v0
  amplitudeU : E.Au=S.Au n
  amplitudeV : E.Av=S.Av n
  scores : E.scores.C=scoreBound

 theorem natural_admissible_reduction (A : AbstractScaleParameters) (S : NaturalScaleChoice A)
    (C0 scoreBound c2 : ℝ) (_hC0 : 1 ≤ C0) (hc2 : 0<c2)
    (hconstant : ∀barp∈Icc A.lo A.hi,comparisonStar A.lo A.hi barp C0 scoreBound ≤ A.Cstar)
    (Phi : ℝ×ℝ→ℝ) (hPhi4 : ContDiffAt ℝ 4 Phi 0)
    (hMixed : OddTaylor.mixedDerivative Phi 0≠0) :
    ∃ c1 : ℝ,0<c1 ∧
      (∀ q : ℝ,Tendsto (fun n : ℕ=>(S.B n:ℝ)/((n:ℝ)*(Real.log n)^q)) atTop atTop) ∧
      ∀ᶠ n : ℕ in atTop,n ≤ S.B n ∧
        (∃ k : ℕ,0<k ∧ Even k ∧ S.B n=k^A.d) ∧
        ∀ {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
          {p : ℕ} [NeZero p] (μ : Measure X) [IsProbabilityMeasure μ] (π : ProbabilityMeasure Z)
          (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)
          (_hId : PhysicalScaleIdentification A S n C0 scoreBound E)
          (nu : Fin p→Measure H) [∀ i,IsProbabilityMeasure (nu i)]
          (_hGamma : ∀i j,frequency n A.theta A.tau ≤ j→
            (E.pairs i).field.gammaNorm (nu i) ((2:ENNReal)•μ) E.Au E.Av (frequency n A.theta A.tau) j ≤
              A.CΓ^(j+1)*E.Au^2*E.Av^2*Real.exp (A.CE*frequency n A.theta A.tau)*
                LatticePriors.gammaSpatialFactor (S.R n) (frequency n A.theta A.tau) j)
          (_hBilinear : c2*S.gap n ≤
            |(∫ q,E.targetFunctional (fun x=>x.1*x.2) q ∂parameterPrior nu (frequency n A.theta A.tau) true)-
             (∫ q,E.targetFunctional (fun x=>x.1*x.2) q ∂parameterPrior nu (frequency n A.theta A.tau) false)|)
          (T : ProbabilityMeasure Y→ℝ) (Cls : Set (ProbabilityMeasure Y))
          (_hT : ∀q,T (E.observationProbability q)=E.targetFunctional Phi q)
          (_hCls : ∀q,E.observationProbability q∈Cls),
          (3/8:ℝ≥0∞) ≤ Model.minimaxTail n T Cls
            (c1*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ∧
          ENNReal.ofReal (c1/2*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ≤
            Model.minimaxRMSE n T Cls := by
  obtain ⟨epsilon,hepsilon,C,hC,B,hB,hfinite⟩ :=
    AdmissibleReductionTesting.local_admissible_testing_lower Phi hPhi4
  let clead:=|OddTaylor.mixedDerivative Phi 0| *c2
  have hclead : 0<clead:=mul_pos (abs_pos.mpr hMixed) hc2
  let c1:=clead/8*AbstractScaleChoice.gapConstant A
  have hc1 : 0<c1:=mul_pos (div_pos hclead (by norm_num)) (AbstractScaleChoice.gapConstant_pos A)
  have hTaylor:=S.gap_minus_Taylor_eventually_lower clead (A.v0*C*A.hi*C0^4) hclead
  have hVar:=S.prior_variance_eventually_budget (8*A.v0^2*(A.hi*B)^2)
    (clead/2) (1/1024) (div_pos hclead (by norm_num)) (by norm_num)
  have hHard:=S.poissonMajorant_tendsto_zero.eventually_le_const (by norm_num : (0:ℝ)<1/128)
  have hAu:=S.Au_tendsto_zero.eventually_le_const (by norm_num : (0:ℝ)<1)
  have hAv:=S.Av_tendsto_zero.eventually_le_const (by norm_num : (0:ℝ)<1)
  have hUl:=S.Au_tendsto_zero.const_mul C0
  have hVl:=S.Av_tendsto_zero.const_mul C0
  have hRl:=S.Lambda_tendsto_zero.const_mul (2*A.hi)
  simp only [mul_zero] at hUl hVl hRl
  have hUe:=hUl.eventually_le_const hepsilon
  have hVe:=hVl.eventually_le_const hepsilon
  have hRate:=hRl.eventually_le_const (by norm_num : (0:ℝ)<1)
  have hM:=(frequency_tendsto A.theta A.tau A.theta_pos A.hhalf A.tau_pos).comp tendsto_natCast_atTop_atTop
  refine ⟨c1,hc1,S.block_superlog,?_⟩
  filter_upwards [S.eventually_large_block,S.eventually_even_power,S.hRpos,
    S.amplitude_bounds,S.gap_eventually_lower,S.gap_eventually_pos,hTaylor,hVar,hHard,hAu,hAv,hUe,hVe,hRate,
    hM.eventually_ge_atTop 1,poisson_count_eventually_small,eventually_ge_atTop 3]
    with n hBn hBeven hRn hAmp hGapLower hGap hTaylorN hVarN hHardN hAuN hAvN hUeN hVeN hRateN hMN hcount hn
  refine ⟨hBn,hBeven,?_⟩
  intro H X Z Y _ _ _ _ p _ μ _ π E hId nu _ hGamma hBilinear T Cls hT hCls
  have hnpos : 0<n:=by omega
  have hR : 0<S.R n:=zero_lt_one.trans_le hRn
  have hMpos : 0<frequency n A.theta A.tau:=by
    have hmcast : (1:ℝ) ≤ (frequency n A.theta A.tau:ℝ):=hMN
    exact_mod_cast (zero_lt_one.trans_le hmcast)
  have hLambda:=S.Lambda_nonnegative n
  have hp : (0:ℝ)<p:=by exact_mod_cast NeZero.pos p
  let i0 : Fin p:=⟨0,NeZero.pos p⟩
  obtain ⟨latent⟩:=nonempty_of_isProbabilityMeasure (nu i0)
  have hbarp : E.barp∈Icc A.lo A.hi:=by
    have hb:=(E.pairs i0).mass_mem_density_bounds (latent,0) E.lo_pos E.hi_nonneg
    simpa only [hId.lo,hId.hi] using hb
  have hstar : comparisonStar E.lo E.hi E.barp E.C0 E.scores.C ≤ A.Cstar:=by
    rw [hId.lo,hId.hi,hId.C0,hId.scores]
    exact hconstant E.barp hbarp
  have hstar0 : 0 ≤ comparisonStar E.lo E.hi E.barp E.C0 E.scores.C:=
    zero_le_one.trans (comparisonStar_ge_one E.lo_pos E.barp_pos E.scores.C)
  have hFixed0 : 0 ≤ LatticePriors.canonicalPoissonMajorant A.Cstar A.CΓ A.CE
      (S.R n) (S.Lambda n) (S.Au n) (S.Av n) (frequency n A.theta A.tau):=by
    have hc:=zero_le_one.trans A.hCstar
    have hg:=zero_le_one.trans A.hCΓ
    unfold LatticePriors.canonicalPoissonMajorant
    positivity
  have hHardActual : (p:ℝ)*LatticePriors.canonicalPoissonMajorant
      (comparisonStar E.lo E.hi E.barp E.C0 E.scores.C) A.CΓ A.CE
      (S.R n) (S.Lambda n) E.Au E.Av (frequency n A.theta A.tau) ≤ 1/128:=by
    rw [hId.amplitudeU,hId.amplitudeV]
    calc
      _ ≤ (p:ℝ)*LatticePriors.canonicalPoissonMajorant A.Cstar A.CΓ A.CE
          (S.R n) (S.Lambda n) (S.Au n) (S.Av n) (frequency n A.theta A.tau):=
        mul_le_mul_of_nonneg_left (LatticePriors.canonicalPoissonMajorant_mono_constant _
          hstar0 hstar (zero_le_one.trans A.hCΓ) hLambda hR) hp.le
      _ ≤ (S.B n:ℝ)*LatticePriors.canonicalPoissonMajorant A.Cstar A.CΓ A.CE
          (S.R n) (S.Lambda n) (S.Au n) (S.Av n) (frequency n A.theta A.tau):=by
        apply mul_le_mul_of_nonneg_right _ hFixed0
        rw [←hId.blocks]
        norm_cast
        omega
      _ = S.poissonMajorant n:=S.block_canonicalPoissonMajorant_eq n hnpos hR hMpos
      _ ≤ _:=hHardN
  let rate:ℝ≥0:=2*(n:ℝ≥0)
  have hratepos : 0<rate:=by dsimp [rate]; positivity
  have hPhysicalRate : ((rate*E.pairMass/(p:ℝ≥0):ℝ≥0):ℝ)=2*E.barp*S.Lambda n:=by
    simp only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast]
    change (2*(n:ℝ))*(E.v0*E.barp)/(p:ℝ)=_
    rw [hId.volume,S.Lambda_eq,←hId.blocks]
    push_cast
    field_simp [hp.ne']
  have hRateActual : ((rate*E.pairMass/(p:ℝ≥0):ℝ≥0):ℝ) ≤ 1:=by
    rw [hPhysicalRate]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbarp.2 (by norm_num)) hLambda).trans hRateN
  have hScale : ((rate*E.pairMass/(p:ℝ≥0):ℝ≥0):ℝ) ≤ 2*E.barp*S.Lambda n:=hPhysicalRate.le
  let delta:=clead/8*S.gap n
  have hdelta : 0<delta:=mul_pos (div_pos hclead (by norm_num)) hGap
  have hTaylorActual : 4*delta ≤ |OddTaylor.mixedDerivative Phi 0| *c2*S.gap n-
      E.v0*C*E.hi*E.C0^4*E.Au*E.Av*(E.Au^2+E.Av^2):=by
    rw [hId.volume,hId.hi,hId.C0,hId.amplitudeU,hId.amplitudeV]
    convert hTaylorN using 1
    dsimp [delta,clead]
    ring
  have hVarActual : 8*E.v0^2*(E.hi*B)^2/(2*p:ℕ) ≤ (4*delta)^2/1024:=by
    rw [hId.volume,hId.hi,hId.blocks]
    convert hVarN using 1
    dsimp [delta]
    ring
  have hu : E.C0*E.Au ≤ epsilon:=by rw [hId.C0,hId.amplitudeU]; exact hUeN
  have hv : E.C0*E.Av ≤ epsilon:=by rw [hId.C0,hId.amplitudeV]; exact hVeN
  have htest:=hfinite μ π E nu (frequency n A.theta A.tau) A.CΓ A.CE (S.R n) (S.Lambda n) rate
    (hId.amplitudeU ▸ hAuN) (hId.amplitudeV ▸ hAvN) hu hv hLambda (zero_le_one.trans A.hCΓ) hR hratepos
    hRateActual hScale hGamma hHardActual c2 (S.gap n) delta hc2 hGap hdelta hBilinear
    hTaylorActual hVarActual T Cls hT hCls n hcount
  have hThreshold : c1*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau ≤ delta:=by
    have h:=mul_le_mul_of_nonneg_left hGapLower (div_pos hclead (by norm_num : (0:ℝ)<8)).le
    convert h using 1
    dsimp [c1,delta]
    ring
  refine ⟨htest.1.trans (Model.minimaxTail_antitone_threshold n T Cls hThreshold),?_⟩
  exact (ENNReal.ofReal_le_ofReal (by nlinarith [hThreshold])).trans htest.2

end RoughRegime.PoissonMeasure.AdmissibleReduction
