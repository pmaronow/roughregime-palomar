module

public import RoughRegime.AdmissibleProductTargets
public import RoughRegime.AdmissibleProductPoisson
public import RoughRegime.AdmissibleExperimentKernel
public import RoughRegime.AdmissibleExperimentTarget
public import RoughRegime.PoissonMinimaxReduction


@[expose] public section
/-! Finite testing transfer for the original admissible phase hypotheses.
Only the original coefficient and bilinear-separation hypotheses are supplied;
nonlinear target means, concentration, actual observation marginals and
randomized fixed-sample testing are derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissibleReductionTesting
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open AdmissibleTargets AdmissiblePhasePair

 theorem admissible_testing_lower (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi)
     (hPhi4 : ContDiffAt ℝ 4 Phi 0) :
     ∃ epsilon>0,∃ C ≥ 0,∃ B ≥ 0,∀ {H X Z Y : Type*} [MeasurableSpace H]
       [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
       {p : ℕ} [NeZero p] (μ : Measure X) [IsProbabilityMeasure μ] (π : ProbabilityMeasure Z)
       (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)
       (nu : Fin p→Measure H) [∀ i,IsProbabilityMeasure (nu i)]
       (M : ℕ) (CG CE R Lambda : ℝ) (rate : ℝ≥0)
       (_hAu1 : E.Au ≤ 1) (_hAv1 : E.Av ≤ 1)
       (_hu : E.C0*E.Au ≤ epsilon) (_hv : E.C0*E.Av ≤ epsilon)
       (_hLambda : 0 ≤ Lambda) (_hCG : 0 ≤ CG) (_hR : 0<R) (_hratepos : 0<rate)
       (_hrate : ((rate*E.pairMass/(p:ℝ≥0):ℝ≥0):ℝ) ≤ 1)
       (_hscale : ((rate*E.pairMass/(p:ℝ≥0):ℝ≥0):ℝ) ≤ 2*E.barp*Lambda)
       (_hGamma : ∀i j,M ≤ j→(E.pairs i).field.gammaNorm (nu i) ((2:ENNReal)•μ) E.Au E.Av M j ≤
         CG^(j+1)*E.Au^2*E.Av^2*Real.exp (CE*M)*LatticePriors.gammaSpatialFactor R M j)
       (_hHard : (p:ℝ)*LatticePriors.canonicalPoissonMajorant
         (comparisonStar E.lo E.hi E.barp E.C0 E.scores.C) CG CE R Lambda E.Au E.Av M ≤ 1/128)
       (c2 gap delta : ℝ) (_hc2 : 0<c2) (_hgap : 0<gap) (_hdelta : 0<delta)
       (_hBilinear : c2*gap ≤ |(∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M true)-
         (∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M false)|)
       (_hTaylor : 4*delta ≤ |OddTaylor.mixedDerivative Phi 0| *c2*gap-
         E.v0*C*E.hi*E.C0^4*E.Au*E.Av*(E.Au^2+E.Av^2))
       (_hVar : 8*E.v0^2*(E.hi*B)^2/(2*p:ℕ) ≤ (4*delta)^2/1024)
       (T : ProbabilityMeasure Y→ℝ) (Cls : Set (ProbabilityMeasure Y))
       (_hT : ∀q,T (E.observationProbability q)=E.targetFunctional Phi q)
       (_hCls : ∀q,E.observationProbability q∈Cls)
       (n : ℕ) (_hcount : ProbabilityTheory.poissonMeasure rate {m | m<n} ≤ (1/32:ℝ≥0∞)),
       (3/8:ℝ≥0∞) ≤ Model.minimaxTail n T Cls delta ∧
         ENNReal.ofReal (delta/2) ≤ Model.minimaxRMSE n T Cls := by
   obtain ⟨epsilon,he,C,hC,B,hB,hControls⟩ := uniform_target_controls Phi hPhi hPhi4
   refine ⟨epsilon,he,C,hC,B,hB,?_⟩
   intro H X Z Y _ _ _ _ p _ μ _ π E nu _ M CG CE R Lambda rate hAu1 hAv1 hu hv
     hLambda hCG hR hratepos hrate hscale hGamma hHard c2 gap delta hc2 hgap hdelta hBilinear hTaylor hVar T Cls hT hCls n hcount
   have hp : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
   let ratePair : ℝ≥0 := rate*(E.pairMass/(p:ℝ≥0))
   have hrateEq : rate*E.pairMass/(p:ℝ≥0)=ratePair := by
     apply NNReal.coe_injective
     simp only [NNReal.coe_mul,NNReal.coe_div,ratePair]
     ring
   have hratePair : (ratePair:ℝ) ≤ 1 := by rw [←hrateEq];exact hrate
   have hscalePair : (ratePair:ℝ) ≤ 2*E.barp*Lambda := by rw [←hrateEq];exact hscale
   let L := productPoissonMixture E.pairs nu E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
     E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small M ratePair true
   let Rlaw := productPoissonMixture E.pairs nu E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
     E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small M ratePair false
   have hH : GeneralTesting.hellingerSquared L Rlaw ≤ 1/128 := by
     have h := product_physical_comparison_coefficient E.pairs nu E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
       E.Au E.Av E.amplitudeU_nonneg hAu1 E.amplitudeV_nonneg hAv1 E.small M ratePair Lambda CG CE R
       hLambda hratePair hscalePair hCG hR hGamma
     simpa only [Fintype.card_fin] using h.2.trans (by simpa only [Fintype.card_fin] using hHard)
   let K := E.productPhaseKernel hAu1 hAv1 rate
   have hPL : (AdmissiblePhaseExperiment.parameterPrior nu M true ⊗ₘ K).map Prod.snd=L.measure := by
     rw [show (AdmissiblePhaseExperiment.parameterPrior nu M true ⊗ₘ K).map Prod.snd=(AdmissiblePhaseExperiment.parameterPrior nu M true ⊗ₘ K).snd from rfl]
     rw [E.productPhaseKernel_marginal]
     unfold L productPoissonMixture
     rw [LowerMeasure.fintypeProductDensityLaw_measure]
     rfl
   have hPR : (AdmissiblePhaseExperiment.parameterPrior nu M false ⊗ₘ K).map Prod.snd=Rlaw.measure := by
     rw [show (AdmissiblePhaseExperiment.parameterPrior nu M false ⊗ₘ K).map Prod.snd=(AdmissiblePhaseExperiment.parameterPrior nu M false ⊗ₘ K).snd from rfl]
     rw [E.productPhaseKernel_marginal]
     unfold Rlaw productPoissonMixture
     rw [LowerMeasure.fintypeProductDensityLaw_measure]
     rfl
   have hCtl := hControls μ E.pairs E.lo_pos E.hi_nonneg E.C0_nonneg nu M (E.v0/(p:ℝ)) E.Au E.Av
     E.amplitudeU_nonneg E.amplitudeV_nonneg hu hv
   have htarget : (fun q=>T (E.observationProbability q))=E.targetFunctional Phi := funext hT
   have ht : Measurable (fun q=>T (E.observationProbability q)) := by
     rw [htarget]
     exact independentTarget_measurable E.pairs Phi hPhi (E.v0/(p:ℝ)) E.Au E.Av
   have htL : MemLp (fun q=>T (E.observationProbability q)) 2 (AdmissiblePhaseExperiment.parameterPrior nu M true) := by
     rw [htarget]
     exact hCtl.1 true
   have htR : MemLp (fun q=>T (E.observationProbability q)) 2 (AdmissiblePhaseExperiment.parameterPrior nu M false) := by
     rw [htarget]
     exact hCtl.1 false
   let actualGap := |(∫q,T (E.observationProbability q) ∂AdmissiblePhaseExperiment.parameterPrior nu M false)-
     (∫q,T (E.observationProbability q) ∂AdmissiblePhaseExperiment.parameterPrior nu M true)|
   have hErr : |((∫q,E.targetFunctional Phi q ∂AdmissiblePhaseExperiment.parameterPrior nu M true)-
       (∫q,E.targetFunctional Phi q ∂AdmissiblePhaseExperiment.parameterPrior nu M false))-
       OddTaylor.mixedDerivative Phi 0*((∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M true)-
       (∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M false))| ≤
       E.v0*C*E.hi*E.C0^4*E.Au*E.Av*(E.Au^2+E.Av^2) := by
     have hs : |E.v0/(p:ℝ)| *(p:ℝ)=E.v0 := by
       rw [abs_of_nonneg (div_nonneg E.volume_nonneg hp.le),div_mul_cancel₀ _ hp.ne']
     simpa only [Fintype.card_fin,hs,AdmissiblePhaseExperiment.targetFunctional,independentTarget,AdmissiblePhaseExperiment.parameterPrior,independentPrior] using hCtl.2.2
   have hgapdelta : 4*delta ≤ actualGap := by
     let a := (∫q,E.targetFunctional Phi q ∂AdmissiblePhaseExperiment.parameterPrior nu M true)-
       (∫q,E.targetFunctional Phi q ∂AdmissiblePhaseExperiment.parameterPrior nu M false)
     let b := (∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M true)-
       (∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M false)
     let c := OddTaylor.mixedDerivative Phi 0
     have hab : |c*b| ≤ |a|+|a-c*b| := by
       have h := abs_sub a (a-c*b)
       simpa only [sub_sub_cancel] using h
     have hlead := mul_le_mul_of_nonneg_left hBilinear (abs_nonneg c)
     rw [←abs_mul] at hlead
     have hag : actualGap=|a| := by
       dsimp only [actualGap,a]
       simp_rw [hT]
       exact abs_sub_comm _ _
     rw [hag]
     dsimp only [a,b,c] at hab hlead
     linarith
   have hsep : 0<actualGap := (by positivity : (0:ℝ)<4*delta).trans_le hgapdelta
   have hvBound (positive:Bool) : variance (fun q=>T (E.observationProbability q))
       (AdmissiblePhaseExperiment.parameterPrior nu M positive) ≤ 8*E.v0^2*(E.hi*B)^2/(2*p:ℕ) := by
     rw [htarget]
     have h := hCtl.2.1 positive
     apply h.trans
     simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
     field_simp
     ring_nf
     exact le_rfl
   have hVarGap : (4*delta)^2/1024 ≤ actualGap^2/1024 := by
     gcongr
   have hvL := (hvBound true).trans (hVar.trans hVarGap)
   have hvR := (hvBound false).trans (hVar.trans hVarGap)
   have hlaw (q : Fin p→PhaseParameter H) :
       referenceProcess (E.observationProbability q:Measure Y) rate=E.poissonPlacementKernel rate ∘ₘ K q := by
     rw [show K q=E.pairProcess q rate from E.productPhaseKernel_apply hAu1 hAv1 rate q]
     exact (E.poissonPlacementKernel_law q rate hratepos).symm
   exact GeneralTesting.fuzzy_placement_fixed_minimax L Rlaw (AdmissiblePhaseExperiment.parameterPrior nu M true)
     (AdmissiblePhaseExperiment.parameterPrior nu M false) K hPL hPR (E.poissonPlacementKernel rate) E.observationProbability T rate
     hlaw
     Cls hCls ht htL htR hH hsep hvL hvR n hcount delta hdelta.le
     (by dsimp only [actualGap] at hgapdelta; linarith)

end RoughRegime.PoissonMeasure.AdmissibleReductionTesting
