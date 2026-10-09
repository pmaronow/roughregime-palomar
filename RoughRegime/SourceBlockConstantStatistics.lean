module

public import RoughRegime.SourceBlockConstantModel
public import RoughRegime.SourceBlockConstantParameters
public import RoughRegime.SourceNonlinearGap
public import RoughRegime.SourceSelectedVariance


@[expose] public section
/-! Target separation and independent-prior concentration for the literal
J=0 construction, at the actual rounded R=m=1 reduction scales. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {pi : ProbabilityMeasure Z}
variable (F : SourceModelFamily A0 D O pi) (hrough : (A0.withDimension D).theta<1/2)
    (Cstar CG CE : ℝ) (hstar : 1 ≤ Cstar) (hCG : 1 ≤ CG) (hCE : 0 ≤ CE)

 theorem blockConstantFrame_Au_numeric (n : ℕ)
     (V : F.BlockConstantValidity
       (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).theta
       (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).tau
       (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).c0 n) :
     let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
     (F.blockConstantFrame P.theta P.tau P.c0 n V).Au=P.blockConstantChoice.Au n := by
   dsimp only
   rw [F.blockConstantFrame_Au]
   rfl

 theorem blockConstantFrame_Av_numeric (n : ℕ)
     (V : F.BlockConstantValidity
       (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).theta
       (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).tau
       (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).c0 n) :
     let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
     (F.blockConstantFrame P.theta P.tau P.c0 n V).Av=P.blockConstantChoice.Av n := by
   dsimp only
   rw [F.blockConstantFrame_Av]
   rfl

 theorem eventually_blockConstant_radius (epsilon : ℝ) (he : 0<epsilon) :
     let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
     ∀ᶠ n in atTop,∀V : F.BlockConstantValidity P.theta P.tau P.c0 n,
       (F.blockConstantFrame P.theta P.tau P.c0 n V).Au/F.rminus ≤ epsilon ∧
       (F.blockConstantFrame P.theta P.tau P.c0 n V).Av/F.rminus ≤ epsilon := by
   dsimp only
   let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
   let S := P.blockConstantChoice
   have hu := S.Au_tendsto_zero.div_const F.rminus
   have hv := S.Av_tendsto_zero.div_const F.rminus
   simp only [zero_div] at hu hv
   filter_upwards [hu.eventually_le_const he,hv.eventually_le_const he] with n hun hvn
   intro V
   rw [F.blockConstantFrame_Au_numeric hrough Cstar CG CE hstar hCG hCE n V,
     F.blockConstantFrame_Av_numeric hrough Cstar CG CE hstar hCG hCE n V]
   exact ⟨hun,hvn⟩

/-- Actual Model target priors in the J=0 construction concentrate around
means separated by a fixed positive multiple of the common rough scale.
All Taylor and variance budgets follow from the true numeric tuning. -/
 theorem blockConstant_target_statistics :
     let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
     ∃ cg : ℝ,0<cg ∧ ∀ᶠ n in atTop,∀V : F.BlockConstantValidity P.theta P.tau P.c0 n,
       ∀(hM : 0<frequency n P.theta P.tau)
         (hband : 1 ≤ sourceBandConstant (D+1) A0.α A0.β*frequency n P.theta P.tau),
       let G := F.blockConstantFrame P.theta P.tau P.c0 n V
       let nu := F.latticeSetup.coefficientPrior 0 (frequency n P.theta P.tau) hM (by simpa [sourceFineScale] using hband)
       ∀hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4,
       (∀positive:Bool,MemLp (F.actualTarget G hsmall) 2 (globalBlockPrior nu G.M positive)) ∧
       (∀positive:Bool,variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive) ≤
         (F.actualMeanGap G hsmall nu)^2/1024) ∧
       cg*RoughRegime.Rates.subcriticalScale n P.theta P.tau ≤ F.actualMeanGap G hsmall nu := by
   dsimp only
   let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
   let S := P.blockConstantChoice
   obtain ⟨epsilon,he,C,hC,B,hB,hbound,hseps⟩ :=
     F.latticeSetup.nonlinear_target_separation F.integrand F.integrand_measurable F.integrand_C4
   let Cerr := F.volume*C*F.rplus/F.rminus^4
   let Cvar := 4*(F.rplus*B)^2
   let cg := F.gapCoefficient*AbstractScaleChoice.gapConstant P
   have hcg : 0<cg := mul_pos F.gapCoefficient_pos (AbstractScaleChoice.gapConstant_pos P)
   have hbudget := S.Taylor_error_ratio_tendsto_zero Cerr
   have hvarbudget := S.prior_variance_eventually_budget Cvar F.gapCoefficient (1/1024)
     F.gapCoefficient_pos (by norm_num)
   refine ⟨cg,hcg,?_⟩
   filter_upwards [F.eventually_blockConstant_radius hrough Cstar CG CE hstar hCG hCE epsilon he,
     hbudget.eventually_le_const F.gapCoefficient_pos,hvarbudget,S.gap_eventually_pos,S.gap_eventually_lower]
       with n hrad herrorn hvarn hgp hscale
   intro V hM hband
   let G := F.blockConstantFrame P.theta P.tau P.c0 n V
   let nu := F.latticeSetup.coefficientPrior 0 (frequency n P.theta P.tau) hM (by simpa [sourceFineScale] using hband)
   intro hsmall
   have hradG : G.Au/G.rminus ≤ epsilon ∧ G.Av/G.rminus ≤ epsilon := hrad V
   have hAu : G.Au=S.Au n := F.blockConstantFrame_Au_numeric hrough Cstar CG CE hstar hCG hCE n V
   have hAv : G.Av=S.Av n := F.blockConstantFrame_Av_numeric hrough Cstar CG CE hstar hCG hCE n V
   have hErr : Cerr*S.Au n*S.Av n*((S.Au n)^2+(S.Av n)^2) ≤ F.gapCoefficient*S.gap n :=
     (div_le_iff₀ hgp).mp herrorn
   have ht := hseps (F.blockConstantGrid P.theta P.tau P.c0 n) 0 (frequency n P.theta P.tau)
     V.positive_grid hM (nearestEven_even _) (by simpa [sourceFineScale] using hband)
     F.epsilonU F.epsilonV (sourceDensityMargin n) F.epsilonU_pos.le F.epsilonV_pos.le
     V.positive_margin V.margin_le
   dsimp only at ht
   rw [←F.blockConstantFrame_eq_latticeSetup P.theta P.tau P.c0 n V] at ht
   have htG := ht hradG.1 hradG.2
   have hMean : F.actualMeanGap G hsmall nu=|G.priorMeanDifference F.integrand nu| := by
     unfold actualMeanGap
     rw [F.actualTarget_eq_responseFunctional G hsmall]
     rfl
   have hErrEq : F.volume*(C*F.rplus*(G.Au/F.rminus)*(G.Av/F.rminus)*
       ((G.Au/F.rminus)^2+(G.Av/F.rminus)^2))=Cerr*S.Au n*S.Av n*((S.Au n)^2+(S.Av n)^2) := by
     rw [hAu,hAv]
     dsimp [Cerr]
     field_simp [F.interval.1.ne']
   have hLead : |OddTaylor.mixedDerivative F.integrand 0| *F.latticeSetup.separationConstant*G.Au*G.Av*
       Upper.intervalRho (F.rminus+sourceDensityMargin n) (F.rplus-sourceDensityMargin n)^(frequency n P.theta P.tau)=
       2*F.gapCoefficient*S.gap n := by
     rw [S.gap_eq,hAu,hAv]
     dsimp only [gapCoefficient,Upper.narrowedRho,P,blockConstantParameters,sourceDensityMargin]
     ring
   change _-F.volume*(C*F.rplus*(G.Au/F.rminus)*(G.Av/F.rminus)*
       ((G.Au/F.rminus)^2+(G.Av/F.rminus)^2)) ≤ |G.priorMeanDifference F.integrand nu| at htG
   rw [hErrEq,hLead,←hMean] at htG
   have hgap : F.gapCoefficient*S.gap n ≤ F.actualMeanGap G hsmall nu := by linarith
   have hboundG : ∀u v:ℝ,|u| ≤ G.Au/G.rminus→|v| ≤ G.Av/G.rminus→
       |F.integrand (u,v)-F.integrand 0| ≤ B := by
     intro u v hu hv
     exact hbound u v (hu.trans hradG.1) (hv.trans hradG.2)
   have hLp := F.actualTarget_prior_memLp G hsmall B hboundG nu
   have hVar := F.actualTarget_prior_variance_grid G V.positive_grid hsmall B hB hboundG nu
   have hCount : ((2*F.blockConstantGrid P.theta P.tau P.c0 n:ℕ):ℝ)^(D+1)=(S.B n:ℝ) := by
     change ((2*F.blockConstantGrid P.theta P.tau P.c0 n:ℕ):ℝ)^(D+1)=
       (selectedBlockCount P.theta P.tau P.c0 (fun _=>1) (D+1) n:ℝ)
     simpa only [blockConstantGrid,sourceGridCount,Nat.cast_mul,Nat.cast_ofNat] using
       selectedGrid_blockCount_eq P.theta P.tau P.c0 (fun _=>1) (D+1) n
   have hVar' : ∀positive:Bool,variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive) ≤ Cvar/(S.B n:ℝ) := by
     intro positive
     have hv := hVar positive
     rw [hCount] at hv
     exact hv
   have hVarFinal := F.prior_variance_control_of_bounds G hsmall nu _ (F.gapCoefficient*S.gap n)
     (mul_pos F.gapCoefficient_pos hgp).le hVar' (by convert hvarn using 1; ring) hgap
   refine ⟨hLp,hVarFinal,?_⟩
   have hscale' : AbstractScaleChoice.gapConstant P*RoughRegime.Rates.subcriticalScale n P.theta P.tau ≤ S.gap n := by
     simpa only [S,AbstractScaleParameters.blockConstantChoice_m,one_pow,mul_one] using hscale
   calc
     _ = F.gapCoefficient*(AbstractScaleChoice.gapConstant P*RoughRegime.Rates.subcriticalScale n P.theta P.tau) := by dsimp [cg]; ring
     _ ≤ F.gapCoefficient*S.gap n := mul_le_mul_of_nonneg_left hscale' F.gapCoefficient_pos.le
     _ ≤ _ := hgap

end RoughRegime.LatticePriors.SourceModelFamily
