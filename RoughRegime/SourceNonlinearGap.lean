module

public import RoughRegime.SourceTargetSeparation
public import RoughRegime.CanonicalPriorTargets


@[expose] public section
/-! True nonlinear target mean separation for the original source priors,
derived from actual C4 regularity and the literal puv target separation. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

namespace CanonicalFrame
 theorem responseFunctional_bilinear {D N : ℕ} {ι : Type*} [Fintype ι]
     (F : CanonicalFrame D N ι) :
     F.responseFunctional (fun x=>x.1*x.2)=F.productIntegral := by
   funext z
   apply integral_congr_ae
   filter_upwards with x
   ring
end CanonicalFrame

namespace SourceLatticeSetup
variable {D : ℕ} {alpha beta rminus rplus : ℝ}
  (S : SourceLatticeSetup D alpha beta rminus rplus)

 theorem nonlinear_target_separation (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi)
     (hPhi4 : ContDiffAt ℝ 4 Phi 0) :
     ∃ epsilon>0,∃ C≥0,∃ B≥0,
       (∀ u v:ℝ,|u| ≤ epsilon→|v| ≤ epsilon→|Phi (u,v)-Phi 0| ≤ B) ∧
       ∀ (N J M : ℕ) (hN : 0<N) (hM : 0<M) (_heven : Even M)
         (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
         (epsilonU epsilonV delta : ℝ) (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV)
         (hd : 0<delta) (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
       let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
       F.Au/rminus ≤ epsilon→F.Av/rminus ≤ epsilon→
       |OddTaylor.mixedDerivative Phi 0| *S.separationConstant*F.Au*F.Av*
         Upper.intervalRho (rminus+delta) (rplus-delta)^M-
         S.v0*(C*rplus*(F.Au/rminus)*(F.Av/rminus)*
           ((F.Au/rminus)^2+(F.Av/rminus)^2)) ≤
       |F.priorMeanDifference Phi (S.coefficientPrior J M hM hscale)| := by
   obtain ⟨epsilon,he,C,hC,B,hB,hbound,hrem⟩ :=
     CanonicalFrame.uniform_response_prior_taylor Phi hPhi hPhi4
   refine ⟨epsilon,he,C,hC,B,hB,hbound,?_⟩
   intro N J M hN hM heven hscale epsilonU epsilonV delta heU heV hd hmargin
   dsimp only
   let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
   intro hAu hAv
   let nu := S.coefficientPrior J M hM hscale
   have ht := hrem F nu hAu hAv
   have hvolume := S.frame_volume N J M hN epsilonU epsilonV delta heU heV hd hmargin
   change (F.ell*(2*N:ℕ))^(D+1)=S.v0 at hvolume
   rw [hvolume] at ht
   have hg := S.target_separation N J M hN hM heven hscale epsilonU epsilonV delta
     heU heV hd hmargin
   dsimp only at hg
   rw [←F.responseFunctional_bilinear] at hg
   change S.separationConstant*F.Au*F.Av*Upper.intervalRho (rminus+delta) (rplus-delta)^M ≤
     F.priorMeanDifference (fun x=>x.1*x.2) nu at hg
   have hmul := mul_le_mul_of_nonneg_left (hg.trans (le_abs_self _))
     (abs_nonneg (OddTaylor.mixedDerivative Phi 0))
   have htriangle : |OddTaylor.mixedDerivative Phi 0*F.priorMeanDifference (fun x=>x.1*x.2) nu| ≤
       |F.priorMeanDifference Phi nu-OddTaylor.mixedDerivative Phi 0*
         F.priorMeanDifference (fun x=>x.1*x.2) nu| +|F.priorMeanDifference Phi nu| := by
     have h := abs_add_le (OddTaylor.mixedDerivative Phi 0*
       F.priorMeanDifference (fun x=>x.1*x.2) nu-F.priorMeanDifference Phi nu)
       (F.priorMeanDifference Phi nu)
     rw [sub_add_cancel,abs_sub_comm] at h
     exact h
   rw [abs_mul] at htriangle
   change |OddTaylor.mixedDerivative Phi 0| *S.separationConstant*F.Au*F.Av*
     Upper.intervalRho (rminus+delta) (rplus-delta)^M-
     S.v0*(C*F.rplus*(F.Au/F.rminus)*(F.Av/F.rminus)*
       ((F.Au/F.rminus)^2+(F.Av/F.rminus)^2)) ≤ |F.priorMeanDifference Phi nu|
   nlinarith
end SourceLatticeSetup
end RoughRegime.LatticePriors
