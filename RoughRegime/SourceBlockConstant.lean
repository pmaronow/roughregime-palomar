module

public import RoughRegime.SourceLiteralCoefficients
public import RoughRegime.SourceCoefficientIdentity
public import RoughRegime.SourceNonlinearGap
public import RoughRegime.SourceAdmissibility
public import RoughRegime.BlockConstantReduction


@[expose] public section
/-! The literal J=0 source construction has no digit phase and no gate loss.
Its genuine priors and physical coefficients satisfy the two source estimates
with R=m=1. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier
set_option backward.isDefEq.respectTransparency false

 theorem blockPhase_empty {d : ℕ} {ι : Type*} [Fintype ι] [IsEmpty ι]
     (U : SmoothStep) (M : ℕ) (a : ι→ℕ) (q : ι→Fin d) (gamma : ι→ℝ)
     (z : ι→ℤ) (x : Model.Covariate d) : blockPhase U M a q gamma z x=0 := by
   simp [blockPhase]

 theorem jointGate_empty {ι : Type*} [Fintype ι] [IsEmpty ι]
     (Q M : ℕ) (eta lam : ι→ℝ) (z : ι→ℤ) : jointGate Q M eta lam z=1 := by
   simp [jointGate]

@[simp] theorem sourceFineScale_zero (s : ℝ) : sourceFineScale 0 s=1 := by simp [sourceFineScale]
@[simp] theorem sourceSpatialVolume_zero (d : ℕ) : sourceSpatialVolume 0 d=1 := by simp [sourceSpatialVolume]
@[simp] theorem sourceAmplitude_zero (epsilon B : ℝ) (d : ℕ) (t : ℝ) :
    sourceAmplitude epsilon B 0 d t 1=epsilon*B^(-(t/(d:ℝ))) := by simp [sourceAmplitude]

namespace SourceLatticeSetup
variable {D : ℕ} {alpha beta rminus rplus : ℝ}
    (S : SourceLatticeSetup D alpha beta rminus rplus)

 theorem block_constant_amplitudes (N M : ℕ) (hN : 0<N) (epsilonU epsilonV delta : ℝ)
     (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0<delta)
     (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) :
     let F := S.frame N 0 M hN epsilonU epsilonV delta heU heV hd hmargin
     F.Au=epsilonU*(sourceGridCount N (D+1))^(-(alpha/(D+1:ℕ))) ∧
       F.Av=epsilonV*(sourceGridCount N (D+1))^(-(beta/(D+1:ℕ))) := by
   dsimp only [frame,sourceCanonicalFrame]
   simp [sourceAmplitude,sourceSpatialVolume,sourceFineScale]

/-- The literal J=0 density varies only through the one angular variable;
the arithmetic lattice phase and the multiplicative gate are constant. -/
 theorem block_constant_local_density (N M : ℕ) (hN : 0<N) (epsilonU epsilonV delta : ℝ)
     (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0<delta)
     (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus)
     (w : PairState (Fin 0×Fin (D+1))) (label : Bool) (y : Model.Covariate (D+1)) :
     let F := S.frame N 0 M hN epsilonU epsilonV delta heU heV hd hmargin
     F.localBlockDensity w label y=
       F.p0+F.outer y*((rminus+rplus)/2-F.p0)+
         Lower.sign label*((rplus-rminus)/2-delta)*F.outer y*Real.cos w.2.1 := by
   dsimp only
   unfold CanonicalFrame.localBlockDensity blockDensity blockOscillatingDensity
   rw [blockPhase_empty,add_zero]
   dsimp only [frame,sourceCanonicalFrame]
   ring

/-- Genuine physical coefficients of the J=0 priors satisfy the original
Gamma estimate with R=1, including exact low-degree cancellation. -/
 theorem block_constant_coefficient_bound : ∃CE:ℝ,0 ≤ CE ∧ 1 ≤ gammaConstant rplus ∧
     ∀(M j : ℕ)(delta Au Av : ℝ)(hM : 0<M)
       (hscale : 1 ≤ sourceBandConstant (D+1) alpha beta*M),
       0<delta→delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus→
       S.gammaL2Squared 0 M j delta Au Av hM (by simpa using hscale) ≤
         if M ≤ j then gammaConstant rplus^(j+1)*Au^2*Av^2*Real.exp (CE*M) else 0 := by
   obtain ⟨CE,hCE,hCG,hb⟩ := S.uniform_coefficient_bound
   refine ⟨CE,hCE,hCG,?_⟩
   intro M j delta Au Av hM hscale hd hmargin
   simpa [gammaSpatialFactor] using hb 0 M j delta Au Av hM (by simpa using hscale) hd hmargin

/-- The actual globally glued bilinear functional under the J=0 probability
priors has the source gap, with a constant fixed before all grid sizes. -/
 theorem block_constant_bilinear_separation (N M : ℕ) (hN : 0<N) (hM : 0<M) (heven : Even M)
     (hscale : 1 ≤ sourceBandConstant (D+1) alpha beta*M)
     (epsilonU epsilonV delta : ℝ) (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0<delta)
     (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) :
     let F := S.frame N 0 M hN epsilonU epsilonV delta heU heV hd hmargin
     S.separationConstant*F.Au*F.Av*Upper.intervalRho (rminus+delta) (rplus-delta)^M ≤
       (∫z,F.productIntegral z ∂S.prior N 0 M hM (by simpa using hscale) true)-
       (∫z,F.productIntegral z ∂S.prior N 0 M hM (by simpa using hscale) false) := by
   exact S.target_separation N 0 M hN hM heven (by simpa using hscale)
     epsilonU epsilonV delta heU heV hd hmargin

end SourceLatticeSetup
end RoughRegime.LatticePriors
