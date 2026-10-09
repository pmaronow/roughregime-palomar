module

public import RoughRegime.SourceLiteralCoefficients
public import RoughRegime.SourcePriorReindex


@[expose] public section
/-! The exact literal source coefficient prior and the canonical source
state prior differ only by their finite index order and product association. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace RoughRegime.LatticePriors.SourceLatticeSetup
open RoughRegime.LatticeFourier RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)

abbrev coordinatePrior (J M : ℕ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M) :=
  gatePrior (sourceGateOrder alpha beta) M
    (sourceEtas J (D+1) (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta)
      (sourceAlpha0 alpha beta) (min alpha beta))
    (by have:=S.Q_ge_three; omega) hM
    (sourceEtas_pos _ _ _ _ _ _ S.gamma_bounds.1 S.lambda_ge_one)
    (sourceEtas_band _ _ _ _ _ _ _ _ (by have:=S.Q_ge_three; omega) S.gamma_bounds.1
      S.gamma_bounds.2.1 S.lambda_ge_one S.alpha0_pos hscale)

 theorem literal_phasePrior_reindex (J M : ℕ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (positive : Bool) :
    MeasurePreserving (phaseStateEquiv (Equiv.prodComm (Fin (D+1)) (Fin J)))
      ((phasePrior (S.coordinatePrior J M hM hscale) M (if positive then 1 else -1)
        (by cases positive <;> norm_num)).measure)
      (blockPrior (S.coefficientPrior J M hM hscale) M positive) :=
  gate_phasePrior_reindex (Equiv.prodComm (Fin (D+1)) (Fin J)) (sourceGateOrder alpha beta) M
    (S.eta J) (by have:=S.Q_ge_three; omega) hM (S.eta_pos J) (S.eta_band J M hscale) positive

end RoughRegime.LatticePriors.SourceLatticeSetup
