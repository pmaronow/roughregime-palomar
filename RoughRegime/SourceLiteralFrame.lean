module

public import RoughRegime.SourceFrame
public import RoughRegime.SourceAnalyticParameters
public import RoughRegime.SourceGamma
public import RoughRegime.CanonicalLattice


@[expose] public section
/-! The fixed parameters and actual probability priors of the original
lattice construction, chosen once before the grid and frequency. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

structure SourceLatticeSetup (D : ℕ) (alpha beta rminus rplus : ℝ) where
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  lower_pos : 0 < rminus
  lower_lt_one : rminus < 1
  one_lt_upper : 1 < rplus
  v0 : ℝ
  volume_pos : 0 < v0
  volume_le_half : v0 ≤ 1/2
  denominator_pos : 0 < 1-v0*sourceOuterIntegral (D+1)
  margin_pos : 0 < sourceMarginBound (D+1) v0 rminus rplus

def sourceLatticeSetup (D : ℕ) (alpha beta rminus rplus : ℝ)
    (ha : 0< alpha) (hb : 0< beta) (hl : 0< rminus) (hl1 : rminus<1) (hh1 : 1< rplus) :
    SourceLatticeSetup D alpha beta rminus rplus := by
  let h := exists_source_fixed_volume (D+1) rminus rplus hl1 hh1
  exact ⟨ha,hb,hl,hl1,hh1,h.choose,h.choose_spec.1,h.choose_spec.2.1,
    h.choose_spec.2.2.1,h.choose_spec.2.2.2⟩

namespace SourceLatticeSetup
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)
include S

 theorem interval : rminus < rplus := S.lower_lt_one.trans S.one_lt_upper
 theorem volume_le_one : S.v0 ≤ 1 := by linarith [S.volume_le_half]
 theorem fine_pos (J : ℕ) : 0 < sourceFineScale J (min alpha beta) := by
   unfold sourceFineScale; positivity
 theorem Q_ge_three : 3 ≤ sourceGateOrder alpha beta := sourceGateOrder_ge_three _ _ S.alpha_pos
 theorem gamma_bounds : 0< sourceGammaStar (D+1) ∧ sourceGammaStar (D+1)≤1/4 ∧
     sourceGammaStar (D+1)≤ sourceInnerSquareIntegral (D+1)/(16*(D+1:ℕ)) :=
   sourceGammaStar_bounds _ (Nat.succ_pos _)
 theorem lambda_ge_one : 1≤ sourceLambdaStar (D+1) alpha beta := sourceLambdaStar_ge_one _ _ _
 theorem alpha0_pos : 0< sourceAlpha0 alpha beta := sourceAlpha0_pos _ _ S.alpha_pos S.beta_pos

abbrev frame (N J M : ℕ) (hN : 0< N) (epsilonU epsilonV delta : ℝ)
    (heU : 0≤ epsilonU) (heV : 0≤ epsilonV) (hd : 0< delta)
    (hmargin : delta≤ sourceMarginBound (D+1) S.v0 rminus rplus) :=
  sourceCanonicalFrame D N J (sourceGateOrder alpha beta) M hN
    (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta) (sourceAlpha0 alpha beta)
    (sourceFineScale J (min alpha beta)) epsilonU epsilonV alpha beta S.v0 rminus rplus delta
    S.gamma_bounds.1 S.gamma_bounds.2.1 (S.fine_pos J) heU heV S.volume_pos S.volume_le_one
    S.lower_pos S.interval hd hmargin S.denominator_pos

def eta (S : SourceLatticeSetup D alpha beta rminus rplus) (J : ℕ) : Fin J × Fin (D+1) → ℝ :=
  fun i=> sourceEta (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta)
    (sourceAlpha0 alpha beta) (sourceFineScale J (min alpha beta)) i.1.val
 theorem eta_pos (J : ℕ) (i : Fin J × Fin (D+1)) : 0< S.eta J i :=
  sourceEta_pos _ _ _ _ _ S.gamma_bounds.1 (zero_lt_one.trans_le S.lambda_ge_one) (S.fine_pos J)
 theorem eta_band (J M : ℕ)
    (hscale : sourceFineScale J (min alpha beta)≤ sourceBandConstant (D+1) alpha beta*M)
    (i : Fin J × Fin (D+1)) : 4*(6*sourceGateOrder alpha beta/S.eta J i)≤(M:ℝ) :=
  literal_source_lattice_band _ (Nat.succ_pos _) _ _ S.alpha_pos S.beta_pos M _ (S.fine_pos J) hscale i.1.val

def coefficientPrior (J M : ℕ) (hM : 0< M)
    (hscale : sourceFineScale J (min alpha beta)≤ sourceBandConstant (D+1) alpha beta*M) :
    Measure (Fin J × Fin (D+1) → ℤ) :=
  gatePrior (sourceGateOrder alpha beta) M (S.eta J) (by have:=S.Q_ge_three; omega)
    hM (S.eta_pos J) (S.eta_band J M hscale)
instance coefficientPrior_probability (J M : ℕ) (hM : 0< M)
    (hscale : sourceFineScale J (min alpha beta)≤ sourceBandConstant (D+1) alpha beta*M) :
    IsProbabilityMeasure (S.coefficientPrior J M hM hscale) := by
  unfold coefficientPrior
  infer_instance

def prior (N J M : ℕ) (hM : 0< M)
    (hscale : sourceFineScale J (min alpha beta)≤ sourceBandConstant (D+1) alpha beta*M) (positive : Bool) :
    Measure (GridPair D N → PairState (Fin J × Fin (D+1))) :=
  globalBlockPrior (S.coefficientPrior J M hM hscale) M positive
instance prior_probability (N J M : ℕ) (hM : 0< M)
    (hscale : sourceFineScale J (min alpha beta)≤ sourceBandConstant (D+1) alpha beta*M) (positive : Bool) :
    IsProbabilityMeasure (S.prior N J M hM hscale positive) := by
  unfold prior
  infer_instance

/-- The pairs are literally independent and have the original angular/sign law. -/
 theorem prior_eq_pi (N J M : ℕ) (hM : 0< M)
    (hscale : sourceFineScale J (min alpha beta)≤ sourceBandConstant (D+1) alpha beta*M) (positive : Bool) :
    S.prior N J M hM hscale positive =
      Measure.pi (fun _ : GridPair D N=> blockPrior (S.coefficientPrior J M hM hscale) M positive) := rfl

def separationConstant : ℝ := 9*S.v0*sourceInnerSquareIntegral (D+1)/(16*intervalCenter rminus rplus)
 theorem separationConstant_pos : 0< S.separationConstant := by
   unfold separationConstant intervalCenter
   have hv := S.volume_pos
   have hl := S.lower_pos
   have hh : 0< rplus := S.lower_pos.trans S.interval
   have hI := innerBump_square_integral_pos (D+1)
   change 0< sourceInnerSquareIntegral (D+1) at hI
   positivity

 theorem frame_volume (N J M : ℕ) (hN : 0< N) (epsilonU epsilonV delta : ℝ)
    (heU : 0≤ epsilonU) (heV : 0≤ epsilonV) (hd : 0< delta)
    (hmargin : delta≤ sourceMarginBound (D+1) S.v0 rminus rplus) :
    ((S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin).ell*(2*N:ℕ))^(D+1)=S.v0 := by
   change (sourceBlockScale S.v0 (sourceGridCount N (D+1)) (D+1)*(2*N:ℕ))^(D+1)=_
   rw [sourceBlockScale_grid_side _ _ _ S.volume_pos.le hN (Nat.succ_pos _)]
   simpa only [sourceGridSide,one_div] using Real.rpow_inv_natCast_pow S.volume_pos.le (Nat.succ_ne_zero D)

end SourceLatticeSetup
end RoughRegime.LatticePriors
