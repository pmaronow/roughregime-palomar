module

public import RoughRegime.SourceLiteralPriorReindex
public import RoughRegime.CanonicalPhaseField
public import RoughRegime.PhaseFieldPriorTransport
public import RoughRegime.SourceRealizationHolder
public import RoughRegime.SourceAmplitudeGrid


@[expose] public section
/-! The literal source coefficient is the actual canonical marked-experiment
coefficient, under the original lattice prior, after finite index reordering. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.LatticePriors.SourceLatticeSetup
open RoughRegime.DyadicDigits RoughRegime.LatticeFourier RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)

def coordinateField (J M : ℕ) (delta : ℝ) :=
  latticePhaseField canonicalStep (sourceGateOrder alpha beta) M
    (sourceGammas J (D+1) (sourceGammaStar (D+1)))
    (sourceEtas J (D+1) (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta)
      (sourceAlpha0 alpha beta) (min alpha beta))
    (sourceLambdas J (D+1) (sourceLambdaStar (D+1) alpha beta))
    (sourceFixedBaseline (D+1) S.v0 rminus rplus) ((rminus+rplus)/2) ((rplus-rminus)/2-delta)
    (fun x=>outerBump (D+1) (WithLp.toLp 2 x))
    (fun x=>innerBump (D+1) (WithLp.toLp 2 x))

def latentIndexEquiv (J : ℕ) : (Fin (D+1) × Fin J → ℤ) ≃ᵐ (Fin J × Fin (D+1) → ℤ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin J × Fin (D+1)=>ℤ)
    (Equiv.prodComm (Fin (D+1)) (Fin J))

@[simp] theorem latentIndexEquiv_apply (J : ℕ) (ξ : Fin (D+1) × Fin J → ℤ) :
    latentIndexEquiv (D:=D) J ξ=fun k=>ξ (k.2,k.1) := by
  funext k
  rcases k with ⟨i,q⟩
  exact
    (MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : Fin J × Fin (D+1)=>ℤ)
      (Equiv.prodComm (Fin (D+1)) (Fin J)) ξ (q,i))

 theorem canonical_coordinate_field (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) :
    (S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin).canonicalCoordinatePhaseField.latentPullback
      (latentIndexEquiv (D:=D) J) = S.coordinateField J M delta := by
  let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
  have hphase (ξ : Fin (D+1) × Fin J → ℤ) (x : Fin (D+1) → ℝ) :
      blockPhase F.U F.M F.a F.q F.gamma (latentIndexEquiv (D:=D) J ξ) (WithLp.toLp 2 x)=
      sourceMarkPhase canonicalStep M (sourceGammas J (D+1) (sourceGammaStar (D+1))) ξ x := by
    simp only [latentIndexEquiv_apply]
    change blockPhase canonicalStep M (fun i : Fin J × Fin (D+1)=>J-i.1.val) Prod.snd
      (fun i=>sourceGamma (sourceGammaStar (D+1)) i.1.val) (fun k=>ξ (k.2,k.1)) (WithLp.toLp 2 x)=_
    simp only [blockPhase,coordinateSoftDigit,sourceMarkPhase,sourceGammas,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have hgate (ξ : Fin (D+1) × Fin J → ℤ) :
      jointGate F.Q F.M F.eta F.lambda (latentIndexEquiv (D:=D) J ξ)=
      jointGate (sourceGateOrder alpha beta) M
        (sourceEtas J (D+1) (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta)
          (sourceAlpha0 alpha beta) (min alpha beta))
        (sourceLambdas J (D+1) (sourceLambdaStar (D+1) alpha beta)) ξ := by
    simp only [latentIndexEquiv_apply]
    change jointGate (sourceGateOrder alpha beta) M
      (fun i : Fin J × Fin (D+1)=>sourceEta _ _ _ _ i.1.val)
      (fun i=>sourceLambda _ i.1.val) (fun k=>ξ (k.2,k.1))=_
    simp only [jointGate,sourceEtas,sourceLambdas,Fintype.prod_prod_type]
    rw [Finset.prod_comm]
  apply AffinePhaseField.ext_fields
  · funext ξ x
    change (outerBump _ (WithLp.toLp 2 x.1) - ∫y,outerBump _ y ∂Model.cubeVolume _) *
      ((rminus+rplus)/2-sourceFixedBaseline _ S.v0 rminus rplus)=_
    rw [cubeVolume_integral_transport]
    rfl
  · funext ξ x
    change RoughRegime.Lower.sign x.2*((rplus-rminus)/2-delta)*outerBump _ (WithLp.toLp 2 x.1)*
      Real.cos (blockPhase F.U F.M F.a F.q F.gamma (latentIndexEquiv (D:=D) J ξ) (WithLp.toLp 2 x.1))=_
    rw [hphase]
    unfold coordinateField latticePhaseField centeredWave
    ring
  · funext ξ x
    change -(RoughRegime.Lower.sign x.2*((rplus-rminus)/2-delta)*outerBump _ (WithLp.toLp 2 x.1)*
      Real.sin (blockPhase F.U F.M F.a F.q F.gamma (latentIndexEquiv (D:=D) J ξ) (WithLp.toLp 2 x.1)))=_
    rw [hphase]
    unfold coordinateField latticePhaseField centeredWave
    ring
  all_goals
    funext ξ x
    change jointGate F.Q F.M F.eta F.lambda (latentIndexEquiv (D:=D) J ξ)*innerBump _ (WithLp.toLp 2 x.1)=_
    rw [hgate]
    rfl

theorem coordinate_prior_preserving (J M : ℕ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M) :
    MeasurePreserving (latentIndexEquiv (D:=D) J) (S.coordinatePrior J M hM hscale)
      (S.coefficientPrior J M hM hscale) :=
  gatePrior_reindex (Equiv.prodComm (Fin (D+1)) (Fin J)) (sourceGateOrder alpha beta) M
    (S.eta J) (by have:=S.Q_ge_three; omega) hM (S.eta_pos J) (S.eta_band J M hscale)

 theorem coordinate_gammaNorm_eq (J M j : ℕ) (delta Au Av : ℝ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (hd : 0 < delta) (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus)
    (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) :
    (S.coordinateField J M delta).gammaNorm (S.coordinatePrior J M hM hscale)
      ((cubeUniform (D+1)).prod (Measure.count : Measure Bool)) Au Av M j =
      S.gammaL2Squared J M j delta Au Av hM hscale := by
  let outer := fun x : Fin (D+1) → ℝ=>outerBump (D+1) (WithLp.toLp 2 x)
  let inner := fun x : Fin (D+1) → ℝ=>innerBump (D+1) (WithLp.toLp 2 x)
  have ho : Continuous outer := (outerBump_smooth (D+1)).continuous.comp (PiLp.continuous_toLp 2 _)
  have hi : Continuous inner := (innerBump_smooth (D+1)).continuous.comp (PiLp.continuous_toLp 2 _)
  let p0 := sourceFixedBaseline (D+1) S.v0 rminus rplus
  have h0 : delta ≤ (p0-rminus)/2 := hmargin.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h1 : delta ≤ (rplus-p0)/2 := hmargin.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr : delta ≤ (rplus-rminus)/4 := hmargin.trans (min_le_left _ _)
  have hp : 0 ≤ p0 ∧ p0 ≤ rplus := by have hl:=S.lower_pos; constructor <;> linarith
  have hh : 0 ≤ (rplus-rminus)/2-delta := by linarith [S.interval]
  have hl : 0 ≤ (rminus+rplus)/2-((rplus-rminus)/2-delta) := by have hlo:=S.lower_pos; linarith
  have hu : (rminus+rplus)/2+((rplus-rminus)/2-delta) ≤ rplus := by linarith
  exact latticePhaseField_gammaNorm_eq canonicalStep (sourceGateOrder alpha beta) M
    (sourceGammas J (D+1) (sourceGammaStar (D+1)))
    (sourceEtas J (D+1) (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta)
      (sourceAlpha0 alpha beta) (min alpha beta))
    (sourceLambdas J (D+1) (sourceLambdaStar (D+1) alpha beta))
    (by have:=S.Q_ge_three; omega) hM
    (sourceEtas_pos _ _ _ _ _ _ S.gamma_bounds.1 S.lambda_ge_one)
    (sourceEtas_band _ _ _ _ _ _ _ _ (by have:=S.Q_ge_three; omega) S.gamma_bounds.1
      S.gamma_bounds.2.1 S.lambda_ge_one S.alpha0_pos hscale)
    (fun q i=>by have h := S.gamma_bounds.1; unfold sourceGammas sourceGamma; positivity)
    (fun q i=>sourceGamma_le_quarter _ _ S.gamma_bounds.1 S.gamma_bounds.2.1)
    p0 ((rminus+rplus)/2) ((rplus-rminus)/2-delta) Au Av rplus hAu hAu1 hAv hAv1
    (S.lower_pos.le.trans S.interval.le) outer inner ho hi
    (fun _=>by rw [abs_of_nonneg (innerBump (D+1)).nonneg]; exact (innerBump (D+1)).le_one)
    (fun _=>(outerBump (D+1)).nonneg) (fun _=>(outerBump (D+1)).le_one) hp hh hl hu j

 theorem canonical_gammaNorm_eq (N J M j : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (hAu1 : (S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin).Au ≤ 1)
    (hAv1 : (S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin).Av ≤ 1) :
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    (2:ℝ)^(j+2)*F.canonicalPhaseField.gammaNorm (S.coefficientPrior J M hM hscale)
      ((Model.cubeVolume (D+1)).prod uniformBlockLabel) F.Au F.Av M j =
      S.gammaL2Squared J M j delta F.Au F.Av hM hscale := by
  let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
  have he := S.coordinate_prior_preserving J M hM hscale
  have ht := F.canonicalCoordinatePhaseField.gammaNorm_latentPullback
    (S.coefficientPrior J M hM hscale) (S.coordinatePrior J M hM hscale)
    ((cubeUniform (D+1)).prod uniformBlockLabel)
    (latentIndexEquiv (D:=D) J) he F.Au F.Av M j
  rw [S.canonical_coordinate_field N J M hN epsilonU epsilonV delta heU heV hd hmargin] at ht
  have hs : (cubeUniform (D+1)).prod (Measure.count : Measure Bool)=
      (2:ENNReal) • ((cubeUniform (D+1)).prod uniformBlockLabel) := by
    rw [uniformBlockLabel,Measure.prod_smul_right,smul_smul]
    have htwo : (2:ENNReal)*2⁻¹=1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    rw [one_div,htwo,one_smul]
  have hc := S.coordinate_gammaNorm_eq J M j delta F.Au F.Av hM hscale hd hmargin
    F.Au_nonneg hAu1 F.Av_nonneg hAv1
  rw [hs,(S.coordinateField J M delta).gammaNorm_two_smul
    (S.coordinatePrior J M hM hscale) ((cubeUniform (D+1)).prod uniformBlockLabel) F.Au F.Av M j,ht] at hc
  have hcoord := F.canonicalPhaseField_gammaNorm_coordinate (S.coefficientPrior J M hM hscale) j
  have hmval : F.M=M := rfl
  rw [hmval] at hcoord
  rw [hcoord] at hc
  exact hc

theorem frame_amplitudes_le_one (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus)
    (heU1 : epsilonU ≤ 1) (heV1 : epsilonV ≤ 1) :
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    F.Au ≤ 1 ∧ F.Av ≤ 1 := by
  have hb : (1:ℝ)≤2*(N:ℝ) := by exact_mod_cast (by omega : 1≤2*N)
  have hu := sourceAmplitude_grid_le epsilonU N J (D+1) alpha (sourceFineScale J (min alpha beta))
    heU hN (Nat.succ_pos _) (S.fine_pos J).le (S.fine_below_alpha J)
  have hv := sourceAmplitude_grid_le epsilonV N J (D+1) beta (sourceFineScale J (min alpha beta))
    heV hN (Nat.succ_pos _) (S.fine_pos J).le (S.fine_below_beta J)
  have hra := Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr S.alpha_pos.le)
  have hrb := Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr S.beta_pos.le)
  exact ⟨hu.trans ((mul_le_mul_of_nonneg_left hra heU).trans (by simpa using heU1)),
    hv.trans ((mul_le_mul_of_nonneg_left hrb heV).trans (by simpa using heV1))⟩

 theorem uniform_canonical_coefficient_bound : ∃ CE : ℝ, 0 ≤ CE ∧ 1≤gammaConstant rplus ∧
    ∀ (N J M j : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
      (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
      (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) (hM : 0 < M)
      (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M),
      epsilonU ≤ 1 → epsilonV ≤ 1 →
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    (2:ℝ)^(j+2)*F.canonicalPhaseField.gammaNorm (S.coefficientPrior J M hM hscale)
      ((Model.cubeVolume (D+1)).prod uniformBlockLabel) F.Au F.Av M j ≤
      if M≤j then gammaConstant rplus^(j+1)*F.Au^2*F.Av^2*Real.exp (CE*M)*
        gammaSpatialFactor ((2:ℝ)^((D+1)*J)) M j else 0 := by
  obtain ⟨CE,hCE,hCG,hbound⟩:=S.uniform_coefficient_bound
  refine ⟨CE,hCE,hCG,?_⟩
  intro N J M j hN epsilonU epsilonV delta heU heV hd hmargin hM hscale heU1 heV1
  obtain ⟨hAu1,hAv1⟩:=S.frame_amplitudes_le_one N J M hN epsilonU epsilonV delta heU heV hd hmargin heU1 heV1
  dsimp only
  rw [S.canonical_gammaNorm_eq N J M j hN epsilonU epsilonV delta heU heV hd hmargin hM hscale hAu1 hAv1]
  exact hbound J M j delta _ _ hM hscale hd hmargin

end RoughRegime.LatticePriors.SourceLatticeSetup
