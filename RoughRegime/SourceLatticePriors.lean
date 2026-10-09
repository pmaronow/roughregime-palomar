module

public import RoughRegime.SourceAdmissibility
public import RoughRegime.SourceRealizationHolder
public import RoughRegime.SourceLiteralCoefficients
public import RoughRegime.SourceTargetSeparation
public import RoughRegime.SourceAxisHolder
public import RoughRegime.SourceCoefficientIdentity
public import RoughRegime.SourceUnrestrictedHolder


@[expose] public section
/-! The full original lattice-prior endpoint. All fixed source parameters and
all constants precede the grid, hierarchical level, frequency, shrinking
margin, amplitudes and realization. The actual priors, fields and target are
those of the literal construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

structure SourceLatticeConclusions {D : ℕ} {alpha beta rminus rplus : ℝ}
    (S : SourceLatticeSetup D alpha beta rminus rplus) (C CG CE : ℝ) : Prop where
  constant_ge_one : 1 ≤ C
  gamma_constant_ge_one : 1 ≤ CG
  gamma_constant_eq : CG = gammaConstant rplus
  entropy_constant_nonneg : 0 ≤ CE
  cstar_bounds : 0 < sourceBandConstant (D+1) alpha beta ∧ sourceBandConstant (D+1) alpha beta < 1
  separation_constant_pos : 0 < S.separationConstant
  probability_priors : ∀ (N J M : ℕ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (positive : Bool), IsProbabilityMeasure (S.prior N J M hM hscale positive)
  independent_pairs : ∀ (N J M : ℕ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (positive : Bool),
    iIndepFun (fun k : GridPair D N=>fun z : GridPair D N → PairState (Fin J × Fin (D+1))=>z k)
      (S.prior N J M hM hscale positive)
  exact_conditional_signs : ∀ (N J M : ℕ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (positive : Bool), S.prior N J M hM hscale positive = Measure.pi (fun _ : GridPair D N=>
      (S.coefficientPrior J M hM hscale).prod (LatticeFourier.angleUniform.compProd (angularSignKernel M positive)))
  realization : ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
      RealizationProperties (F.p z) (F.u z) (F.v z) rminus rplus delta F.Au F.Av
        (gridRegion (D+1) N F.offset F.ell)
  density_outside : ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    ∀ z x, x ∉ gridRegion (D+1) N F.offset F.ell → F.p z x=F.p0
  pair_mass : ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    ∀ z (k : GridPair D N), (∫ x in gridBlockClosed F.offset F.ell (k,false) ∪ gridBlockClosed F.offset F.ell (k,true),
      F.p z x)=F.pairMass
  local_affine_density : ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    ∀ (z : GridPair D N → PairState (Fin J × Fin (D+1))) (b : GridBlock D N) x, x ∈ gridBlockClosed F.offset F.ell b →
      let y := gridCoords F.offset F.ell b x
      let φ := blockPhase F.U F.M F.a F.q F.gamma (z b.1).1 y
      F.p z x = (F.p0+F.outer y*((rminus+rplus)/2-F.p0)) +
        (Lower.sign b.2*((rplus-rminus)/2-delta)*F.outer y*Real.cos φ)*Real.cos ((z b.1).2.1) +
        (-(Lower.sign b.2*((rplus-rminus)/2-delta)*F.outer y*Real.sin φ))*Real.sin ((z b.1).2.1)
  local_signed_products : ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    ∀ (z : GridPair D N → PairState (Fin J × Fin (D+1))) (b : GridBlock D N) x, x ∈ gridBlockClosed F.offset F.ell b →
      let y := gridCoords F.offset F.ell b x
      let gate := jointGate F.Q F.M F.eta F.lambda (z b.1).1
      F.p z x*F.u z x=F.Au*Lower.sign (z b.1).2.2.1*gate*F.inner y ∧
      F.p z x*F.v z x=F.Av*Lower.sign (z b.1).2.2.2*gate*F.inner y
  holder : ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    ∀ z, Model.holderNorm (F.u z) alpha ≤ ENNReal.ofReal (C*epsilonU) ∧
      Model.holderNorm (F.v z) beta ≤ ENNReal.ofReal (C*epsilonV)
  coefficients : ∀ (J M j : ℕ) (delta Au Av : ℝ) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M),
    0 < delta → delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus →
    S.gammaL2Squared J M j delta Au Av hM hscale ≤
      if M ≤ j then CG ^ (j+1)*Au^2*Av^2*Real.exp (CE*M)*
        gammaSpatialFactor ((2:ℝ)^((D+1)*J)) M j else 0
  canonical_coefficients : ∀ (N J M j : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
    (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) (hM : 0 < M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M),
    epsilonU ≤ 1 → epsilonV ≤ 1 →
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    (2:ℝ)^(j+2)*F.canonicalPhaseField.gammaNorm (S.coefficientPrior J M hM hscale)
      ((Model.cubeVolume (D+1)).prod uniformBlockLabel) F.Au F.Av M j ≤
      if M ≤ j then CG^(j+1)*F.Au^2*F.Av^2*Real.exp (CE*M)*
        gammaSpatialFactor ((2:ℝ)^((D+1)*J)) M j else 0
  target_separation : ∀ (N J M : ℕ) (hN : 0 < N) (hM : 0 < M) (heven : Even M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (epsilonU epsilonV delta : ℝ) (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    S.separationConstant*F.Au*F.Av*intervalRho (rminus+delta) (rplus-delta)^M ≤
      (∫ z,F.productIntegral z ∂S.prior N J M hM hscale true)-
      (∫ z,F.productIntegral z ∂S.prior N J M hM hscale false)
  unrestricted_map : ∀ (map : ℝ×ℝ → ℝ) (V : Set (ℝ×ℝ)), IsOpen V → (0:ℝ×ℝ) ∈ V →
    ContDiffOn ℝ ∞ map V → ∃ eta CK : ℝ, 0 < eta ∧ 0 < CK ∧
      ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
        (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
        (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
      let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      F.Au+F.Av ≤ eta → ∀ z,
        ContDiff ℝ ∞ (fun x=>map ((F.field z).u x,(F.field z).v x)-map 0) ∧
        Model.holderNorm (fun x=>map ((F.field z).u x,(F.field z).v x)-map 0) (min alpha beta) ≤
          ENNReal.ofReal (CK*(epsilonU+epsilonV))
  first_axis_map : ∀ (map : ℝ×ℝ → ℝ) (V : Set (ℝ×ℝ)), IsOpen V → (0:ℝ×ℝ) ∈ V →
    ContDiffOn ℝ ∞ map V → (∀ v, (0,v) ∈ V → map (0,v)=0) →
    ∃ eta CK : ℝ, 0 < eta ∧ 0 < CK ∧
      ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
        (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
        (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
      let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      F.Au+F.Av ≤ eta → ∀ z,
        ContDiff ℝ ∞ (fun x=>map ((F.field z).u x,(F.field z).v x)) ∧
        Model.holderNorm (fun x=>map ((F.field z).u x,(F.field z).v x)) alpha ≤ ENNReal.ofReal (CK*epsilonU)
  second_axis_map : ∀ (map : ℝ×ℝ → ℝ) (V : Set (ℝ×ℝ)), IsOpen V → (0:ℝ×ℝ) ∈ V →
    ContDiffOn ℝ ∞ map V → (∀ u, (u,0) ∈ V → map (u,0)=0) →
    ∃ eta CK : ℝ, 0 < eta ∧ 0 < CK ∧
      ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
        (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
        (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
      let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      F.Au+F.Av ≤ eta → ∀ z,
        ContDiff ℝ ∞ (fun x=>map ((F.field z).u x,(F.field z).v x)) ∧
        Model.holderNorm (fun x=>map ((F.field z).u x,(F.field z).v x)) beta ≤ ENNReal.ofReal (CK*epsilonV)

/-- Lemma14 with the literal source choices and one common set of constants,
all fixed before every resolution and realization. -/
theorem source_lattice_priors {D : ℕ} {alpha beta rminus rplus : ℝ}
    (S : SourceLatticeSetup D alpha beta rminus rplus) :
    ∃ C CG CE : ℝ, SourceLatticeConclusions S C CG CE := by
  obtain ⟨C,hC,hholder⟩ := S.holder_bound
  obtain ⟨CE,hCE,hCG,hcoeff⟩ := S.uniform_coefficient_bound
  refine ⟨C,gammaConstant rplus,CE,?_⟩
  refine {
    constant_ge_one:=hC
    gamma_constant_ge_one:=hCG
    gamma_constant_eq:=rfl
    entropy_constant_nonneg:=hCE
    cstar_bounds:=sourceBandConstant_bounds _ (Nat.succ_pos _) _ _ S.alpha_pos S.beta_pos
    separation_constant_pos:=S.separationConstant_pos
    probability_priors:=by intros; infer_instance
    independent_pairs:=S.independent_pairs
    exact_conditional_signs:=S.prior_exact_conditional_signs
    realization:=by intros; exact CanonicalFrame.realization _ _
    density_outside:=by intros; exact CanonicalFrame.density_outside_region _ _ _ ‹_›
    pair_mass:=by intros; exact CanonicalFrame.geometric_pair_mass _ _ _
    local_affine_density:=by intros; exact CanonicalFrame.local_density_affine _ _ _ _ ‹_›
    local_signed_products:=by intros; exact CanonicalFrame.local_density_profile_products _ _ _ _ ‹_›
    holder:=hholder
    coefficients:=hcoeff
    canonical_coefficients:=by
      intro N J M j hN epsilonU epsilonV delta heU heV hd hmargin hM hscale heU1 heV1
      obtain ⟨hAu1,hAv1⟩ := S.frame_amplitudes_le_one N J M hN epsilonU epsilonV delta heU heV hd hmargin heU1 heV1
      dsimp only
      rw [S.canonical_gammaNorm_eq N J M j hN epsilonU epsilonV delta heU heV hd hmargin hM hscale hAu1 hAv1]
      exact hcoeff J M j delta _ _ hM hscale hd hmargin
    target_separation:=S.target_separation
    unrestricted_map:=source_unrestricted_K_holder S
    first_axis_map:=?_
    second_axis_map:=?_ }
  · intro map V hV hV0 hmap haxis
    simpa only [sub_zero] using source_axis_K_holder_first S map 0 V hV hV0 hmap haxis
  · intro map V hV hV0 hmap haxis
    simpa only [sub_zero] using source_axis_K_holder_second S map 0 V hV hV0 hmap haxis

/-- Complete fixed-parameter construction: the small volume and every
analytic parameter are chosen from the model endpoints and exponents. -/
theorem construct_source_lattice_priors (D : ℕ) (alpha beta rminus rplus : ℝ)
    (ha : 0 < alpha) (hb : 0 < beta) (hl : 0 < rminus) (hl1 : rminus < 1) (hh1 : 1 < rplus) :
    ∃ (S : SourceLatticeSetup D alpha beta rminus rplus) (C CG CE : ℝ),
      SourceLatticeConclusions S C CG CE := by
  exact ⟨sourceLatticeSetup D alpha beta rminus rplus ha hb hl hl1 hh1,
    source_lattice_priors _⟩

end RoughRegime.LatticePriors
