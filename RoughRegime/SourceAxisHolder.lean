module

public import RoughRegime.SourceLiteralFrame
public import RoughRegime.CanonicalKHolder


@[expose] public section
/-! The exact two axis estimates in Lemma14(b), with every source analytic
parameter fixed literally and constants chosen before the grid resolutions. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

variable {D : ℕ} {alpha beta rminus rplus : ℝ}

theorem source_axis_K_holder_first (S : SourceLatticeSetup D alpha beta rminus rplus)
    (map : ℝ × ℝ → ℝ) (k0 : ℝ) (V : Set (ℝ × ℝ)) (hV : IsOpen V)
    (hV0 : (0:ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V)
    (haxis : ∀ v : ℝ, (0,v) ∈ V  →  map (0,v)=k0) :
    ∃ eta C : ℝ, 0<eta ∧ 0<C ∧
      ∀ (N J M : ℕ) (hN : 0<N) (epsilonU epsilonV delta : ℝ),
      ∀ (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0<delta)
        (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
      let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      F.Au+F.Av ≤ eta  →  ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
        ContDiff ℝ ∞ (fun x => map ((F.field z).u x,(F.field z).v x)-k0) ∧
          Model.holderNorm (fun x => map ((F.field z).u x,(F.field z).v x)-k0) alpha ≤ 
            ENNReal.ofReal (C*epsilonU) := by
  have hinner (x : Model.Covariate (D+1)) : innerBump (D+1) x ∈ Icc (0:ℝ) 1 :=
    ⟨(innerBump (D+1)).nonneg,(innerBump (D+1)).le_one⟩
  obtain ⟨eta,C,heta,hC,hbound⟩ := canonical_source_K_holder_first canonicalStep D
    (sourceGateOrder alpha beta) (sourceJetBudget alpha beta)
    (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta) (sourceAlpha0 alpha beta)
    S.gamma_bounds.1 S.gamma_bounds.2.1 (zero_lt_one.trans_le S.lambda_ge_one)
    S.alpha0_pos.le (sourceAlpha0_lt_one alpha beta) (sourceJetBudget_pos alpha beta)
    (sourceJetBudget_le_twice_order alpha beta) rminus rplus S.lower_pos S.interval
    (innerBump (D+1)) (outerBump (D+1)) (outerBump_one_on_inner (D+1))
    (innerBump_zero_outside (D+1)) (outerBump_zero_outside (D+1))
    (innerBump_smooth (D+1)) (innerBump_compact (D+1)) hinner (innerBump_tsupport_subset (D+1))
    alpha beta (sourceAlpha0_lt_alpha alpha beta S.alpha_pos)
    (source_alpha_derivative_budget alpha beta S.alpha_pos) S.v0 S.volume_pos map k0 V hV hV0 hmap haxis
  refine ⟨eta,C,heta,hC,?_⟩
  intro N J M hN epsilonU epsilonV delta heU heV hd hmargin
  dsimp only
  intro hsmall z
  have hm0 : (2:ℝ)^((J:ℝ)*sourceAlpha0 alpha beta) ≤ sourceFineScale J (min alpha beta) := by
    unfold sourceFineScale
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (le_min (sourceAlpha0_lt_alpha alpha beta S.alpha_pos).le (sourceAlpha0_lt_beta alpha beta S.beta_pos).le)
      (Nat.cast_nonneg J)
  have hmU : sourceFineScale J (min alpha beta) ≤ (2:ℝ)^((J:ℝ)*alpha) := by
    unfold sourceFineScale
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg J))
  have hh : (rplus-rminus)/2-delta ∈ Icc (-intervalHalfWidth rminus rplus) (intervalHalfWidth rminus rplus) := by
    have he := hmargin.trans (min_le_left _ _)
    unfold intervalHalfWidth
    constructor <;> linarith
  have he := hbound N (sourceGridOffset S.v0 (D+1)) (sourceGridCount N (D+1))
    (sourceFixedBaseline (D+1) S.v0 rminus rplus) epsilonU epsilonV (sourceGridCount_pos N (D+1) hN)
    heU heV (sourceBlockScale_grid_le_one S.v0 N (D+1) S.volume_pos S.volume_le_one hN)
    J M _ hm0 hmU hsmall z _ hh (stateSignU z) (stateSignV z)
    (fun b => (stateSignU_abs z b).le) (fun b => (stateSignV_abs z b).le)
  simpa only [SourceLatticeSetup.frame,sourceCanonicalFrame,CanonicalFrame.field,CanonicalFrame.u,CanonicalFrame.v,
    canonicalSourceProfile,intervalCenter,add_comm rplus rminus] using he

theorem source_axis_K_holder_second (S : SourceLatticeSetup D alpha beta rminus rplus)
    (map : ℝ × ℝ → ℝ) (k0 : ℝ) (V : Set (ℝ × ℝ)) (hV : IsOpen V)
    (hV0 : (0:ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V)
    (haxis : ∀ u : ℝ, (u,0) ∈ V  →  map (u,0)=k0) :
    ∃ eta C : ℝ, 0<eta ∧ 0<C ∧
      ∀ (N J M : ℕ) (hN : 0<N) (epsilonU epsilonV delta : ℝ),
      ∀ (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0<delta)
        (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
      let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      F.Au+F.Av ≤ eta  →  ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
        ContDiff ℝ ∞ (fun x => map ((F.field z).u x,(F.field z).v x)-k0) ∧
          Model.holderNorm (fun x => map ((F.field z).u x,(F.field z).v x)-k0) beta ≤ 
            ENNReal.ofReal (C*epsilonV) := by
  have hinner (x : Model.Covariate (D+1)) : innerBump (D+1) x ∈ Icc (0:ℝ) 1 :=
    ⟨(innerBump (D+1)).nonneg,(innerBump (D+1)).le_one⟩
  obtain ⟨eta,C,heta,hC,hbound⟩ := canonical_source_K_holder_second canonicalStep D
    (sourceGateOrder alpha beta) (sourceJetBudget alpha beta)
    (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta) (sourceAlpha0 alpha beta)
    S.gamma_bounds.1 S.gamma_bounds.2.1 (zero_lt_one.trans_le S.lambda_ge_one)
    S.alpha0_pos.le (sourceAlpha0_lt_one alpha beta) (sourceJetBudget_pos alpha beta)
    (sourceJetBudget_le_twice_order alpha beta) rminus rplus S.lower_pos S.interval
    (innerBump (D+1)) (outerBump (D+1)) (outerBump_one_on_inner (D+1))
    (innerBump_zero_outside (D+1)) (outerBump_zero_outside (D+1))
    (innerBump_smooth (D+1)) (innerBump_compact (D+1)) hinner (innerBump_tsupport_subset (D+1))
    alpha beta (sourceAlpha0_lt_beta alpha beta S.beta_pos)
    (source_beta_derivative_budget alpha beta S.beta_pos) S.v0 S.volume_pos map k0 V hV hV0 hmap haxis
  refine ⟨eta,C,heta,hC,?_⟩
  intro N J M hN epsilonU epsilonV delta heU heV hd hmargin
  dsimp only
  intro hsmall z
  have hm0 : (2:ℝ)^((J:ℝ)*sourceAlpha0 alpha beta) ≤ sourceFineScale J (min alpha beta) := by
    unfold sourceFineScale
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (le_min (sourceAlpha0_lt_alpha alpha beta S.alpha_pos).le (sourceAlpha0_lt_beta alpha beta S.beta_pos).le)
      (Nat.cast_nonneg J)
  have hmV : sourceFineScale J (min alpha beta) ≤ (2:ℝ)^((J:ℝ)*beta) := by
    unfold sourceFineScale
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg J))
  have hh : (rplus-rminus)/2-delta ∈ Icc (-intervalHalfWidth rminus rplus) (intervalHalfWidth rminus rplus) := by
    have he := hmargin.trans (min_le_left _ _)
    unfold intervalHalfWidth
    constructor <;> linarith
  have he := hbound N (sourceGridOffset S.v0 (D+1)) (sourceGridCount N (D+1))
    (sourceFixedBaseline (D+1) S.v0 rminus rplus) epsilonU epsilonV (sourceGridCount_pos N (D+1) hN)
    heU heV (sourceBlockScale_grid_le_one S.v0 N (D+1) S.volume_pos S.volume_le_one hN)
    J M _ hm0 hmV hsmall z _ hh (stateSignU z) (stateSignV z)
    (fun b => (stateSignU_abs z b).le) (fun b => (stateSignV_abs z b).le)
  simpa only [SourceLatticeSetup.frame,sourceCanonicalFrame,CanonicalFrame.field,CanonicalFrame.u,CanonicalFrame.v,
    canonicalSourceProfile,intervalCenter,add_comm rplus rminus] using he

end RoughRegime.LatticePriors
