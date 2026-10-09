module

public import RoughRegime.SourceLiteralFrame
public import RoughRegime.CanonicalHolder


@[expose] public section
/-! The literal source profiles, with one common Hölder constant before every
resolution, frequency, density margin, amplitude and realization. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.LatticePriors.SourceLatticeSetup
open RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)
include S

 theorem fine_above_alpha0 (J : ℕ) :
     (2:ℝ)^((J:ℝ)*sourceAlpha0 alpha beta) ≤ sourceFineScale J (min alpha beta) := by
   unfold sourceFineScale
   exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
     (mul_le_mul_of_nonneg_left (le_min (sourceAlpha0_lt_alpha _ _ S.alpha_pos).le
       (sourceAlpha0_lt_beta _ _ S.beta_pos).le) (Nat.cast_nonneg J))
 theorem fine_below_alpha (J : ℕ) : sourceFineScale J (min alpha beta) ≤ (2:ℝ)^((J:ℝ)*alpha) := by
   unfold sourceFineScale
   exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
     (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg J))
 theorem fine_below_beta (J : ℕ) : sourceFineScale J (min alpha beta) ≤ (2:ℝ)^((J:ℝ)*beta) := by
   unfold sourceFineScale
   exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
     (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg J))

 theorem holder_bound : ∃ C : ℝ, 1≤C ∧
     ∀ (N J M : ℕ) (hN : 0<N) (epsilonU epsilonV delta : ℝ)
       (heU : 0≤epsilonU) (heV : 0≤epsilonV) (hd : 0<delta)
       (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
     let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
     ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
       Model.holderNorm (F.u z) alpha ≤ ENNReal.ofReal (C*epsilonU) ∧
       Model.holderNorm (F.v z) beta ≤ ENNReal.ofReal (C*epsilonV) := by
   have hi01 (x : Model.Covariate (D+1)) : innerBump (D+1) x ∈ Icc (0:ℝ) 1 :=
     ⟨(innerBump (D+1)).nonneg,(innerBump (D+1)).le_one⟩
   obtain ⟨Cu,hCu,hU⟩ := canonical_source_profile_holder_bound canonicalStep D
     (sourceGateOrder alpha beta) (sourceJetBudget alpha beta)
     (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta) (sourceAlpha0 alpha beta)
     S.gamma_bounds.1 S.gamma_bounds.2.1 (zero_lt_one.trans_le S.lambda_ge_one)
     S.alpha0_pos.le (sourceAlpha0_lt_one _ _) (sourceJetBudget_pos _ _) (sourceJetBudget_le_twice_order _ _)
     rminus rplus S.lower_pos S.interval (innerBump (D+1)) (outerBump (D+1))
     (outerBump_one_on_inner _) (innerBump_zero_outside _) (outerBump_zero_outside _)
     (innerBump_smooth _) (innerBump_compact _) hi01 (innerBump_tsupport_subset _)
     alpha (sourceAlpha0_lt_alpha _ _ S.alpha_pos) (source_alpha_derivative_budget _ _ S.alpha_pos) S.v0 S.volume_pos
   obtain ⟨Cv,hCv,hV⟩ := canonical_source_profile_holder_bound canonicalStep D
     (sourceGateOrder alpha beta) (sourceJetBudget alpha beta)
     (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta) (sourceAlpha0 alpha beta)
     S.gamma_bounds.1 S.gamma_bounds.2.1 (zero_lt_one.trans_le S.lambda_ge_one)
     S.alpha0_pos.le (sourceAlpha0_lt_one _ _) (sourceJetBudget_pos _ _) (sourceJetBudget_le_twice_order _ _)
     rminus rplus S.lower_pos S.interval (innerBump (D+1)) (outerBump (D+1))
     (outerBump_one_on_inner _) (innerBump_zero_outside _) (outerBump_zero_outside _)
     (innerBump_smooth _) (innerBump_compact _) hi01 (innerBump_tsupport_subset _)
     beta (sourceAlpha0_lt_beta _ _ S.beta_pos) (source_beta_derivative_budget _ _ S.beta_pos) S.v0 S.volume_pos
   let C := max 1 (max Cu Cv)
   have huC : Cu≤C := (le_max_left _ _).trans (le_max_right _ _)
   have hvC : Cv≤C := (le_max_right _ _).trans (le_max_right _ _)
   refine ⟨C,le_max_left _ _,?_⟩
   intro N J M hN epsilonU epsilonV delta heU heV hd hmargin
   dsimp only
   let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
   intro z
   have hB := sourceGridCount_pos N (D+1) hN
   have hell := sourceBlockScale_grid_le_one S.v0 N (D+1) S.volume_pos S.volume_le_one hN
   have hh : (rplus-rminus)/2-delta ∈ Icc (-intervalHalfWidth rminus rplus) (intervalHalfWidth rminus rplus) := by
     have he := hmargin.trans (min_le_left _ _)
     unfold intervalHalfWidth
     constructor <;> linarith
   have hu := hU N (sourceGridOffset S.v0 (D+1)) (sourceGridCount N (D+1))
     (sourceFixedBaseline (D+1) S.v0 rminus rplus) epsilonU hB heU hell J M _
     (S.fine_above_alpha0 J) (S.fine_below_alpha J) z _ hh (stateSignU z)
     (fun b=>(stateSignU_abs z b).le)
   have hv := hV N (sourceGridOffset S.v0 (D+1)) (sourceGridCount N (D+1))
     (sourceFixedBaseline (D+1) S.v0 rminus rplus) epsilonV hB heV hell J M _
     (S.fine_above_alpha0 J) (S.fine_below_beta J) z _ hh (stateSignV z)
     (fun b=>(stateSignV_abs z b).le)
   constructor
   · have he : Model.holderNorm (F.u z) alpha ≤ ENNReal.ofReal (Cu*epsilonU) := by
       simpa only [F,frame,sourceCanonicalFrame,CanonicalFrame.u,intervalCenter,add_comm rplus rminus] using hu
     exact he.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right huC heU))
   · have he : Model.holderNorm (F.v z) beta ≤ ENNReal.ofReal (Cv*epsilonV) := by
       simpa only [F,frame,sourceCanonicalFrame,CanonicalFrame.v,intervalCenter,add_comm rplus rminus] using hv
     exact he.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hvC heV))

end RoughRegime.LatticePriors.SourceLatticeSetup
