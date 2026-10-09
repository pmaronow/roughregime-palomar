module

public import RoughRegime.SourceRealizationHolder
public import RoughRegime.CanonicalKHolder


@[expose] public section
/-! The unrestricted smooth-map clause of the literal source construction. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

 theorem source_unrestricted_K_holder {D : ℕ} {alpha beta rminus rplus : ℝ}
    (S : SourceLatticeSetup D alpha beta rminus rplus)
    (map : ℝ×ℝ → ℝ) (V : Set (ℝ×ℝ)) (hV : IsOpen V) (hV0 : (0:ℝ×ℝ)∈V)
    (hmap : ContDiffOn ℝ ∞ map V) :
    ∃ eta C : ℝ, 0<eta ∧ 0<C ∧
      ∀ (N J M : ℕ) (hN : 0 < N) (epsilonU epsilonV delta : ℝ)
        (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
        (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus),
      let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      F.Au+F.Av ≤ eta → ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
        ContDiff ℝ ∞ (fun x=>map ((F.field z).u x,(F.field z).v x)-map 0) ∧
        Model.holderNorm (fun x=>map ((F.field z).u x,(F.field z).v x)-map 0) (min alpha beta) ≤
          ENNReal.ofReal (C*(epsilonU+epsilonV)) := by
  have hinner (x : Model.Covariate (D+1)) : innerBump (D+1) x ∈ Icc (0:ℝ) 1 :=
    ⟨(innerBump (D+1)).nonneg,(innerBump (D+1)).le_one⟩
  have horder : Model.holderOrder (min alpha beta)≤Model.holderOrder alpha :=
    Nat.sub_le_sub_right (Nat.ceil_mono (min_le_left _ _)) 1
  have hbudget := (Nat.add_le_add_right horder 2).trans (source_alpha_derivative_budget alpha beta S.alpha_pos)
  obtain ⟨eta,C,heta,hC,hbound⟩ := canonical_source_K_holder_min canonicalStep D
    (sourceGateOrder alpha beta) (sourceJetBudget alpha beta)
    (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta) (sourceAlpha0 alpha beta)
    S.gamma_bounds.1 S.gamma_bounds.2.1 (zero_lt_one.trans_le S.lambda_ge_one)
    S.alpha0_pos.le (sourceAlpha0_lt_one alpha beta) (sourceJetBudget_pos alpha beta)
    (sourceJetBudget_le_twice_order alpha beta) rminus rplus S.lower_pos S.interval
    (innerBump (D+1)) (outerBump (D+1)) (outerBump_one_on_inner (D+1))
    (innerBump_zero_outside (D+1)) (outerBump_zero_outside (D+1))
    (innerBump_smooth (D+1)) (innerBump_compact (D+1)) hinner (innerBump_tsupport_subset (D+1))
    alpha beta (lt_min (sourceAlpha0_lt_alpha alpha beta S.alpha_pos)
      (sourceAlpha0_lt_beta alpha beta S.beta_pos)) hbudget S.v0 S.volume_pos map V hV hV0 hmap
  refine ⟨eta,C,heta,hC,?_⟩
  intro N J M hN epsilonU epsilonV delta heU heV hd hmargin
  dsimp only
  intro hsmall z
  have hB : (1:ℝ) ≤ sourceGridCount N (D+1) := by
    unfold sourceGridCount
    exact_mod_cast (Nat.one_le_pow _ _ (show 0<2*N by omega))
  have hh : (rplus-rminus)/2-delta ∈ Icc (-intervalHalfWidth rminus rplus) (intervalHalfWidth rminus rplus) := by
    have he := hmargin.trans (min_le_left _ _)
    unfold intervalHalfWidth
    constructor <;> linarith
  have he := hbound N (sourceGridOffset S.v0 (D+1)) (sourceGridCount N (D+1))
    (sourceFixedBaseline (D+1) S.v0 rminus rplus) epsilonU epsilonV hB heU heV
    (sourceBlockScale_grid_le_one S.v0 N (D+1) S.volume_pos S.volume_le_one hN)
    J M _ (S.fine_above_alpha0 J) le_rfl hsmall z _ hh (stateSignU z) (stateSignV z)
    (fun b=>(stateSignU_abs z b).le) (fun b=>(stateSignV_abs z b).le)
  have hz : (0:ℝ×ℝ)=(0,0) := by ext <;> rfl
  rw [hz]
  simpa only [SourceLatticeSetup.frame,sourceCanonicalFrame,CanonicalFrame.field,CanonicalFrame.u,CanonicalFrame.v,
    canonicalSourceProfile,intervalCenter,add_comm rplus rminus] using he

end RoughRegime.LatticePriors
