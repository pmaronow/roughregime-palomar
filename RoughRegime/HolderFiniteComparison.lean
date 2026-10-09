module

public import RoughRegime.HolderCalculus
public import RoughRegime.HolderComparison


@[expose] public section
/-! Lower-exponent comparison for the actual finite Hölder class on the
closed cube; no globally smooth extension is assumed. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def finiteLowerExponentConstant (d : ℕ) (s : ℝ) : ℝ:=
  (d:ℝ)+3+((d:ℝ)+1)^(holderOrder s+1)

theorem coordinateDerivative_lipschitz_finite {d : ℕ} (f : Covariate d→ℝ) (s H : ℝ)
    (hH : 0 ≤ H) (hf : f∈holderBall s H) (q : ℕ) (hq : q<holderOrder s)
    (σ : Fin q→Fin d) (x y : Covariate d) (hx : x∈cube d) (hy : y∈cube d) :
    |coordinateDerivative f q σ x-coordinateDerivative f q σ y| ≤
      holderJetConstant d s H*‖x-y‖ := by
  have hr:=holderBall_regular f s H hf
  have hd:=hr.2.differentiableOn_iteratedFDerivWithin (m:=q) (by exact_mod_cast hq) (uniqueDiffOn_cube d)
  have hlip:‖iteratedFDerivWithin ℝ q f (cube d) x-iteratedFDerivWithin ℝ q f (cube d) y‖ ≤
      holderJetConstant d s H*‖x-y‖:=
    (convex_cube d).norm_image_sub_le_of_norm_fderivWithin_le hd
      (fun z hz=>by rw [norm_fderivWithin_iteratedFDerivWithin]
                    exact holderBall_jet_bound_uniform f s H hH hf (q+1) (by omega) z hz) hy hx
  have hh:=(iteratedFDerivWithin ℝ q f (cube d) x-iteratedFDerivWithin ℝ q f (cube d) y).le_opNorm
    (fun j=>EuclideanSpace.single (σ j) (1:ℝ))
  have hc:|coordinateDerivative f q σ x-coordinateDerivative f q σ y| ≤
      ‖iteratedFDerivWithin ℝ q f (cube d) x-iteratedFDerivWithin ℝ q f (cube d) y‖:=by
    simpa only [coordinateDerivative,sub_apply,Real.norm_eq_abs,
      PiLp.norm_single,norm_one,Finset.prod_const_one,mul_one] using hh
  exact hc.trans hlip

theorem holderBall_lower_exponent_finite {d : ℕ} (f : Covariate d→ℝ)
    (t s H : ℝ) (ht : 0<t) (hts : t ≤ s) (hH : 0 ≤ H) (hf : f∈holderBall s H) :
    f∈holderBall t (finiteLowerExponentConstant d s*H) := by
  have hr:=holderBall_regular f s H hf
  have horder:holderOrder t ≤ holderOrder s:=by
    unfold holderOrder;exact Nat.sub_le_sub_right (Nat.ceil_mono hts) 1
  let J:ℝ:=((d:ℝ)+1)^(holderOrder s+1)
  have hJ:0 ≤ J:=by dsimp [J];positivity
  have hsup:derivativeSup f (holderOrder t) ≤ ENNReal.ofReal H:=by
    apply iSup_le;intro q
    apply iSup_le;intro hq
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    exact ENNReal.ofReal_le_ofReal (holderBall_coordinate_bound f s H hH hf q (hq.trans horder) σ x hx)
  have hsem:holderSeminorm f t ≤ ENNReal.ofReal (((d:ℝ)+2+J)*H):=by
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    apply iSup_le;intro y
    apply iSup_le;intro hy
    apply iSup_le;intro hxy
    have hd:1 ≤ d:=by
      by_contra h
      have hd0:d=0:=by omega
      subst d;exact hxy (Subsingleton.elim _ _)
    have hdist:0<‖x-y‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    apply ENNReal.ofReal_le_ofReal
    by_cases heq:holderOrder t=holderOrder s
    · have hfrac:=holderBall_coordinate_modulus f s H hH hf (heq ▸ σ) x y hx hy
      have hexp:0 ≤ holderExponent s-holderExponent t:=by
        unfold holderExponent;rw [heq];linarith
      have hexp1:holderExponent s-holderExponent t ≤ 1:=by
        linarith [holderExponent_pos ht,holderExponent_le_one hr.1]
      have hpow:‖x-y‖^(holderExponent s-holderExponent t) ≤ (d:ℝ):=by
        by_cases hdist1:‖x-y‖ ≤ 1
        · exact (Real.rpow_le_one hdist.le hdist1 hexp).trans (by exact_mod_cast hd)
        · have hpow':‖x-y‖^(holderExponent s-holderExponent t) ≤ ‖x-y‖:=by
            simpa only [Real.rpow_one] using
              Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hdist1) hexp1
          exact hpow'.trans (cube_norm_sub_le_dimension x y hx hy)
      have hp:‖x-y‖^holderExponent s=
          ‖x-y‖^holderExponent t*‖x-y‖^(holderExponent s-holderExponent t):=by
        rw [← Real.rpow_add hdist];congr 1;ring
      have hfrac':|coordinateDerivative f (holderOrder t) σ x-coordinateDerivative f (holderOrder t) σ y| ≤
          H*‖x-y‖^holderExponent s:=by
        have htransport (q r:ℕ) (he:q=r) (τ:Fin q→Fin d) (z:Covariate d):
            coordinateDerivative f r (he ▸ τ) z=coordinateDerivative f q τ z:=by subst r;rfl
        simpa only [htransport _ _ heq σ x,htransport _ _ heq σ y] using hfrac
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hdist _)).mpr
      rw [hp] at hfrac'
      have hscaled:=mul_le_mul_of_nonneg_left hpow hH
      have hc:(d:ℝ)*H ≤ ((d:ℝ)+2+J)*H:=by nlinarith
      nlinarith [Real.rpow_pos_of_pos hdist (holderExponent t)]
    · have hq:holderOrder t<holderOrder s:=by omega
      have hlip:=coordinateDerivative_lipschitz_finite f s H hH hf _ hq σ x y hx hy
      have hxB:=holderBall_coordinate_bound f s H hH hf _ horder σ x hx
      have hyB:=holderBall_coordinate_bound f s H hH hf _ horder σ y hy
      have hb:|coordinateDerivative f (holderOrder t) σ x-coordinateDerivative f (holderOrder t) σ y| ≤ 2*H:=
        (abs_sub _ _).trans (by linarith)
      have hh:=holder_ratio_le hdist (holderExponent_pos ht).le (holderExponent_le_one ht)
        (by positivity : 0 ≤ 2*H) (holderJetConstant_nonneg d s H hH) hb hlip
      apply hh.trans
      apply max_le
      · nlinarith
      · change J*H ≤ ((d:ℝ)+2+J)*H
        nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  change holderNorm f t ≤ _
  rw [holderNorm,ite_eq_left ⟨ht,hr.2.of_le (by exact_mod_cast horder)⟩]
  calc
    _ ≤ ENNReal.ofReal H+ENNReal.ofReal (((d:ℝ)+2+J)*H):=add_le_add hsup hsem
    _ = ENNReal.ofReal (finiteLowerExponentConstant d s*H):=by
      rw [← ENNReal.ofReal_add hH (by positivity)]
      congr 1;dsimp [finiteLowerExponentConstant,J];ring

end RoughRegime.Model
