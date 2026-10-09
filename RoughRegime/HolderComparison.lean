module

public import RoughRegime.HolderModulus
public import RoughRegime.HolderRegularity


@[expose] public section
/-! The lower-exponent comparison used in the localization lemma, for the
actual coordinate Hölder norm on the closed unit cube. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

theorem cube_norm_sub_le_dimension {d : ℕ} (x y : Covariate d)
    (hx : x ∈ cube d) (hy : y ∈ cube d) : ‖x-y‖ ≤ (d : ℝ) := by
  classical
  have he : x-y = ∑ i : Fin d, (x i-y i) • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [he]
  calc
    _ ≤ ∑ i : Fin d, ‖(x i-y i) • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_smul,Real.norm_eq_abs,PiLp.norm_single,norm_one,mul_one]
      rw [abs_le]
      exact ⟨by linarith [(hx i).1,(hy i).2],by linarith [(hx i).2,(hy i).1]⟩
    _ = (d : ℝ) := by simp

theorem coordinateDerivative_lipschitz_of_next_bound {d q : ℕ}
    (f : Covariate d → ℝ) (hf : ContDiff ℝ ∞ f) (H : ℝ) (hH : 0 ≤ H)
    (hb : ∀ (σ : Fin (q+1) → Fin d) x, x∈cube d → |coordinateDerivative f (q+1) σ x| ≤ H)
    (σ : Fin q → Fin d) (x y : Covariate d) (hx : x∈cube d) (hy : y∈cube d) :
    |coordinateDerivative f q σ x-coordinateDerivative f q σ y| ≤ (d : ℝ)*H*‖x-y‖ := by
  let v : Fin q → Covariate d := fun j => EuclideanSpace.single (σ j) 1
  let G : Covariate d → ℝ := fun z => iteratedFDeriv ℝ q f z v
  have hj : Differentiable ℝ (iteratedFDeriv ℝ q f) :=
    hf.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top q))
  have hG : Differentiable ℝ G := hj.continuousMultilinear_apply_const v
  have hd (z : Covariate d) (hz : z∈cube d) : ‖fderiv ℝ G z‖ ≤ (d : ℝ)*H := by
    apply linear_norm_le_coordinate_bound _ H hH
    intro i
    have hh := hb (Fin.cons i σ) z hz
    rw [coordinateDerivative_eq_iteratedFDeriv f (q+1) _ z hz (hf.of_le (by simp)).contDiffAt] at hh
    have hjet := (hj z).iteratedFDeriv_succ_apply_left'
      (m := @Fin.cons q (fun _ => Covariate d) (EuclideanSpace.single i (1 : ℝ)) v)
    have he : (fun j : Fin (q+1) => (EuclideanSpace.single ((@Fin.cons q (fun _ => Fin d) i σ) j) (1 : ℝ) : Covariate d)) =
        @Fin.cons q (fun _ => Covariate d) (EuclideanSpace.single i (1 : ℝ)) v := by
      funext j
      cases j using Fin.cases <;> simp [v]
    rw [he,hjet] at hh
    simpa only [Fin.tail_cons,Fin.cons_zero] using hh
  have hh := (convex_cube d).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hG z) hd hy hx
  rw [coordinateDerivative_eq_iteratedFDeriv f q σ x hx (hf.of_le (by simp)).contDiffAt,
    coordinateDerivative_eq_iteratedFDeriv f q σ y hy (hf.of_le (by simp)).contDiffAt]
  simpa only [G,v,Real.norm_eq_abs] using hh

private theorem small_power_le_dimension {d : ℕ} (hd : 1 ≤ d) {a e : ℝ}
    (ha : 0 < a) (had : a ≤ (d : ℝ)) (he : 0 ≤ e) (he1 : e ≤ 1) : a^e ≤ (d : ℝ) := by
  by_cases ha1 : a ≤ 1
  · exact (Real.rpow_le_one ha.le ha1 he).trans (by exact_mod_cast hd)
  · have hpow : a^e ≤ a := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ha1) he1
    exact hpow.trans had

theorem holderBall_lower_exponent {d : ℕ} (f : Covariate d → ℝ)
    (hf : ContDiff ℝ ∞ f) (t s H : ℝ) (ht : 0 < t) (hts : t ≤ s)
    (hH : 0 ≤ H) (hb : f ∈ holderBall s H) :
    f ∈ holderBall t (((d : ℝ)+1)*H) := by
  have hs : 0 < s := ht.trans_le hts
  have horder : holderOrder t ≤ holderOrder s := by
    unfold holderOrder
    exact Nat.sub_le_sub_right (Nat.ceil_mono hts) 1
  have hsup : derivativeSup f (holderOrder t) ≤ ENNReal.ofReal H := by
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    exact ENNReal.ofReal_le_ofReal
      (holderBall_coordinate_bound f s H hH hb q (hq.trans horder) σ x hx)
  have hsem : holderSeminorm f t ≤ ENNReal.ofReal ((d : ℝ)*H) := by
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    have hdist : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hd : 1 ≤ d := by
      by_contra h
      have hd0 : d=0 := by omega
      subst d
      exact hxy (Subsingleton.elim _ _)
    apply ENNReal.ofReal_le_ofReal
    by_cases heq : holderOrder t=holderOrder s
    · have hfrac := holderBall_coordinate_modulus f s H hH hb (heq ▸ σ) x y hx hy
      have hexp : 0 ≤ holderExponent s-holderExponent t := by
        unfold holderExponent
        rw [heq]
        linarith
      have hexp1 : holderExponent s-holderExponent t ≤ 1 := by
        linarith [holderExponent_pos ht,holderExponent_le_one hs]
      have hpow := small_power_le_dimension hd hdist (cube_norm_sub_le_dimension x y hx hy) hexp hexp1
      have he : ‖x-y‖^holderExponent s =
          ‖x-y‖^holderExponent t * ‖x-y‖^(holderExponent s-holderExponent t) := by
        rw [← Real.rpow_add hdist]
        congr 1
        ring
      have hfrac' : |coordinateDerivative f (holderOrder t) σ x-coordinateDerivative f (holderOrder t) σ y| ≤
          H*‖x-y‖^holderExponent s := by
        have htransport (q r : ℕ) (h : q=r) (τ : Fin q → Fin d) (z : Covariate d) :
            coordinateDerivative f r (h ▸ τ) z = coordinateDerivative f q τ z := by
          subst r
          rfl
        have hc (z : Covariate d) := htransport _ _ heq σ z
        simpa only [hc] using hfrac
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hdist _)).mpr
      rw [he] at hfrac'
      nlinarith [mul_le_mul_of_nonneg_left hpow hH,
        Real.rpow_pos_of_pos hdist (holderExponent t)]
    · have hnext : holderOrder t+1 ≤ holderOrder s := by omega
      have hLip := coordinateDerivative_lipschitz_of_next_bound f hf H hH
        (fun τ z hz => holderBall_coordinate_bound f s H hH hb _ hnext τ z hz) σ x y hx hy
      by_cases hd1 : d=1
      · have hdist1 : ‖x-y‖ ≤ 1 := by simpa [hd1] using cube_norm_sub_le_dimension x y hx hy
        have hp : ‖x-y‖ ≤ ‖x-y‖^holderExponent t := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hdist hdist1 (holderExponent_le_one ht)
        apply (div_le_iff₀ (Real.rpow_pos_of_pos hdist _)).mpr
        exact hLip.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg _) hH))
      · have htwo : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 2 ≤ d by omega)
        have hxB := holderBall_coordinate_bound f s H hH hb _ horder σ x hx
        have hyB := holderBall_coordinate_bound f s H hH hb _ horder σ y hy
        have hbound : |coordinateDerivative f (holderOrder t) σ x-coordinateDerivative f (holderOrder t) σ y| ≤ 2*H :=
          (abs_sub _ _).trans (by linarith)
        have hh := holder_ratio_le hdist (holderExponent_pos ht).le (holderExponent_le_one ht)
          (by positivity : 0 ≤ 2*H) (by positivity : 0 ≤ (d : ℝ)*H) hbound hLip
        simpa only [max_eq_right (mul_le_mul_of_nonneg_right htwo hH)] using hh
  change holderNorm f t ≤ _
  rw [holderNorm,ite_eq_left ⟨ht,(hf.of_le (by simp)).contDiffOn⟩]
  calc
    _ ≤ ENNReal.ofReal H+ENNReal.ofReal ((d : ℝ)*H) := add_le_add hsup hsem
    _ = ENNReal.ofReal (((d : ℝ)+1)*H) := by
      rw [← ENNReal.ofReal_add hH (by positivity)]
      congr 1
      ring

end RoughRegime.Model
