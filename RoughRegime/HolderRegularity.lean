module

public import RoughRegime.HolderGeometry


@[expose] public section
/-! Actual Hölder norm bounds from smooth derivatives on the cube. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

lemma holder_ratio_le {a s γ A B : ℝ} (hs : 0 < s) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (haA : a ≤ A) (haB : a ≤ B * s) :
    a / s ^ γ ≤ max A B := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hs γ)).mpr
  by_cases hs1 : s ≤ 1
  · have hp : s ≤ s ^ γ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hs hs1 hγ1
    exact haB.trans ((mul_le_mul_of_nonneg_left hp hB).trans
      (mul_le_mul_of_nonneg_right (le_max_right A B) (Real.rpow_nonneg hs.le γ)))
  · have hp : 1 ≤ s ^ γ := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hs1) hγ
    exact haA.trans ((le_max_left A B).trans
      (le_mul_of_one_le_right (le_trans hA (le_max_left A B)) hp))

theorem holderNorm_le_of_iteratedFDeriv_bound {d : ℕ} (f : Covariate d → ℝ)
    (t : ℝ) (ht : 0 < t) (hf : ContDiff ℝ ∞ f) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ q, q ≤ holderOrder t + 1 → ∀ x ∈ cube d, ‖iteratedFDeriv ℝ q f x‖ ≤ B) :
    holderNorm f t ≤ ENNReal.ofReal (3 * B) := by
  have hc : ∀ q (σ : Fin q → Fin d) x, x ∈ cube d →
      coordinateDerivative f q σ x =
        iteratedFDeriv ℝ q f x (fun j => EuclideanSpace.single (σ j) 1) := by
    intro q σ x hx
    exact coordinateDerivative_eq_iteratedFDeriv f q σ x hx
      (hf.of_le (by simp)).contDiffAt
  have hsup : derivativeSup f (holderOrder t) ≤ ENNReal.ofReal B := by
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    apply iSup_le
    intro σ
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply ENNReal.ofReal_le_ofReal
    rw [hc q σ x hx, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖iteratedFDeriv ℝ q f x‖ * ∏ j, ‖EuclideanSpace.single (σ j) (1 : ℝ)‖ :=
        (iteratedFDeriv ℝ q f x).le_opNorm _
      _ ≤ B := by
        simpa only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one]
          using (hb q (by omega) x hx)
  have hsem : holderSeminorm f t ≤ ENNReal.ofReal (2 * B) := by
    apply iSup_le
    intro σ
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    apply iSup_le
    intro hxy
    apply ENNReal.ofReal_le_ofReal
    let k := holderOrder t
    let G := iteratedFDeriv ℝ k f
    have hpoint : |coordinateDerivative f k σ x - coordinateDerivative f k σ y| ≤
        ‖G x - G y‖ := by
      rw [hc k σ x hx, hc k σ y hy, ← Real.norm_eq_abs]
      have hh := (G x - G y).le_opNorm (fun j => EuclideanSpace.single (σ j) (1 : ℝ))
      simpa [G, PiLp.norm_single] using hh
    have hnorm : ‖G x - G y‖ ≤ 2 * B := by
      exact (norm_sub_le _ _).trans (by nlinarith [hb k (by omega) x hx, hb k (by omega) y hy])
    have hlip : ‖G x - G y‖ ≤ B * ‖x - y‖ := by
      apply (convex_cube d).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (hf.differentiable_iteratedFDeriv (m := k)
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))).differentiableAt) _ hy hx
      intro z hz
      rw [norm_fderiv_iteratedFDeriv]
      exact hb (k + 1) le_rfl z hz
    have hs : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hh := holder_ratio_le hs (holderExponent_pos ht).le (holderExponent_le_one ht)
      (by positivity : 0 ≤ 2 * B) hB (hpoint.trans hnorm) (hpoint.trans hlip)
    simpa only [max_eq_left (by linarith : B ≤ 2 * B)] using hh
  have hreg : 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) :=
    ⟨ht, (hf.of_le (by simp)).contDiffOn⟩
  unfold holderNorm
  rw [ite_eq_left hreg]
  calc
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal (2 * B) := add_le_add hsup hsem
    _ = ENNReal.ofReal (3 * B) := by
      rw [← ENNReal.ofReal_add hB (by positivity)]
      congr 1
      ring

end RoughRegime.Model
