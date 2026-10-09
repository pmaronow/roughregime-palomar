module

public import RoughRegime.DisjointHolder


@[expose] public section
/-! Actual Hölder control under scalar amplitudes. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Model

theorem holderNorm_const_mul_le {d : ℕ} (f : Covariate d → ℝ) (t H A : ℝ)
    (ht : 0<t) (hH : 0≤H) (hf : ContDiff ℝ ∞ f)
    (hb : holderNorm f t ≤ ENNReal.ofReal H) :
    holderNorm (fun x => A*f x) t ≤ ENNReal.ofReal (2*|A| * H) := by
  have hsmooth : ContDiff ℝ ∞ (fun x => A*f x) := contDiff_const.mul hf
  have hcoord (q : ℕ) (σ : Fin q → Fin d) (x : Covariate d) (hx : x∈cube d) :
      coordinateDerivative (fun x => A*f x) q σ x=A*coordinateDerivative f q σ x := by
    rw [coordinateDerivative_eq_iteratedFDeriv _ q σ x hx (hsmooth.of_le (by simp)).contDiffAt,
      coordinateDerivative_eq_iteratedFDeriv f q σ x hx (hf.of_le (by simp)).contDiffAt]
    change (iteratedFDeriv ℝ q (A • f) x) _ = _
    rw [iteratedFDeriv_const_smul_apply (hf.of_le (by simp)).contDiffAt]
    rfl
  have hsup : derivativeSup (fun x => A*f x) (holderOrder t) ≤ ENNReal.ofReal (|A| * H) := by
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply ENNReal.ofReal_le_ofReal
    rw [hcoord q σ x hx,abs_mul]
    exact mul_le_mul_of_nonneg_left (holderBall_coordinate_bound f t H hH hb q hq σ x hx) (abs_nonneg A)
  have hsem : holderSeminorm (fun x => A*f x) t ≤ ENNReal.ofReal (|A| * H) := by
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    apply ENNReal.ofReal_le_ofReal
    have hpow : 0<‖x-y‖^holderExponent t := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    apply (div_le_iff₀ hpow).mpr
    rw [hcoord _ σ x hx,hcoord _ σ y hy,← mul_sub,abs_mul]
    exact (mul_le_mul_of_nonneg_left (holderBall_coordinate_modulus f t H hH hb σ x y hx hy) (abs_nonneg A)).trans_eq (by ring)
  unfold holderNorm
  rw [ite_eq_left ⟨ht,(hsmooth.of_le (by simp)).contDiffOn⟩]
  calc
    _ ≤ ENNReal.ofReal (|A| * H)+ENNReal.ofReal (|A| * H) := add_le_add hsup hsem
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end RoughRegime.Model
