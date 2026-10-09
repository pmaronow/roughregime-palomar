module

public import RoughRegime.HolderRegularity
public import RoughRegime.HolderModulus
public import RoughRegime.LatticeScales
public import RoughRegime.LatticeConstruction


@[expose] public section
/-! Hölder interpolation and the source's uniformly summable hierarchical scales. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace RoughRegime.Model

/-- Interpolation after rescaling the spatial distance by L. -/
lemma holder_ratio_scaled_le {a s γ A B L : ℝ} (hs : 0 < s) (hL : 0 < L)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haA : a ≤ A) (haB : a ≤ B * (L * s)) :
    a / s ^ γ ≤ max A B * L ^ γ := by
  have h := holder_ratio_le (mul_pos hL hs) hγ hγ1 hA hB haA haB
  have hp := (div_le_iff₀ (Real.rpow_pos_of_pos (mul_pos hL hs) γ)).mp h
  rw [Real.mul_rpow hL.le hs.le] at hp
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hs γ)).mpr
  nlinarith

/-- The norm of a smooth function whose q-th derivative is bounded by A L^q
is at most3 A L^t. This retains the fractional Hölder exponent. -/
theorem holderNorm_le_of_scaled_iteratedFDeriv_bound {d : ℕ}
    (f : Covariate d → ℝ) (t : ℝ) (ht : 0 < t) (hf : ContDiff ℝ ∞ f)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hb : ∀ q, q ≤ holderOrder t + 1 → ∀ x ∈ cube d,
      ‖iteratedFDeriv ℝ q f x‖ ≤ A * L ^ q) :
    holderNorm f t ≤ ENNReal.ofReal (3 * A * L ^ t) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hc : ∀ q (σ : Fin q → Fin d) x, x ∈ cube d →
      coordinateDerivative f q σ x =
        iteratedFDeriv ℝ q f x (fun j => EuclideanSpace.single (σ j) 1) := by
    intro q σ x hx
    exact coordinateDerivative_eq_iteratedFDeriv f q σ x hx (hf.of_le (by simp)).contDiffAt
  have hk : (holderOrder t : ℝ) ≤ t := by
    have h := holderExponent_pos ht
    unfold holderExponent at h
    linarith
  have hpow (q : ℕ) (hq : q ≤ holderOrder t) : L ^ q ≤ L ^ t := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL ((Nat.cast_le.mpr hq).trans hk)
  have hsup : derivativeSup f (holderOrder t) ≤ ENNReal.ofReal (A * L ^ t) := by
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
    have hh := (iteratedFDeriv ℝ q f x).le_opNorm (fun j => EuclideanSpace.single (σ j) (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hh
    exact hh.trans ((hb q (by omega) x hx).trans (mul_le_mul_of_nonneg_left (hpow q hq) hA))
  have hsem : holderSeminorm f t ≤ ENNReal.ofReal (2 * A * L ^ t) := by
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
    have hpoint : |coordinateDerivative f k σ x - coordinateDerivative f k σ y| ≤ ‖G x - G y‖ := by
      rw [hc k σ x hx, hc k σ y hy, ← Real.norm_eq_abs]
      have hh := (G x - G y).le_opNorm (fun j => EuclideanSpace.single (σ j) (1 : ℝ))
      simpa [G, PiLp.norm_single] using hh
    have hnorm : ‖G x - G y‖ ≤ 2 * A * L ^ k :=
      (norm_sub_le _ _).trans (by nlinarith [hb k (by omega) x hx, hb k (by omega) y hy])
    have hlip : ‖G x - G y‖ ≤ (A * L ^ (k + 1)) * ‖x - y‖ := by
      apply (convex_cube d).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (hf.differentiable_iteratedFDeriv (m := k)
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))).differentiableAt) _ hy hx
      intro z hz
      rw [norm_fderiv_iteratedFDeriv]
      exact hb (k + 1) le_rfl z hz
    have hs : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hscaled : |coordinateDerivative f k σ x - coordinateDerivative f k σ y| ≤
        (A * L ^ k) * (L * ‖x - y‖) := by
      have hh := hpoint.trans hlip
      convert hh using 1
      ring
    have hh := holder_ratio_scaled_le hs hL0 (holderExponent_pos ht).le (holderExponent_le_one ht)
      (by positivity : 0 ≤ 2 * A * L ^ k) (by positivity : 0 ≤ A * L ^ k)
      (hpoint.trans hnorm) hscaled
    have he : L ^ k * L ^ holderExponent t = L ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
      congr 1
      dsimp [k, holderExponent]
      ring
    rw [max_eq_left (by nlinarith [pow_nonneg hL0.le k] : A * L ^ k ≤ 2 * A * L ^ k)] at hh
    calc
      _ ≤ (2 * A * L ^ k) * L ^ holderExponent t := hh
      _ = _ := by rw [mul_assoc, he]
  have hreg : 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) :=
    ⟨ht, (hf.of_le (by simp)).contDiffOn⟩
  unfold holderNorm
  rw [ite_eq_left hreg]
  calc
    _ ≤ ENNReal.ofReal (A * L ^ t) + ENNReal.ofReal (2 * A * L ^ t) := add_le_add hsup hsem
    _ = ENNReal.ofReal (3 * A * L ^ t) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Finite sums of actual smooth Hölder functions have a bound independent of
 the number of summands, apart from the sum of their norms. -/
theorem holderNorm_sum_le {d : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → Covariate d → ℝ) (C : ι → ℝ) (t : ℝ) (ht : 0 < t)
    (hC : ∀ i ∈ S, 0 ≤ C i) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hbound : ∀ i ∈ S, holderNorm (f i) t ≤ ENNReal.ofReal (C i)) :
    holderNorm (fun x => ∑ i ∈ S, f i x) t ≤ ENNReal.ofReal (2 * ∑ i ∈ S, C i) := by
  have hsmooth : ContDiff ℝ ∞ (fun x => ∑ i ∈ S, f i x) := ContDiff.sum hf
  have hcoord (q : ℕ) (σ : Fin q → Fin d) (x : Covariate d) (hx : x ∈ cube d) :
      coordinateDerivative (fun x => ∑ i ∈ S, f i x) q σ x = ∑ i ∈ S, coordinateDerivative (f i) q σ x := by
    rw [coordinateDerivative_eq_iteratedFDeriv _ q σ x hx (hsmooth.of_le (by simp)).contDiffAt,
      iteratedFDeriv_fun_sum_apply (fun i hi => ((hf i hi).of_le (by simp)).contDiffAt)]
    rw [sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact (coordinateDerivative_eq_iteratedFDeriv (f i) q σ x hx ((hf i hi).of_le (by simp)).contDiffAt).symm
  have hsum0 : 0 ≤ ∑ i ∈ S, C i := Finset.sum_nonneg hC
  have hsup : derivativeSup (fun x => ∑ i ∈ S, f i x) (holderOrder t) ≤ ENNReal.ofReal (∑ i ∈ S, C i) := by
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply ENNReal.ofReal_le_ofReal
    rw [hcoord q σ x hx]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun i hi => holderBall_coordinate_bound (f i) t (C i)
      (hC i hi) (hbound i hi) q hq σ x hx)
  have hsem : holderSeminorm (fun x => ∑ i ∈ S, f i x) t ≤ ENNReal.ofReal (∑ i ∈ S, C i) := by
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).mpr
    rw [hcoord _ σ x hx, hcoord _ σ y hy, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => holderBall_coordinate_modulus (f i) t (C i)
      (hC i hi) (hbound i hi) σ x y hx hy)
  unfold holderNorm
  rw [ite_eq_left ⟨ht, (hsmooth.of_le (by simp)).contDiffOn⟩]
  calc
    _ ≤ ENNReal.ofReal (∑ i ∈ S, C i) + ENNReal.ofReal (∑ i ∈ S, C i) := add_le_add hsup hsem
    _ = _ := by rw [← ENNReal.ofReal_add hsum0 hsum0]; congr 1; ring

end RoughRegime.Model
