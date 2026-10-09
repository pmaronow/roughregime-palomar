module

public import RoughRegime.DesignHilbert


@[expose] public section
/-! Bessel's inequality for the actual cell moment vectors. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]

def designMoment (μ : Measure X) (g : X → ℝ) (z : n → X → ℝ) (f : X → ℝ) : n → ℝ :=
  fun i => ∫ x, g x * z i x * f x ∂μ

 theorem designLp_orthonormal (μ : Measure X) [IsFiniteMeasure μ]
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hb : ∀ i x, |z i x| ≤ B)
    (ho : ∀ i j, (∫ x, z i x * z j x ∂μ) = if i = j then 1 else 0) :
    Orthonormal ℝ (fun i => designLp μ (z i) (hz i) B (hb i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [designLp_inner]
  exact ho i j

/-- The genuine moment vector satisfies the source Bessel estimate. -/
 theorem designMoment_norm_le (μ : Measure X) [IsProbabilityMeasure μ]
    (g f : X → ℝ) (hg : Measurable g) (hf : Measurable f)
    (G H : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hgB : ∀ᵐ x ∂μ, |g x| ≤ G) (hfB : ∀ᵐ x ∂μ, |f x| ≤ H)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hb : ∀ i x, |z i x| ≤ B)
    (ho : ∀ i j, (∫ x, z i x * z j x ∂μ) = if i = j then 1 else 0) :
    ‖WithLp.toLp 2 (designMoment μ g z f)‖ ≤ G * H := by
  have htf : MemLp (fun x => g x * f x) 2 μ := by
    apply MemLp.of_bound (hg.mul hf).aestronglyMeasurable (G * H)
    filter_upwards [hgB, hfB] with x hgx hfx
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hgx hfx (abs_nonneg _) hG
  let tf := htf.toLp (fun x => g x * f x)
  let zz := fun i => designLp μ (z i) (hz i) B (hb i)
  have hinner (i : n) : inner ℝ (zz i) tf = designMoment μ g z f i := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [designLp_ae μ (z i) (hz i) B (hb i), htf.coeFn_toLp] with x hzx htfx
    change inner ℝ ((zz i) x) (tf x) = _
    dsimp only [zz, tf] at *
    simp [hzx, htfx, mul_comm, mul_left_comm, mul_assoc]
  have hbe := (designLp_orthonormal μ z hz B hb ho).sum_inner_products_le tf (s := Finset.univ)
  have hnorm : ‖tf‖ ≤ G * H := by
    have ht := Lp.norm_le_of_ae_bound (f := tf) (mul_nonneg hG hH) (by
      filter_upwards [htf.coeFn_toLp, hgB, hfB] with x htx hgx hfx
      dsimp only [tf] at *
      rw [htx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hgx hfx (abs_nonneg _) hG)
    simpa [measureUnivNNReal] using ht
  have hs : ‖WithLp.toLp 2 (designMoment μ g z f)‖ ^ 2 ≤ ‖tf‖ ^ 2 := by
    change (∑ i, ‖inner ℝ (zz i) tf‖ ^ 2) ≤ ‖tf‖ ^ 2 at hbe
    simpa only [PiLp.norm_sq_eq_of_L2, hinner] using hbe
  have ht := (sq_le_sq₀ (norm_nonneg tf) (mul_nonneg hG hH)).mpr hnorm
  have hh := hs.trans ht
  nlinarith [norm_nonneg (WithLp.toLp 2 (designMoment μ g z f)), mul_nonneg hG hH]

end RoughRegime.Model
