module

public import RoughRegime.ProjectionFrame
public import RoughRegime.Conditional
public import RoughRegime.Model


@[expose] public section
/-! Actual weighted Gram spectral bounds for finite bounded orthonormal
families under a normalized cell measure. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]

 def designGram (μ : Measure X) (g : X → ℝ) (z : n → X → ℝ) : Matrix n n ℝ :=
  fun i j => ∫ x, g x * z i x * z j x ∂μ
 def designCombination (z : n → X → ℝ) (v : n → ℝ) (x : X) : ℝ := ∑ i, v i * z i x

 omit [Fintype n] [DecidableEq n] in
 theorem design_product_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (G : ℝ) (hG : ∀ᵐ x ∂μ, |g x| ≤ G)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hB : 0 ≤ B)
    (hzB : ∀ i x, |z i x| ≤ B) (i j : n) :
    Integrable (fun x => g x * z i x * z j x) μ := by
  apply Integrable.of_bound ((hg.mul (hz i)).mul (hz j)).aestronglyMeasurable (G * B * B)
  filter_upwards [hG] with x hx
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx (hzB i x) (abs_nonneg _) (by linarith [abs_nonneg (g x)]))
    (hzB j x) (abs_nonneg _) (mul_nonneg (by linarith [abs_nonneg (g x)]) hB)

 omit [Fintype n] [DecidableEq n] in
 theorem designGram_isHermitian (μ : Measure X) (g : X → ℝ) (z : n → X → ℝ) :
    (designGram μ g z).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

 omit [DecidableEq n] in
 theorem designGram_bilinear (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (G : ℝ) (hG : ∀ᵐ x ∂μ, |g x| ≤ G)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hB : 0 ≤ B)
    (hzB : ∀ i x, |z i x| ≤ B) (v w : n → ℝ) :
    v ⬝ᵥ (designGram μ g z).mulVec w =
      ∫ x, g x * designCombination z v x * designCombination z w x ∂μ := by
  have hi (i j : n) := design_product_integrable μ g hg G hG z hz B hB hzB i j
  calc
    _ = ∑ i, ∑ j, (v i * w j) * (∫ x, g x * z i x * z j x ∂μ) := by
      simp only [dotProduct, mulVec, designGram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∫ x, ∑ i, ∑ j, (v i * w j) * (g x * z i x * z j x) ∂μ := by
      simp_rw [← integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
        (fun j _ => (hi i j).const_mul (v i * w j)))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum Finset.univ (fun j _ => (hi i j).const_mul (v i * w j))).symm
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      unfold designCombination
      simp only [Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

 theorem designCombination_square_integral (μ : Measure X) [IsFiniteMeasure μ]
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hB : 0 ≤ B)
    (hzB : ∀ i x, |z i x| ≤ B)
    (horth : ∀ i j, (∫ x, z i x * z j x ∂μ) = if i = j then 1 else 0)
    (v : n → ℝ) :
    (∫ x, designCombination z v x ^ 2 ∂μ) = v ⬝ᵥ v := by
  have hg : designGram μ (fun _ => 1) z = 1 := by
    ext i j
    simpa only [designGram, one_mul, Matrix.one_apply] using horth i j
  have he := designGram_bilinear μ (fun _ => 1) measurable_const 1 (Filter.Eventually.of_forall (fun _ => by norm_num))
    z hz B hB hzB v v
  simpa only [hg, Matrix.one_mulVec, one_mul, ← pow_two] using he.symm

 theorem designGram_quadratic_bounds (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (lo hi : ℝ) (hlo : 0 ≤ lo)
    (hg_bounds : ∀ᵐ x ∂μ, lo ≤ g x ∧ g x ≤ hi)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hB : 0 ≤ B)
    (hzB : ∀ i x, |z i x| ≤ B)
    (horth : ∀ i j, (∫ x, z i x * z j x ∂μ) = if i = j then 1 else 0)
    (v : n → ℝ) :
    lo * (v ⬝ᵥ v) ≤ v ⬝ᵥ (designGram μ g z).mulVec v ∧
      v ⬝ᵥ (designGram μ g z).mulVec v ≤ hi * (v ⬝ᵥ v) := by
  have hgb : ∀ᵐ x ∂μ, |g x| ≤ hi := hg_bounds.mono (fun x hx => by rw [abs_of_nonneg (hlo.trans hx.1)]; exact hx.2)
  rw [designGram_bilinear μ g hg hi hgb z hz B hB hzB v v]
  have hmeas : Measurable (designCombination z v) := Finset.measurable_sum _ (fun i _ => measurable_const.mul (hz i))
  have hb : ∀ x, |designCombination z v x| ≤ ∑ i, |v i| * B := by
    intro x
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hzB i x) (abs_nonneg _)))
  have hBv : 0 ≤ ∑ i, |v i| * B := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) hB)
  have hi0 : Integrable (fun x => designCombination z v x ^ 2) μ := by
    apply Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable ((∑ i, |v i| * B) ^ 2)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hBv).mpr (hb x)
  have hig : Integrable (fun x => g x * designCombination z v x ^ 2) μ := by
    apply Integrable.of_bound (hg.mul (hmeas.pow_const 2)).aestronglyMeasurable (hi * (∑ i, |v i| * B) ^ 2)
    filter_upwards [hg_bounds] with x hx
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (designCombination z v x)), abs_of_nonneg (hlo.trans hx.1)]
    apply mul_le_mul hx.2 _ (sq_nonneg _) (hlo.trans (hx.1.trans hx.2))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hBv).mpr (hb x)
  have hsq := designCombination_square_integral μ z hz B hB hzB horth v
  constructor
  · have hm := integral_mono_ae (hi0.const_mul lo) hig (hg_bounds.mono (fun x hx =>
      mul_le_mul_of_nonneg_right hx.1 (sq_nonneg _)))
    rw [integral_const_mul, hsq] at hm
    simpa only [pow_two, mul_assoc] using hm
  · have hm := integral_mono_ae hig (hi0.const_mul hi) (hg_bounds.mono (fun x hx =>
      mul_le_mul_of_nonneg_right hx.2 (sq_nonneg _)))
    rw [integral_const_mul, hsq] at hm
    simpa only [pow_two, mul_assoc] using hm

 theorem designGram_spectrum_subset (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (lo hi : ℝ) (hlo : 0 ≤ lo)
    (hg_bounds : ∀ᵐ x ∂μ, lo ≤ g x ∧ g x ≤ hi)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hB : 0 ≤ B)
    (hzB : ∀ i x, |z i x| ≤ B)
    (horth : ∀ i j, (∫ x, z i x * z j x ∂μ) = if i = j then 1 else 0) :
    spectrum ℝ (designGram μ g z) ⊆ Set.Icc lo hi := by
  let Ω := designGram μ g z
  have hΩ := designGram_isHermitian μ g z
  rw [hΩ.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  have hb := designGram_quadratic_bounds μ g hg lo hi hlo hg_bounds z hz B hB hzB horth
    (hΩ.eigenvectorBasis i)
  have hn : (hΩ.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hΩ.eigenvectorBasis i : n → ℝ) = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ite_true] using
      (orthonormal_iff_ite.mp hΩ.eigenvectorBasis.orthonormal i i)
  have he := hΩ.eigenvalues_eq i
  simp only [star_trivial, RCLike.re_to_real] at he
  simpa only [hn, mul_one, ← he, Set.mem_Icc] using hb

 theorem designGram_posDef (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (lo hi : ℝ) (hlo : 0 < lo)
    (hg_bounds : ∀ᵐ x ∂μ, lo ≤ g x ∧ g x ≤ hi)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hB : 0 ≤ B)
    (hzB : ∀ i x, |z i x| ≤ B)
    (horth : ∀ i j, (∫ x, z i x * z j x ∂μ) = if i = j then 1 else 0) :
    (designGram μ g z).PosDef := by
  have hΩ := designGram_isHermitian μ g z
  apply hΩ.posDef_iff_eigenvalues_pos.mpr
  intro i
  exact hlo.trans_le ((designGram_spectrum_subset μ g hg lo hi hlo.le hg_bounds z hz B hB hzB horth)
    (hΩ.eigenvalues_mem_spectrum_real i)).1

end RoughRegime.Model
