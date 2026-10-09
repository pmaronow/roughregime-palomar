module

public import RoughRegime.HilbertGram


@[expose] public section
/-! Euclidean moment and polynomial residual bounds from actual Hilbert projections. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open RealInnerProductSpace Matrix
namespace RoughRegime.ProjectionFrame
open RoughRegime.HilbertGram RoughRegime.ProjectionGram

variable {E n a : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]

def euclidean (x : n → ℝ) : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm x

omit [Fintype n] [DecidableEq n] in
@[simp] lemma euclidean_coe (x : n → ℝ) : (euclidean x : n → ℝ) = x := rfl

lemma dotProduct_mulVec_norm_le (A : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    ‖(x : n → ℝ) ⬝ᵥ (A.mulVec (y : n → ℝ))‖ ≤ ‖x‖ * ‖A‖ * ‖y‖ := by
  have hc := norm_inner_le_norm (𝕜 := ℝ) x (euclidean (A.mulVec (y : n → ℝ)))
  have he : ⟪x, euclidean (A.mulVec (y : n → ℝ))⟫ =
      (x : n → ℝ) ⬝ᵥ A.mulVec (y : n → ℝ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    exact dotProduct_comm _ _
  rw [he] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_left (A.l2_opNorm_mulVec y) (norm_nonneg x)).trans_eq (by ring))

/-- Synthesis from a finite, possibly nonorthonormal family has the actual Gram norm bound. -/
theorem linearCombination_norm_le (z : n → E) (x : EuclideanSpace ℝ n) :
    ‖linearCombination z (x : n → ℝ)‖ ≤ Real.sqrt ‖Matrix.gram ℝ z‖ * ‖x‖ := by
  have he : (x : n → ℝ) ⬝ᵥ (Matrix.gram ℝ z).mulVec (x : n → ℝ) =
      ‖linearCombination z (x : n → ℝ)‖ ^ 2 := by
    simpa only [star_trivial, linearCombination, real_inner_self_eq_norm_sq] using
      Matrix.star_dotProduct_gram_mulVec z (x : n → ℝ) (x : n → ℝ)
  have hb := dotProduct_mulVec_norm_le (Matrix.gram ℝ z) x x
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
  have hs := Real.sq_sqrt (norm_nonneg (Matrix.gram ℝ z))
  have hb2 : ‖linearCombination z (x : n → ℝ)‖ ^ 2 ≤
      (Real.sqrt ‖Matrix.gram ℝ z‖ * ‖x‖) ^ 2 := by
    rw [mul_pow, hs]
    nlinarith only [hb]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp hb2

/-- Exact finite Bessel bound for the moment vector in a nonorthonormal child basis. -/
theorem moments_norm_le (z : n → E) (f : E) :
    ‖euclidean (moments z f)‖ ≤ Real.sqrt ‖Matrix.gram ℝ z‖ * ‖f‖ := by
  let x := euclidean (moments z f)
  have he : ⟪linearCombination z (x : n → ℝ), f⟫ = ‖x‖ ^ 2 := by
    rw [inner_linearCombination_moments]
    change (moments z f) ⬝ᵥ (moments z f) = ‖x‖ ^ 2
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, x, euclidean_coe] using
      (real_inner_self_eq_norm_sq x)
  have hc := norm_inner_le_norm (𝕜 := ℝ) (linearCombination z (x : n → ℝ)) f
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hc
  have hs := linearCombination_norm_le z x
  have hb := hc.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg f))
  by_cases hx : ‖x‖ = 0
  · change ‖x‖ ≤ _
    rw [hx]
    positivity
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    change ‖x‖ ≤ _
    apply (mul_le_mul_iff_left₀ hxpos).mp
    convert hb using 1 <;> ring

omit [DecidableEq n] [DecidableEq a] in
/-- A child-minus-parent projection annihilates every actual parent approximant;
its norm is controlled without assuming a residual contraction inequality. -/
theorem residual_projection_norm_le (z : n → E) (L : Matrix n a ℝ) (f t : E)
    (ht : t ∈ basisSpan (parentBasis z L)) :
    ‖(basisSpan z).starProjection f - (basisSpan (parentBasis z L)).starProjection f‖ ≤
      2 * ‖f - t‖ := by
  have htP : (basisSpan (parentBasis z L)).starProjection t = t := by
    exact Submodule.starProjection_mem_subspace_eq_self ⟨t, ht⟩
  have htZ : (basisSpan z).starProjection t = t := by
    exact Submodule.starProjection_mem_subspace_eq_self ⟨t, parentBasis_span_le z L ht⟩
  have he : (basisSpan z).starProjection f - (basisSpan (parentBasis z L)).starProjection f =
      (basisSpan z).starProjection (f - t) - (basisSpan (parentBasis z L)).starProjection (f - t) := by
    rw [map_sub, map_sub, htP, htZ]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add
    ((basisSpan z).norm_starProjection_apply_le (f - t))
    ((basisSpan (parentBasis z L)).norm_starProjection_apply_le (f - t))).trans_eq (by ring))

/-- Actual moment vectors of the projection residual coincide with `Ω N u`. -/
theorem residual_moments_eq (z : n → E) (hz : LinearIndependent ℝ z)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (f : E) :
    moments z ((basisSpan z).starProjection f - (basisSpan (parentBasis z L)).starProjection f) =
      (Matrix.gram ℝ z).mulVec ((residualOperator (Matrix.gram ℝ z) L).mulVec (moments z f)) := by
  rw [residual_projection_coefficients z hz L hL f]
  ext i
  simp only [moments, linearCombination, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct,
    Matrix.gram_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The polynomial residual factors are small because actual parent approximation
errors are small; no small-factor hypothesis is supplied. -/
theorem polynomialResidual_moment_norm_le (z : n → E) (hz : LinearIndependent ℝ z)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (f t : E)
    (ht : t ∈ basisSpan (parentBasis z L)) :
    ‖euclidean ((polynomialResidual (Matrix.gram ℝ z) L).mulVec (moments z f))‖ ≤
      2 * |(ProjectionGram.gram (Matrix.gram ℝ z) L).det| *
        Real.sqrt ‖Matrix.gram ℝ z‖ * ‖f - t‖ := by
  have hΩ : (Matrix.gram ℝ z).PosDef := Matrix.posDef_gram_of_linearIndependent hz
  rw [polynomialResidual_eq _ hΩ L hL, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    ← residual_moments_eq z hz L hL f]
  have he (c : ℝ) (v : n → ℝ) : euclidean (c • v) = c • euclidean v := rfl
  rw [he, norm_smul, Real.norm_eq_abs]
  have hb := moments_norm_le z ((basisSpan z).starProjection f -
    (basisSpan (parentBasis z L)).starProjection f)
  have hr := residual_projection_norm_le z L f t ht
  calc
    _ ≤ |(ProjectionGram.gram (Matrix.gram ℝ z) L).det| *
        (Real.sqrt ‖Matrix.gram ℝ z‖ *
          ‖(basisSpan z).starProjection f - (basisSpan (parentBasis z L)).starProjection f‖) := by gcongr
    _ ≤ |(ProjectionGram.gram (Matrix.gram ℝ z) L).det| *
        (Real.sqrt ‖Matrix.gram ℝ z‖ * (2 * ‖f - t‖)) := by gcongr
    _ = _ := by ring

/-- A Hermitian matrix in the positive source interval has the stated actual
Euclidean operator norm bound. -/
theorem matrix_norm_le_hi (lo hi : ℝ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (Ω : Matrix n n ℝ) (hΩ : Ω.IsHermitian) (hSpec : spectrum ℝ Ω ⊆ Set.Icc lo hi) :
    ‖Ω‖ ≤ hi := by
  rw [← cfc_id ℝ Ω (Matrix.isHermitian_iff_isSelfAdjoint.mp hΩ)]
  apply norm_cfc_le hhi
  intro x hx
  exact (abs_of_nonneg (hlo.trans (hSpec hx).1)).le.trans (hSpec hx).2

/-- Actual parent Gram determinant bound, including the empty determinant equal to one. -/
theorem gram_det_le_hi_pow (lo hi : ℝ) (_hlo : 0 < lo) (_hlt : lo < hi)
    (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef) (hSpec : spectrum ℝ Ω ⊆ Set.Icc lo hi)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) :
    |(ProjectionGram.gram Ω L).det| ≤ hi ^ Fintype.card a := by
  let Γ := ProjectionGram.gram Ω L
  have hΓ := gram_posDef Ω hΩ L hL
  have hs := gram_spectrum_subset lo hi Ω hΩ.isHermitian hSpec L hL
  rw [abs_of_pos hΓ.det_pos, hΓ.isHermitian.det_eq_prod_eigenvalues]
  calc
    _ ≤ ∏ _i : a, hi := Finset.prod_le_prod₀
      (fun i _ => (hΓ.eigenvalues_pos i).le)
      (fun i _ => (hs (hΓ.isHermitian.eigenvalues_mem_spectrum_real i)).2)
    _ = _ := by simp

/-- Source-sized small residual factors follow from genuine Hilbert parent
approximation errors and the actual source spectrum. -/
theorem polynomialResidual_moment_norm_le_of_spectrum (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (z : n → E) (hz : LinearIndependent ℝ z)
    (hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (f t : E)
    (ht : t ∈ basisSpan (parentBasis z L)) :
    ‖euclidean ((polynomialResidual (Matrix.gram ℝ z) L).mulVec (moments z f))‖ ≤
      2 * hi ^ Fintype.card a * Real.sqrt hi * ‖f - t‖ := by
  have hΩ := Matrix.posDef_gram_of_linearIndependent hz
  have hhi : 0 < hi := hlo.trans hlt
  apply (polynomialResidual_moment_norm_le z hz L hL f t ht).trans
  gcongr
  · exact gram_det_le_hi_pow lo hi hlo hlt _ hΩ hSpec L hL
  · exact matrix_norm_le_hi lo hi hlo.le (hlo.trans hlt).le _ hΩ.isHermitian hSpec

end RoughRegime.ProjectionFrame
