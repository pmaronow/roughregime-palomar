module

public import RoughRegime.ProjectionGram


@[expose] public section
/-! Actual Hilbert-space projections expressed by the finite Gram normal equations. -/
noncomputable section
open scoped BigOperators
open RealInnerProductSpace Matrix
namespace RoughRegime.HilbertGram
open RoughRegime.ProjectionGram

variable {E n a : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]

def basisSpan (z : n → E) : Submodule ℝ E := Submodule.span ℝ (Set.range z)

instance basisSpan_finiteDimensional (z : n → E) : FiniteDimensional ℝ (basisSpan z) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range z)

def linearCombination (z : n → E) (c : n → ℝ) : E := ∑ i, c i • z i

def moments (z : n → E) (f : E) : n → ℝ := fun i => ⟪z i, f⟫

def parentBasis (z : n → E) (L : Matrix n a ℝ) : a → E := fun j => ∑ i, L i j • z i

/-- Orthogonal projection onto the actual finite span has the inverse-Gram coefficient vector. -/
theorem projection_coefficients (z : n → E) (hz : LinearIndependent ℝ z) (f : E) :
    (basisSpan z).starProjection f =
      linearCombination z ((Matrix.gram ℝ z)⁻¹.mulVec (moments z f)) := by
  let Ω := Matrix.gram ℝ z
  let u := moments z f
  let c := Ω⁻¹.mulVec u
  have hΩ : Ω.PosDef := Matrix.posDef_gram_of_linearIndependent hz
  have hn : Ω.mulVec c = u := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ω.isUnit_iff_isUnit_det.mp hΩ.isUnit),
      Matrix.one_mulVec]
  have hr (i : n) : ⟪z i, f - linearCombination z c⟫ = 0 := by
    rw [inner_sub_right]
    have he : ⟪z i, linearCombination z c⟫ = (Ω.mulVec c) i := by
      simp only [linearCombination, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Ω, Matrix.gram_apply]
      ring
    rw [he, hn]
    exact sub_self _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
    exact ⟨c, rfl⟩
  · intro w hw
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
    rw [← hd, inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_smul_right, real_inner_comm, hr i, mul_zero]

omit [DecidableEq n] [Fintype a] [DecidableEq a] in
/-- Parent Gram matrices are exactly the Hilbert Gram matrices of the transported basis. -/
theorem parentBasis_gram (z : n → E) (L : Matrix n a ℝ) :
    Matrix.gram ℝ (parentBasis z L) = ProjectionGram.gram (Matrix.gram ℝ z) L := by
  ext i j
  simp only [Matrix.gram_apply, parentBasis, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, conj_trivial, ProjectionGram.gram, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [DecidableEq n] [Fintype a] [DecidableEq a] in
theorem parentBasis_moments (z : n → E) (L : Matrix n a ℝ) (f : E) :
    moments (parentBasis z L) f = Lᵀ.mulVec (moments z f) := by
  ext i
  simp only [moments, parentBasis, sum_inner, inner_smul_left, conj_trivial,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply]

omit [DecidableEq n] [DecidableEq a] in
lemma linearCombination_parentBasis (z : n → E) (L : Matrix n a ℝ) (c : a → ℝ) :
    linearCombination (parentBasis z L) c = linearCombination z (L.mulVec c) := by
  simp only [linearCombination, parentBasis, Finset.smul_sum, smul_smul,
    Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

omit [DecidableEq n] in
theorem parentBasis_linearIndependent (z : n → E) (hz : LinearIndependent ℝ z)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) : LinearIndependent ℝ (parentBasis z L) := by
  apply Matrix.linearIndependent_of_posDef_gram
  rw [parentBasis_gram]
  exact gram_posDef _ (Matrix.posDef_gram_of_linearIndependent hz) L hL

/-- The source parent projection is exactly the coefficient operator `L Γ⁻¹ Lᵀ`. -/
theorem parent_projection_coefficients (z : n → E) (hz : LinearIndependent ℝ z)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (f : E) :
    (basisSpan (parentBasis z L)).starProjection f =
      linearCombination z ((parentOperator (Matrix.gram ℝ z) L).mulVec (moments z f)) := by
  rw [projection_coefficients _ (parentBasis_linearIndependent z hz L hL),
    parentBasis_gram, parentBasis_moments, linearCombination_parentBasis]
  simp only [parentOperator, Matrix.mulVec_mulVec, Matrix.mul_assoc]

omit [DecidableEq n] in
lemma linearCombination_sub (z : n → E) (c d : n → ℝ) :
    linearCombination z (c - d) = linearCombination z c - linearCombination z d := by
  simp only [linearCombination, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- The actual child-minus-parent projection has precisely the source residual coefficient vector. -/
theorem residual_projection_coefficients (z : n → E) (hz : LinearIndependent ℝ z)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (f : E) :
    (basisSpan z).starProjection f - (basisSpan (parentBasis z L)).starProjection f =
      linearCombination z ((residualOperator (Matrix.gram ℝ z) L).mulVec (moments z f)) := by
  rw [projection_coefficients z hz f, parent_projection_coefficients z hz L hL f,
    residualOperator, Matrix.sub_mulVec, linearCombination_sub]

omit [DecidableEq n] [Fintype a] [DecidableEq a] in
/-- The transported parent span is genuinely contained in the child span. -/
theorem parentBasis_span_le (z : n → E) (L : Matrix n a ℝ) :
    basisSpan (parentBasis z L) ≤ basisSpan z := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  exact ⟨fun i => L i j, rfl⟩

omit [DecidableEq n] in
lemma inner_linearCombination_moments (z : n → E) (c : n → ℝ) (f : E) :
    ⟪linearCombination z c, f⟫ = c ⬝ᵥ moments z f := by
  simp only [linearCombination, sum_inner, real_inner_smul_left, dotProduct, moments]

lemma projection_inner_eq {K : Submodule ℝ E} [K.HasOrthogonalProjection] (f g : E) :
    ⟪K.starProjection f, K.starProjection g⟫ = ⟪K.starProjection f, g⟫ := by
  have ho := Submodule.starProjection_inner_eq_zero g (K.starProjection f)
    (K.starProjection_apply_mem f)
  rw [inner_sub_left] at ho
  have he := sub_eq_zero.mp ho
  calc
    _ = ⟪K.starProjection g, K.starProjection f⟫ := real_inner_comm _ _
    _ = ⟪g, K.starProjection f⟫ := he.symm
    _ = _ := real_inner_comm _ _

/-- The actual projected inner product is the inverse-Gram bilinear form. -/
theorem child_projection_inner (z : n → E) (hz : LinearIndependent ℝ z) (f g : E) :
    ⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ =
      moments z f ⬝ᵥ ((Matrix.gram ℝ z)⁻¹.mulVec (moments z g)) := by
  rw [projection_inner_eq, projection_coefficients z hz f, inner_linearCombination_moments,
    dotProduct_comm]
  exact (Matrix.isHermitian_gram ℝ z).isSymm.inv.dotProduct_mulVec_comm

/-- The actual parent projected inner product uses `B=L Γ⁻¹ Lᵀ` in the child coordinates. -/
theorem parent_projection_inner (z : n → E) (hz : LinearIndependent ℝ z)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (f g : E) :
    ⟪(basisSpan (parentBasis z L)).starProjection f,
      (basisSpan (parentBasis z L)).starProjection g⟫ =
      moments z f ⬝ᵥ ((parentOperator (Matrix.gram ℝ z) L).mulVec (moments z g)) := by
  rw [projection_inner_eq, parent_projection_coefficients z hz L hL f,
    inner_linearCombination_moments, dotProduct_comm]
  exact (parentOperator_isSymm _ (Matrix.posDef_gram_of_linearIndependent hz) L hL).dotProduct_mulVec_comm

/-- Source Lemma 6's exact cell increment identity for genuine orthogonal projections. -/
theorem projection_increment_identity (z : n → E) (hz : LinearIndependent ℝ z)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (f g : E) :
    ⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ -
      ⟪(basisSpan (parentBasis z L)).starProjection f,
        (basisSpan (parentBasis z L)).starProjection g⟫ =
      moments z f ⬝ᵥ ((residualOperator (Matrix.gram ℝ z) L).mulVec (moments z g)) := by
  rw [child_projection_inner z hz f g, parent_projection_inner z hz L hL f g,
    residualOperator, Matrix.sub_mulVec, dotProduct_sub]

omit [DecidableEq n] in
/-- The child basis identifies coefficient vectors faithfully. -/
theorem linearCombination_injective (z : n → E) (hz : LinearIndependent ℝ z) :
    Function.Injective (linearCombination z) := by
  intro c d h
  have hc : linearCombination z (c - d) = 0 := by
    rw [linearCombination_sub, h, sub_self]
  have he := (Fintype.linearIndependent_iff.mp hz) (c - d) hc
  ext i
  exact sub_eq_zero.mp (he i)

omit [DecidableEq a] in
/-- Actual nesting of Hilbert parent spaces implies the column-space nesting
used in the finite matrix residual identity. -/
theorem column_range_subset_of_span_le {b : Type*} [Fintype b] [DecidableEq b]
    (z : n → E) (hz : LinearIndependent ℝ z) (La : Matrix n a ℝ) (Lb : Matrix n b ℝ)
    (hsub : basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb)) :
    Set.range La.mulVec ⊆ Set.range Lb.mulVec := by
  rintro v ⟨x, rfl⟩
  have hm : linearCombination (parentBasis z La) x ∈ basisSpan (parentBasis z La) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hsub hm)
  refine ⟨y, linearCombination_injective z hz ?_⟩
  rw [← linearCombination_parentBasis, ← linearCombination_parentBasis]
  exact hy

/-- The exact residual factorization in Lemma 6 now follows for actual Hilbert
projections and genuinely nested parent spaces. -/
theorem hilbert_increment_residual_factors {b : Type*} [Fintype b] [DecidableEq b]
    (z : n → E) (hz : LinearIndependent ℝ z) (La : Matrix n a ℝ) (Lb : Matrix n b ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (hsub : basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb)) (f g : E) :
    ⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ -
      ⟪(basisSpan (parentBasis z Lb)).starProjection f,
        (basisSpan (parentBasis z Lb)).starProjection g⟫ =
      (polynomialResidual (Matrix.gram ℝ z) La).mulVec (moments z f) ⬝ᵥ
        ((((ProjectionGram.gram (Matrix.gram ℝ z) La).det *
          (ProjectionGram.gram (Matrix.gram ℝ z) Lb).det)⁻¹ • (Matrix.gram ℝ z)⁻¹).mulVec
            ((polynomialResidual (Matrix.gram ℝ z) Lb).mulVec (moments z g))) := by
  rw [projection_increment_identity z hz Lb hLb f g]
  symm
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  rw [polynomialResidual_reconstruction _ (Matrix.posDef_gram_of_linearIndependent hz) La Lb hLa hLb
    (column_range_subset_of_span_le z hz La Lb hsub)]

end RoughRegime.HilbertGram
