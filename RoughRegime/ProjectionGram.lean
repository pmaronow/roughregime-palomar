module

public import RoughRegime.CombinedAnalytic
public import RoughRegime.KernelExpressions


@[expose] public section
/-! Actual Gram normal equations and polynomial residual factors for nested projections. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace RoughRegime.ProjectionGram

variable {n a b : Type*} [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Parent Gram matrix in the child basis. -/
def gram (Ω : Matrix n n ℝ) (L : Matrix n a ℝ) : Matrix a a ℝ := Lᵀ * Ω * L
/-- Coefficient operator for the parent projection in the child basis. -/
def parentOperator (Ω : Matrix n n ℝ) (L : Matrix n a ℝ) : Matrix n n ℝ :=
  L * (gram Ω L)⁻¹ * Lᵀ
/-- Complementary coefficient operator. -/
def residualOperator (Ω : Matrix n n ℝ) (L : Matrix n a ℝ) : Matrix n n ℝ :=
  Ω⁻¹ - parentOperator Ω L
/-- The actual polynomial residual factor, including zero-dimensional parents. -/
def polynomialResidual (Ω : Matrix n n ℝ) (L : Matrix n a ℝ) : Matrix n n ℝ :=
  (gram Ω L).det • 1 - Ω * L * (gram Ω L).adjugate * Lᵀ

omit [DecidableEq n] in
theorem orthonormal_mulVec_injective (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) :
    Function.Injective L.mulVec := by
  intro x y hxy
  have h := congrArg Lᵀ.mulVec hxy
  simpa only [mulVec_mulVec, hL, one_mulVec] using h

omit [DecidableEq n] in
theorem gram_posDef (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) : (gram Ω L).PosDef := by
  simpa only [gram, conjTranspose_eq_transpose_of_trivial] using
    hΩ.conjTranspose_mul_mul_same (orthonormal_mulVec_injective L hL)

omit [DecidableEq n] in
theorem gram_isUnit (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) : IsUnit (gram Ω L) :=
  (gram_posDef Ω hΩ L hL).isUnit

omit [DecidableEq n] in
lemma gram_det_ne_zero (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) : (gram Ω L).det ≠ 0 :=
  ((gram Ω L).isUnit_iff_isUnit_det.mp (gram_isUnit Ω hΩ L hL)).ne_zero

omit [DecidableEq n] in
/-- The inverse Gram coefficients solve the exact finite-dimensional normal equations. -/
theorem gram_normal_equations (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) (u : n → ℝ) :
    (gram Ω L).mulVec ((gram Ω L)⁻¹.mulVec (Lᵀ.mulVec u)) = Lᵀ.mulVec u := by
  rw [mulVec_mulVec, mul_nonsing_inv _
    ((gram Ω L).isUnit_iff_isUnit_det.mp (gram_isUnit Ω hΩ L hL)), one_mulVec]

/-- The coefficient-space projection kills all normal-equation residuals. -/
theorem projection_normal_residual (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) :
    Lᵀ * Ω * (1 - parentOperator Ω L * Ω) = 0 := by
  have hg := (gram Ω L).isUnit_iff_isUnit_det.mp (gram_isUnit Ω hΩ L hL)
  unfold parentOperator
  calc
    _ = Lᵀ * Ω - (gram Ω L * (gram Ω L)⁻¹) * (Lᵀ * Ω) := by
      unfold gram
      simp only [Matrix.mul_sub, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [mul_nonsing_inv _ hg, Matrix.one_mul, sub_self]

omit [DecidableEq n] in
/-- The parent coefficient operator is symmetric. -/
theorem parentOperator_isSymm (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) : (parentOperator Ω L).IsSymm := by
  have hs := (gram_posDef Ω hΩ L hL).isHermitian.isSymm.inv
  change (parentOperator Ω L)ᵀ = parentOperator Ω L
  simp only [parentOperator, transpose_mul, transpose_transpose]
  rw [hs]
  exact (Matrix.mul_assoc L (gram Ω L)⁻¹ Lᵀ).symm

theorem residualOperator_isSymm (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) : (residualOperator Ω L).IsSymm :=
  hΩ.isHermitian.isSymm.inv.sub (parentOperator_isSymm Ω hΩ L hL)

omit [Fintype n] [DecidableEq n] [DecidableEq b] in
/-- Genuine column-space inclusion yields a matrix factorization. -/
theorem factor_of_column_range_subset (La : Matrix n a ℝ) (Lb : Matrix n b ℝ)
    (hsub : Set.range La.mulVec ⊆ Set.range Lb.mulVec) :
    ∃ T : Matrix b a ℝ, La = Lb * T := by
  have hex (j : a) : ∃ v : b → ℝ, Lb.mulVec v = fun i => La i j := by
    have hr : (fun i => La i j) ∈ Set.range La.mulVec := by
      refine ⟨Pi.single j 1, ?_⟩
      rw [mulVec_single, MulOpposite.op_one, one_smul]
      rfl
    exact hsub hr
  choose v hv using hex
  refine ⟨fun i j => v j i, ?_⟩
  ext i j
  exact (congrFun (hv j) i).symm

omit [DecidableEq n] in
/-- Nested parent projections absorb in the actual weighted geometry. -/
theorem nested_parent_absorption (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (La : Matrix n a ℝ) (Lb : Matrix n b ℝ)
    (hLb : Lbᵀ * Lb = 1) (hsub : Set.range La.mulVec ⊆ Set.range Lb.mulVec) :
    parentOperator Ω La * Ω * parentOperator Ω Lb = parentOperator Ω La := by
  obtain ⟨T, hT⟩ := factor_of_column_range_subset La Lb hsub
  have hg := (gram Ω Lb).isUnit_iff_isUnit_det.mp (gram_isUnit Ω hΩ Lb hLb)
  have hfix : Laᵀ * Ω * parentOperator Ω Lb = Laᵀ := by
    rw [hT, transpose_mul]
    unfold parentOperator
    calc
      _ = Tᵀ * (gram Ω Lb * (gram Ω Lb)⁻¹) * Lbᵀ := by
        unfold gram
        simp only [Matrix.mul_assoc]
      _ = Tᵀ * Lbᵀ := by rw [mul_nonsing_inv _ hg, Matrix.mul_one]
  unfold parentOperator at *
  calc
    _ = La * (gram Ω La)⁻¹ * (Laᵀ * Ω * (Lb * (gram Ω Lb)⁻¹ * Lbᵀ)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hfix]

/-- The source nested-complement identity, proved from actual Gram projections. -/
theorem nested_residual_identity (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (La : Matrix n a ℝ) (Lb : Matrix n b ℝ)
    (hLb : Lbᵀ * Lb = 1) (hsub : Set.range La.mulVec ⊆ Set.range Lb.mulVec) :
    residualOperator Ω La * Ω * residualOperator Ω Lb = residualOperator Ω Lb := by
  have hu := Ω.isUnit_iff_isUnit_det.mp hΩ.isUnit
  have hab := nested_parent_absorption Ω hΩ La Lb hLb hsub
  unfold residualOperator
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  rw [nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_assoc (parentOperator Ω La) Ω Ω⁻¹, mul_nonsing_inv _ hu, Matrix.mul_one, hab]
  abel

lemma adjugate_eq_det_smul_inverse (G : Matrix a a ℝ) (hG : IsUnit G) :
    G.adjugate = G.det • G⁻¹ := by
  have hd := (G.isUnit_iff_isUnit_det.mp hG).ne_zero
  rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hd, one_smul]

/-- The polynomial residual factor has the precise rational factorization in the source. -/
theorem polynomialResidual_eq (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) :
    polynomialResidual Ω L = (gram Ω L).det • (Ω * residualOperator Ω L) := by
  have hu := Ω.isUnit_iff_isUnit_det.mp hΩ.isUnit
  rw [polynomialResidual, adjugate_eq_det_smul_inverse _ (gram_isUnit Ω hΩ L hL)]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub]
  congr 1
  unfold residualOperator parentOperator
  rw [Matrix.mul_sub, mul_nonsing_inv _ hu]
  simp only [Matrix.mul_assoc]

/-- The two polynomial residual factors recover the exact increment matrix. -/
theorem polynomialResidual_reconstruction (Ω : Matrix n n ℝ) (hΩ : Ω.PosDef)
    (La : Matrix n a ℝ) (Lb : Matrix n b ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (hsub : Set.range La.mulVec ⊆ Set.range Lb.mulVec) :
    (polynomialResidual Ω La)ᵀ *
      (((gram Ω La).det * (gram Ω Lb).det)⁻¹ • Ω⁻¹) *
      polynomialResidual Ω Lb = residualOperator Ω Lb := by
  have hda := gram_det_ne_zero Ω hΩ La hLa
  have hdb := gram_det_ne_zero Ω hΩ Lb hLb
  have hΩs := hΩ.isHermitian.isSymm
  have hNas := residualOperator_isSymm Ω hΩ La hLa
  have hu := Ω.isUnit_iff_isUnit_det.mp hΩ.isUnit
  rw [polynomialResidual_eq Ω hΩ La hLa, polynomialResidual_eq Ω hΩ Lb hLb,
    transpose_smul, transpose_mul, hΩs, hNas]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hc : (gram Ω Lb).det * (((gram Ω La).det * (gram Ω Lb).det)⁻¹ *
      (gram Ω La).det) = 1 := by field_simp
  rw [hc, one_smul]
  calc
    _ = residualOperator Ω La * (Ω * Ω⁻¹) * Ω * residualOperator Ω Lb := by
      simp only [Matrix.mul_assoc]
    _ = residualOperator Ω Lb := by
      rw [mul_nonsing_inv _ hu, Matrix.mul_one, nested_residual_identity Ω hΩ La Lb hLb hsub]

/-- The exact compression retains the source spectral interval, rather than
assuming spectral bounds for the parent Gram matrices. -/
theorem gram_spectrum_subset (lo hi : ℝ) (Ω : Matrix n n ℝ)
    (hΩ : Ω.IsHermitian) (hSpec : spectrum ℝ Ω ⊆ Set.Icc lo hi)
    (L : Matrix n a ℝ) (hL : Lᵀ * L = 1) :
    spectrum ℝ (gram Ω L) ⊆ Set.Icc lo hi := by
  have hs : IsSelfAdjoint Ω := Matrix.isHermitian_iff_isSelfAdjoint.mp hΩ
  have hgs : IsSelfAdjoint (gram Ω L) := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    simpa only [gram, conjTranspose_eq_transpose_of_trivial] using
      isHermitian_conjTranspose_mul_mul L hΩ
  have hlo : (algebraMap ℝ (Matrix n n ℝ)) lo ≤ Ω :=
    (algebraMap_le_iff_le_spectrum hs).mpr (fun x hx => (hSpec hx).1)
  have hhi : Ω ≤ (algebraMap ℝ (Matrix n n ℝ)) hi :=
    (le_algebraMap_iff_spectrum_le hs).mpr (fun x hx => (hSpec hx).2)
  have lower : (algebraMap ℝ (Matrix a a ℝ)) lo ≤ gram Ω L := by
    apply sub_nonneg.mp
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hlo)).conjTranspose_mul_mul_same L
    convert hp using 1
    simp only [Algebra.algebraMap_eq_smul_one, conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hL, gram, Matrix.mul_assoc]
  have upper : gram Ω L ≤ (algebraMap ℝ (Matrix a a ℝ)) hi := by
    apply sub_nonneg.mp
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hhi)).conjTranspose_mul_mul_same L
    convert hp using 1
    simp only [Algebra.algebraMap_eq_smul_one, conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hL, gram, Matrix.mul_assoc]
  intro x hx
  exact ⟨(algebraMap_le_iff_le_spectrum hgs).mp lower x hx,
    (le_algebraMap_iff_spectrum_le hgs).mp upper x hx⟩

end RoughRegime.ProjectionGram
