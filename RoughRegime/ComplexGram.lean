module

public import RoughRegime.ProjectionGram


@[expose] public section
/-! Hermitian spectral compression and the genuine real-to-complex Gram bridge. -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace RoughRegime.ComplexGram

variable {n a : Type*} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]

lemma map_ofReal_conjTranspose (L : Matrix n a ℝ) :
    Lᴴ.map Complex.ofReal = (L.map Complex.ofReal)ᴴ := by
  ext i j
  simp [Matrix.conjTranspose, Matrix.map_apply]

lemma map_ofReal_posSemidef (M : Matrix n n ℝ) (hM : M.PosSemidef) :
    (M.map Complex.ofReal).PosSemidef := by
  obtain ⟨A, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have he : (star A * A).map Complex.ofReal =
      (A.map Complex.ofReal)ᴴ * (A.map Complex.ofReal) := by
    ext i j
    simp [star_eq_conjTranspose, Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma map_ofReal_isHermitian (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    (M.map Complex.ofReal).IsHermitian :=
  hM.map Complex.ofReal (by intro x; simp)

lemma map_ofReal_algebraMap (r : ℝ) :
    ((algebraMap ℝ (Matrix n n ℝ)) r).map Complex.ofReal =
      (algebraMap ℝ (Matrix n n ℂ)) r := by
  ext i j
  by_cases hij : i = j <;>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, hij]

/-- Complexifying a real symmetric matrix preserves its real spectral interval. -/
theorem map_ofReal_spectrum_subset (lo hi : ℝ) (M : Matrix n n ℝ)
    (hM : M.IsHermitian) (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    spectrum ℝ (M.map Complex.ofReal) ⊆ Set.Icc lo hi := by
  have hs : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hcs : IsSelfAdjoint (M.map Complex.ofReal) :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp (map_ofReal_isHermitian M hM)
  have hlo := (algebraMap_le_iff_le_spectrum hs).mpr (fun x hx => (hSpec hx).1)
  have hhi := (le_algebraMap_iff_spectrum_le hs).mpr (fun x hx => (hSpec hx).2)
  have lower : (algebraMap ℝ (Matrix n n ℂ)) lo ≤ M.map Complex.ofReal := by
    apply sub_nonneg.mp
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hp := map_ofReal_posSemidef _
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hlo))
    simpa only [Matrix.map_sub Complex.ofReal Complex.ofReal_sub, map_ofReal_algebraMap] using hp
  have upper : M.map Complex.ofReal ≤ (algebraMap ℝ (Matrix n n ℂ)) hi := by
    apply sub_nonneg.mp
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hp := map_ofReal_posSemidef _
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hhi))
    simpa only [Matrix.map_sub Complex.ofReal Complex.ofReal_sub, map_ofReal_algebraMap] using hp
  intro x hx
  exact ⟨(algebraMap_le_iff_le_spectrum hcs).mp lower x hx,
    (le_algebraMap_iff_spectrum_le hcs).mp upper x hx⟩

/-- A genuine Hermitian compression by orthonormal columns retains the interval. -/
theorem gram_spectrum_subset (lo hi : ℝ) (Ω : Matrix n n ℂ)
    (hΩ : Ω.IsHermitian) (hSpec : spectrum ℝ Ω ⊆ Set.Icc lo hi)
    (L : Matrix n a ℂ) (hL : Lᴴ * L = 1) :
    spectrum ℝ (Lᴴ * Ω * L) ⊆ Set.Icc lo hi := by
  have hs : IsSelfAdjoint Ω := Matrix.isHermitian_iff_isSelfAdjoint.mp hΩ
  have hgs : IsSelfAdjoint (Lᴴ * Ω * L) :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_conjTranspose_mul_mul L hΩ)
  have hlo := (algebraMap_le_iff_le_spectrum hs).mpr (fun x hx => (hSpec hx).1)
  have hhi := (le_algebraMap_iff_spectrum_le hs).mpr (fun x hx => (hSpec hx).2)
  have lower : (algebraMap ℝ (Matrix a a ℂ)) lo ≤ Lᴴ * Ω * L := by
    apply sub_nonneg.mp
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hlo)).conjTranspose_mul_mul_same L
    convert hp using 1
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hL, Matrix.mul_assoc]
  have upper : Lᴴ * Ω * L ≤ (algebraMap ℝ (Matrix a a ℂ)) hi := by
    apply sub_nonneg.mp
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hhi)).conjTranspose_mul_mul_same L
    convert hp using 1
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hL, Matrix.mul_assoc]
  intro x hx
  exact ⟨(algebraMap_le_iff_le_spectrum hgs).mp lower x hx,
    (le_algebraMap_iff_spectrum_le hgs).mp upper x hx⟩

end RoughRegime.ComplexGram
