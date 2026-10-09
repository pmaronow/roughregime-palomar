module

public import RoughRegime.ProjectionGram
public import Mathlib.LinearAlgebra.Matrix.Reindex


@[expose] public section
/-! Exact child-block projection energies in the parent's normalized basis. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
namespace RoughRegime.BlockProjectionEnergy

variable {B n : Type*} [Fintype B] [DecidableEq B] [Fintype n] [DecidableEq n]

 def blockRingHom : (B → Matrix n n ℝ) →+* Matrix (B × n) (B × n) ℝ :=
  (Matrix.reindexRingEquiv ℝ (Equiv.prodComm n B)).toRingHom.comp
    (Matrix.blockDiagonalRingHom n B ℝ)

 def blockGram (Ω : B → Matrix n n ℝ) : Matrix (B × n) (B × n) ℝ := blockRingHom Ω

@[simp] lemma blockGram_apply (Ω : B → Matrix n n ℝ) (b c : B) (i j : n) :
    blockGram Ω (b, i) (c, j) = if b = c then Ω b i j else 0 := rfl

@[simp] lemma blockGram_one : blockGram (1 : B → Matrix n n ℝ) = 1 :=
  blockRingHom.map_one

lemma blockGram_mul (Ω Ψ : B → Matrix n n ℝ) :
    blockGram (fun b => Ω b * Ψ b) = blockGram Ω * blockGram Ψ :=
  blockRingHom.map_mul Ω Ψ

/-- The actual inverse is blockwise inverse, even when a child dimension is zero. -/
theorem blockGram_inv (Ω : B → Matrix n n ℝ) (hΩ : ∀ b, IsUnit (Ω b)) :
    (blockGram Ω)⁻¹ = blockGram (fun b => (Ω b)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [← blockGram_mul]
  have he : (fun b => (Ω b)⁻¹ * Ω b) = (1 : B → Matrix n n ℝ) := by
    funext b
    exact nonsing_inv_mul _ ((Ω b).isUnit_iff_isUnit_det.mp (hΩ b))
  rw [he, blockGram_one]

lemma blockGram_mulVec (Ω : B → Matrix n n ℝ) (v : B × n → ℝ) (b : B) (i : n) :
    (blockGram Ω).mulVec v (b, i) = (Ω b).mulVec (fun j => v (b, j)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockGram_apply]
  simp [ite_mul]

/-- The genuine quadratic cross-energy of a block projection is the sum of its
actual child energies. -/
theorem blockGram_inverse_energy (Ω : B → Matrix n n ℝ) (hΩ : ∀ b, IsUnit (Ω b))
    (u v : B × n → ℝ) :
    u ⬝ᵥ (blockGram Ω)⁻¹.mulVec v =
      ∑ b, (fun i => u (b, i)) ⬝ᵥ (Ω b)⁻¹.mulVec (fun i => v (b, i)) := by
  rw [blockGram_inv Ω hΩ]
  simp only [dotProduct, Fintype.sum_prod_type, blockGram_mulVec]

lemma inverse_energy_smul (Ω : Matrix n n ℝ) (u v : n → ℝ) (r : ℝ) :
    (r • u) ⬝ᵥ Ω⁻¹.mulVec (r • v) = r ^ 2 * (u ⬝ᵥ Ω⁻¹.mulVec v) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

omit [Fintype B] [DecidableEq B] in
/-- Reindexing the actual matrix and its moment vectors preserves inverse energy. -/
theorem inverse_energy_reindex {m : Type*} [Fintype m] [DecidableEq m]
    (e : n ≃ m) (Ω : Matrix n n ℝ) (u v : n → ℝ) :
    (u ∘ e.symm) ⬝ᵥ (Matrix.reindex e e Ω)⁻¹.mulVec (v ∘ e.symm) =
      u ⬝ᵥ Ω⁻¹.mulVec v := by
  rw [Matrix.inv_reindex]
  change (u ∘ e.symm) ⬝ᵥ (Ω⁻¹.submatrix e.symm e.symm).mulVec (v ∘ e.symm) = _
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  have he : (v ∘ e.symm) ∘ e = v := by funext i; simp
  rw [he]
  exact comp_equiv_dotProduct_comp_equiv u (Ω⁻¹.mulVec v) e.symm

omit [Fintype B] [DecidableEq B] in
lemma parent_energy {a : Type*} [Fintype a] [DecidableEq a]
    (Ω : Matrix n n ℝ) (L : Matrix n a ℝ) (u v : n → ℝ) :
    (Lᵀ.mulVec u) ⬝ᵥ (RoughRegime.ProjectionGram.gram Ω L)⁻¹.mulVec (Lᵀ.mulVec v) =
      u ⬝ᵥ (RoughRegime.ProjectionGram.parentOperator Ω L).mulVec v := by
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  simp only [RoughRegime.ProjectionGram.parentOperator, Matrix.mulVec_mulVec, Matrix.mul_assoc]

omit [Fintype B] [DecidableEq B] in
/-- The finite inverse-energy difference is the source complementary operator. -/
theorem inverse_energy_increment {a : Type*} [Fintype a] [DecidableEq a]
    (Ω : Matrix n n ℝ) (L : Matrix n a ℝ) (u v : n → ℝ) :
    u ⬝ᵥ Ω⁻¹.mulVec v -
      (Lᵀ.mulVec u) ⬝ᵥ (RoughRegime.ProjectionGram.gram Ω L)⁻¹.mulVec (Lᵀ.mulVec v) =
        u ⬝ᵥ (RoughRegime.ProjectionGram.residualOperator Ω L).mulVec v := by
  rw [RoughRegime.ProjectionGram.residualOperator, Matrix.sub_mulVec, dotProduct_sub,
    parent_energy]

/-- The two children each have parent probability one half; the actual normalized
moments are `u_child / sqrt 2`. Thus the parent block projection energy is
exactly the half-sum of the two child energies. -/
theorem bool_child_energy (Ω : Bool → Matrix n n ℝ) (hΩ : ∀ b, (Ω b).PosDef)
    (u v : Bool → n → ℝ) :
    (fun bi : Bool × n => u bi.1 bi.2 / Real.sqrt 2) ⬝ᵥ
      (blockGram Ω)⁻¹.mulVec (fun bi : Bool × n => v bi.1 bi.2 / Real.sqrt 2) =
      (1 / 2 : ℝ) * ∑ b : Bool, u b ⬝ᵥ (Ω b)⁻¹.mulVec (v b) := by
  rw [blockGram_inverse_energy Ω (fun b => (hΩ b).isUnit)]
  have hr : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc
    _ = ∑ b : Bool, (Real.sqrt 2)⁻¹ ^ 2 * (u b ⬝ᵥ (Ω b)⁻¹.mulVec (v b)) := by
      apply Finset.sum_congr rfl
      intro b _
      have hu : (fun i => u b i / Real.sqrt 2) = (Real.sqrt 2)⁻¹ • u b := by
        funext i
        simp [div_eq_mul_inv, mul_comm]
      have hv : (fun i => v b i / Real.sqrt 2) = (Real.sqrt 2)⁻¹ • v b := by
        funext i
        simp [div_eq_mul_inv, mul_comm]
      rw [hu, hv]
      exact inverse_energy_smul (Ω b) (u b) (v b) (Real.sqrt 2)⁻¹
    _ = _ := by rw [hr, Finset.mul_sum]

end RoughRegime.BlockProjectionEnergy
