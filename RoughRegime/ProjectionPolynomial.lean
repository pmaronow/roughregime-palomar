module

public import RoughRegime.ProjectionGram


@[expose] public section
/-! Actual adjugate residual polynomials and the source degree bookkeeping. -/
noncomputable section
open scoped BigOperators
open Matrix MvPolynomial
namespace RoughRegime.ProjectionPolynomial

/-- Affine substitutions preserve total degree; this is proved from the actual
monomial expansion and does not assume the substituted polynomial's degree. -/
theorem affine_substitution_degree {σ τ : Type*} (P : MvPolynomial τ ℝ)
    (Q : τ → MvPolynomial σ ℝ) (hQ : ∀ i, (Q i).totalDegree ≤ 1) :
    ((MvPolynomial.eval₂Hom MvPolynomial.C Q) P).totalDegree ≤ P.totalDegree := by
  classical
  change (MvPolynomial.eval₂ MvPolynomial.C Q P).totalDegree ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (Q i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hQ i))
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

lemma matrix_mul_degree {σ : Type*} {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) (MvPolynomial σ ℝ))
    (B : Matrix (Fin n) (Fin p) (MvPolynomial σ ℝ)) (u v : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ u) (hB : ∀ i j, (B i j).totalDegree ≤ v) :
    ∀ i j, ((A * B) i j).totalDegree ≤ u + v := by
  intro i j
  rw [Matrix.mul_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hA i k) (hB k j))

lemma matrix_det_degree {σ : Type*} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) : A.det.totalDegree ≤ n * d := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  simp only [Units.smul_def]
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i : Fin n, (A (s i) i).totalDegree ≤ ∑ _i : Fin n, d := Finset.sum_le_sum (fun i _ => hA (s i) i)
    _ = n * d := by simp

lemma matrix_adjugate_degree {σ : Type*} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) :
    ∀ i j, (A.adjugate i j).totalDegree ≤ (n - 1) * d := by
  cases n with
  | zero => intro i; exact i.elim0
  | succ n =>
    intro i j
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hs : ((-1 : MvPolynomial σ ℝ) ^ ((j : ℕ) + (i : ℕ))).totalDegree ≤ 0 :=
      (MvPolynomial.totalDegree_pow _ _).trans (by simp)
    exact (Nat.add_le_add hs (matrix_det_degree (A.submatrix j.succAbove i.succAbove) d
      (fun k l => hA _ _))).trans_eq (by simp)

def constantMatrix {σ : Type*} {n p : ℕ} (L : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin p) (MvPolynomial σ ℝ) := fun i j => MvPolynomial.C (L i j)

def gramPolynomial {σ : Type*} {n p : ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) (MvPolynomial σ ℝ) :=
  (constantMatrix (σ := σ) L)ᵀ * Ω * constantMatrix (σ := σ) L

def residualPolynomial {σ : Type*} {n p : ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ) :=
  (gramPolynomial Ω L).det • 1 - Ω * constantMatrix (σ := σ) L *
    (gramPolynomial Ω L).adjugate * (constantMatrix (σ := σ) L)ᵀ

lemma constantMatrix_degree {σ : Type*} {n p : ℕ} (L : Matrix (Fin n) (Fin p) ℝ) :
    ∀ i j, ((constantMatrix (σ := σ) L : Matrix _ _ (MvPolynomial σ ℝ)) i j).totalDegree ≤ 0 := by
  intro i j
  simp [constantMatrix]

theorem gramPolynomial_degree {σ : Type*} {n p : ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ)
    (hΩ : ∀ i j, (Ω i j).totalDegree ≤ 1) :
    ∀ i j, (gramPolynomial Ω L i j).totalDegree ≤ 1 := by
  exact matrix_mul_degree _ _ 1 0
    (matrix_mul_degree _ _ 0 1 (fun i j => constantMatrix_degree L j i) hΩ)
    (constantMatrix_degree L)

/-- Every actual polynomial residual entry has the source degree bound, including
zero-dimensional parent spaces. -/
theorem residualPolynomial_degree {σ : Type*} {n p : ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ)
    (hΩ : ∀ i j, (Ω i j).totalDegree ≤ 1) :
    ∀ i j, (residualPolynomial Ω L i j).totalDegree ≤ p := by
  have hg := gramPolynomial_degree Ω L hΩ
  have hd : (gramPolynomial Ω L).det.totalDegree ≤ p := by simpa using matrix_det_degree _ 1 hg
  have ha := matrix_adjugate_degree _ 1 hg
  intro i j
  unfold residualPolynomial
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · change ((gramPolynomial Ω L).det * (1 : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) i j).totalDegree ≤ p
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have h1 : ((1 : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) i j).totalDegree ≤ 0 := by
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    exact (Nat.add_le_add hd h1).trans_eq (Nat.add_zero p)
  · cases p with
    | zero =>
      simp [Matrix.mul_apply]
    | succ p =>
      have hΩL := matrix_mul_degree Ω (constantMatrix (σ := σ) L) 1 0 hΩ (constantMatrix_degree L)
      have hΩLa := matrix_mul_degree _ _ 1 p hΩL (by simpa using ha)
      simpa [Nat.add_comm] using
        matrix_mul_degree (Ω * constantMatrix (σ := σ) L * (gramPolynomial Ω L).adjugate)
          (constantMatrix (σ := σ) L)ᵀ (1 + p) 0 hΩLa
          (fun k l => constantMatrix_degree L l k) i j

def residualMomentPolynomial {σ : Type*} {n p : ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ)
    (u : Fin n → MvPolynomial σ ℝ) : Fin n → MvPolynomial σ ℝ :=
  (residualPolynomial Ω L).mulVec u

/-- The small source residual vector is a concrete polynomial of degree `p+1`. -/
theorem residualMomentPolynomial_degree {σ : Type*} {n p : ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ)
    (u : Fin n → MvPolynomial σ ℝ) (hΩ : ∀ i j, (Ω i j).totalDegree ≤ 1)
    (hu : ∀ i, (u i).totalDegree ≤ 1) :
    ∀ i, (residualMomentPolynomial Ω L u i).totalDegree ≤ p + 1 := by
  intro i
  unfold residualMomentPolynomial
  rw [Matrix.mulVec, dotProduct]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (Nat.add_le_add (residualPolynomial_degree Ω L hΩ i j) (hu j))

end RoughRegime.ProjectionPolynomial
