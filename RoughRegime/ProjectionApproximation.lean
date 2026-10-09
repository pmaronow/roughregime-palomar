module

public import RoughRegime.ProjectionPolynomial
public import RoughRegime.CombinedAnalytic
public import RoughRegime.ProjectionFrame


@[expose] public section
/-! Concrete source Gram-residual polynomial approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial RealInnerProductSpace
namespace RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionPolynomial RoughRegime.CombinedPolynomial
open RoughRegime.CombinedAnalytic RoughRegime.ProjectionGram
open RoughRegime.HilbertGram RoughRegime.ProjectionFrame

lemma constantMatrix_eval {σ : Type*} {n p : ℕ} (x : σ → ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) :
    (constantMatrix (σ := σ) L).map (MvPolynomial.eval x) = L := by
  ext i j
  simp [constantMatrix, Matrix.map_apply]

lemma gramPolynomial_eval {σ : Type*} {n p : ℕ} (x : σ → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ) :
    (gramPolynomial Ω L).map (MvPolynomial.eval x) =
      ProjectionGram.gram (Ω.map (MvPolynomial.eval x)) L := by
  unfold gramPolynomial ProjectionGram.gram
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    constantMatrix_eval]

lemma residualPolynomial_eval {σ : Type*} {n p : ℕ} (x : σ → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ) :
    (residualPolynomial Ω L).map (MvPolynomial.eval x) =
      polynomialResidual (Ω.map (MvPolynomial.eval x)) L := by
  unfold residualPolynomial polynomialResidual
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, constantMatrix_eval]
  have hadj := (MvPolynomial.eval x).map_adjugate (gramPolynomial Ω L)
  have hdet := (MvPolynomial.eval x).map_det (gramPolynomial Ω L)
  change (gramPolynomial Ω L).adjugate.map (MvPolynomial.eval x) =
    ((gramPolynomial Ω L).map (MvPolynomial.eval x)).adjugate at hadj
  rw [hadj, gramPolynomial_eval]
  change MvPolynomial.eval x (gramPolynomial Ω L).det =
    ((gramPolynomial Ω L).map (MvPolynomial.eval x)).det at hdet
  rw [gramPolynomial_eval] at hdet
  rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), hdet]

lemma residualMomentPolynomial_eval {σ : Type*} {n p : ℕ} (x : σ → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)) (L : Matrix (Fin n) (Fin p) ℝ)
    (u : Fin n → MvPolynomial σ ℝ) :
    (fun i => MvPolynomial.eval x (residualMomentPolynomial Ω L u i)) =
      (polynomialResidual (Ω.map (MvPolynomial.eval x)) L).mulVec
        (fun i => MvPolynomial.eval x (u i)) := by
  funext i
  rw [residualMomentPolynomial, RingHom.map_mulVec, residualPolynomial_eval]
  rfl

def polynomialEntryValuation {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ)) :
    Variables n dims → MvPolynomial σ ℝ
  | Sum.inl ab => Ω ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2

def truncationPolynomialMatrix {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ)) (m : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ) := fun a b =>
  MvPolynomial.eval₂Hom MvPolynomial.C (polynomialEntryValuation Ω M)
    (truncationEntryPolynomial n dims lo hi a b m)

/-- The actual inverse/determinant truncation remains degree `m` after all Gram
entries have been substituted as affine moment polynomials. -/
theorem truncationPolynomialMatrix_degree {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ))
    (hΩ : ∀ a b, (Ω a b).totalDegree ≤ 1)
    (hM : ∀ i a b, (M i a b).totalDegree ≤ 1) (m : ℕ) :
    ∀ a b, (truncationPolynomialMatrix lo hi Ω M m a b).totalDegree ≤ m := by
  intro a b
  apply (affine_substitution_degree _ _ ?_).trans
    (truncationEntryPolynomial_degree n dims lo hi a b m)
  intro v
  cases v with
  | inl ab => exact hΩ ab.1 ab.2
  | inr iab => exact hM iab.1 iab.2.1 iab.2.2

/-- Exact evaluation of the concrete substituted polynomial matrix. -/
theorem truncationPolynomialMatrix_eval {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (x : σ → ℝ) (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ)) (m : ℕ) :
    (truncationPolynomialMatrix lo hi Ω M m).map (MvPolynomial.eval x) =
      truncationMatrix lo hi (Ω.map (MvPolynomial.eval x))
        (fun i => (M i).map (MvPolynomial.eval x)) m := by
  ext a b
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C _ _) = _
  rw [MvPolynomial.eval_eval₂]
  have he : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℝ := by
    ext r
    simp
  rw [he]
  change MvPolynomial.eval₂ (RingHom.id ℝ) _ _ = MvPolynomial.eval₂ (RingHom.id ℝ) _ _
  congr 1
  funext v
  cases v <;> rfl

def bilinearPolynomial {σ : Type*} {n : ℕ}
    (u : Fin n → MvPolynomial σ ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (v : Fin n → MvPolynomial σ ℝ) : MvPolynomial σ ℝ := u ⬝ᵥ S.mulVec v

lemma bilinearPolynomial_degree {σ : Type*} {n : ℕ}
    (u : Fin n → MvPolynomial σ ℝ) (S : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (v : Fin n → MvPolynomial σ ℝ) (a m b : ℕ)
    (hu : ∀ i, (u i).totalDegree ≤ a) (hS : ∀ i j, (S i j).totalDegree ≤ m)
    (hv : ∀ i, (v i).totalDegree ≤ b) :
    (bilinearPolynomial u S v).totalDegree ≤ a + m + b := by
  unfold bilinearPolynomial
  rw [dotProduct]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hm : (S.mulVec v i).totalDegree ≤ m + b := by
    rw [Matrix.mulVec, dotProduct]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hS i j) (hv j))
  exact (Nat.add_le_add (hu i) hm).trans_eq (Nat.add_assoc a m b).symm

lemma bilinearPolynomial_eval {σ : Type*} {n : ℕ} (x : σ → ℝ)
    (u : Fin n → MvPolynomial σ ℝ) (S : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (v : Fin n → MvPolynomial σ ℝ) :
    MvPolynomial.eval x (bilinearPolynomial u S v) =
      (fun i => MvPolynomial.eval x (u i)) ⬝ᵥ
        (S.map (MvPolynomial.eval x)).mulVec (fun i => MvPolynomial.eval x (v i)) := by
  rw [bilinearPolynomial, RingHom.map_dotProduct]
  congr 1
  funext i
  exact (MvPolynomial.eval x).map_mulVec S v i

end RoughRegime.ProjectionApproximation
