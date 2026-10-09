module

public import RoughRegime.KernelExpressions


@[expose] public section
/-! Actual finite sums, products and determinants as kernel expressions. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.KernelExpressions

variable {p : ℕ} {I : Type*} {dims : I → ℕ}

def finiteSum : {n : ℕ} → (Fin n → Expression p dims) → Expression p dims
  | 0, _ => .polynomial 0
  | n + 1, f => .add (f 0) (finiteSum (fun i => f i.succ))

def finiteProd : {n : ℕ} → (Fin n → Expression p dims) → Expression p dims
  | 0, _ => .polynomial 1
  | n + 1, f => .mul (f 0) (finiteProd (fun i => f i.succ))

lemma finiteSum_series {n : ℕ} (lo hi : ℝ)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (t : Fin p → ℂ) (f : Fin n → Expression p dims) :
    (finiteSum f).series lo hi M t = ∑ i, (f i).series lo hi M t := by
  induction n with
  | zero => simp [finiteSum, Expression.series]
  | succ n ih => simp only [finiteSum, Expression.series, ih, Fin.sum_univ_succ]

lemma finiteProd_series {n : ℕ} (lo hi : ℝ)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (t : Fin p → ℂ) (f : Fin n → Expression p dims) :
    (finiteProd f).series lo hi M t = ∏ i, (f i).series lo hi M t := by
  induction n with
  | zero => simp [finiteProd, Expression.series]
  | succ n ih => simp only [finiteProd, Expression.series, ih, Fin.prod_univ_succ]

def indexedSum {J : Type*} [Fintype J] (f : J → Expression p dims) : Expression p dims :=
  finiteSum (fun i : Fin (Fintype.card J) => f ((Fintype.equivFin J).symm i))

def indexedProd {J : Type*} [Fintype J] (f : J → Expression p dims) : Expression p dims :=
  finiteProd (fun i : Fin (Fintype.card J) => f ((Fintype.equivFin J).symm i))

lemma indexedSum_series {J : Type*} [Fintype J] (lo hi : ℝ)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (t : Fin p → ℂ) (f : J → Expression p dims) :
    (indexedSum f).series lo hi M t = ∑ j, (f j).series lo hi M t := by
  rw [indexedSum, finiteSum_series]
  exact Fintype.sum_equiv (Fintype.equivFin J).symm _ _ (fun _ => rfl)

lemma indexedProd_series {J : Type*} [Fintype J] (lo hi : ℝ)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (t : Fin p → ℂ) (f : J → Expression p dims) :
    (indexedProd f).series lo hi M t = ∏ j, (f j).series lo hi M t := by
  rw [indexedProd, finiteProd_series]
  exact Fintype.prod_equiv (Fintype.equivFin J).symm _ _ (fun _ => rfl)

def kernelMatrixSeries (lo hi : ℝ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℂ) := fun a b =>
  PowerSeries.mk (fun k => RoughRegime.ComplexKernel.kernelCoefficient lo hi M k a b)

def determinantExpression (i : I) : Expression p dims :=
  indexedSum (fun σ : Equiv.Perm (Fin (dims i)) =>
    .mul (.polynomial (MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ)))
      (indexedProd (fun j : Fin (dims i) => .kernelEntry i (σ j) j)))

/-- The determinant expression represents the actual determinant of the actual
kernel entry power series, including the empty determinant. -/
theorem determinantExpression_series (lo hi : ℝ)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (t : Fin p → ℂ) (i : I) :
    (determinantExpression i : Expression p dims).series lo hi M t =
      (kernelMatrixSeries lo hi (M i t)).det := by
  rw [determinantExpression, indexedSum_series, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Expression.series, Expression.series, indexedProd_series]
  simp only [MvPolynomial.eval_C, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ,
    PowerSeries.smul_eq_C_mul]
  rfl

end RoughRegime.KernelExpressions
