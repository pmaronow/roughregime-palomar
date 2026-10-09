module

public import RoughRegime.DesignStatistics
public import RoughRegime.LocalProjectionApproximation


@[expose] public section
/-! Literal packed-observable affine polynomials and the uniform source
population domain for the local projection approximation. -/
noncomputable section
open scoped Matrix.Norms.L2Operator BigOperators
open Matrix MvPolynomial MeasureTheory
namespace RoughRegime.Model
open RoughRegime.ProjectionFrame RoughRegime.ProjectionIncrementPolynomial

 def designMomentDimension (n : ℕ) : ℕ := Fintype.card (DesignMomentIndex n)
 def designMomentCoordinate (n : ℕ) : DesignMomentIndex n ≃ Fin (designMomentDimension n) :=
  Fintype.equivFin (DesignMomentIndex n)
 def designUpperIndex {n : ℕ} (i j : Fin n) : DesignUpperPair n :=
  ⟨(min i j, max i j), min_le_max⟩
 def designGramPolynomial (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (designMomentDimension n)) ℝ) :=
  fun i j => X (designMomentCoordinate n (Sum.inl (designUpperIndex i j)))
 def designFirstPolynomial (n : ℕ) : Fin n → MvPolynomial (Fin (designMomentDimension n)) ℝ :=
  fun i => X (designMomentCoordinate n (Sum.inr (Sum.inl i)))
 def designSecondPolynomial (n : ℕ) : Fin n → MvPolynomial (Fin (designMomentDimension n)) ℝ :=
  fun i => X (designMomentCoordinate n (Sum.inr (Sum.inr i)))

 def designMatrix {n : ℕ} (x : Fin (designMomentDimension n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (designGramPolynomial n).map (MvPolynomial.eval x)
 def designFirst {n : ℕ} (x : Fin (designMomentDimension n) → ℝ) : Fin n → ℝ :=
  fun i => MvPolynomial.eval x (designFirstPolynomial n i)
 def designSecond {n : ℕ} (x : Fin (designMomentDimension n) → ℝ) : Fin n → ℝ :=
  fun i => MvPolynomial.eval x (designSecondPolynomial n i)

lemma designMatrix_isHermitian {n : ℕ} (x : Fin (designMomentDimension n) → ℝ) :
    (designMatrix x).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  simp [designMatrix, designGramPolynomial, designUpperIndex, min_comm, max_comm]

lemma designGramPolynomial_degree (n : ℕ) (i j : Fin n) :
    (designGramPolynomial n i j).totalDegree ≤ 1 := by simp [designGramPolynomial]
lemma designFirstPolynomial_degree (n : ℕ) (i : Fin n) :
    (designFirstPolynomial n i).totalDegree ≤ 1 := by simp [designFirstPolynomial]
lemma designSecondPolynomial_degree (n : ℕ) (i : Fin n) :
    (designSecondPolynomial n i).totalDegree ≤ 1 := by simp [designSecondPolynomial]

/-- The paper's fixed population domain, with every symmetric Gram entry and both
actual first moment vectors represented by literal packed coordinates. -/
 def designMomentSet (n : ℕ) (lo hi R : ℝ) : Set (Fin (designMomentDimension n) → ℝ) :=
  {x | spectrum ℝ (designMatrix x) ⊆ Set.Icc lo hi ∧
    ‖euclidean (designFirst x)‖ ≤ R ∧ ‖euclidean (designSecond x)‖ ≤ R}

 def designPackingCLM (n : ℕ) :
    (Matrix (Fin n) (Fin n) ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) →L[ℝ]
      (Fin (designMomentDimension n) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun d j => match (designMomentCoordinate n).symm j with
        | .inl ij => d.1 ij.1.1 ij.1.2
        | .inr (.inl i) => d.2.1 i
        | .inr (.inr i) => d.2.2 i
      map_add' := by
        intro d e
        funext j
        dsimp only [Pi.add_apply]
        cases hq : (designMomentCoordinate n).symm j with
        | inl ij => simp [hq]
        | inr i => cases i <;> simp [hq]
      map_smul' := by
        intro r d
        funext j
        dsimp only [Pi.smul_apply]
        cases hq : (designMomentCoordinate n).symm j with
        | inl ij => simp [hq]
        | inr i => cases i <;> simp [hq] }

lemma designPacking_reconstruct {n : ℕ} (x : Fin (designMomentDimension n) → ℝ) :
    designPackingCLM n (designMatrix x, euclidean (designFirst x), euclidean (designSecond x)) = x := by
  funext j
  change (match (designMomentCoordinate n).symm j with
    | .inl ij => designMatrix x ij.1.1 ij.1.2
    | .inr (.inl i) => designFirst x i
    | .inr (.inr i) => designSecond x i) = x j
  cases hq : (designMomentCoordinate n).symm j with
  | inl ij =>
    have he : designMomentCoordinate n (Sum.inl ij) = j := by
      rw [← hq]
      exact (designMomentCoordinate n).apply_symm_apply j
    simp only [designMatrix, Matrix.map_apply, designGramPolynomial, MvPolynomial.eval_X]
    have hu : designUpperIndex ij.1.1 ij.1.2 = ij := by
      apply Subtype.ext
      simp [designUpperIndex, min_eq_left ij.2, max_eq_right ij.2]
    rw [hu]
    exact congrArg x he
  | inr i =>
    have he : designMomentCoordinate n (Sum.inr i) = j := by
      rw [← hq]
      exact (designMomentCoordinate n).apply_symm_apply j
    cases i with
    | inl i => simpa [designFirst, designFirstPolynomial] using congrArg x he
    | inr i => simpa [designSecond, designSecondPolynomial] using congrArg x he

/-- The full spectral/moment domain is bounded; no bound on packed parameters is
assumed. This provides constants common to every model and every cell. -/
theorem designMomentSet_bounded (n : ℕ) (lo hi R : ℝ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    Bornology.IsBounded (designMomentSet n lo hi R) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖designPackingCLM n‖ * max hi R, ?_⟩
  intro x hx
  have hM := matrix_norm_le_hi lo hi hlo hhi (designMatrix x) (designMatrix_isHermitian x) hx.1
  have hd : ‖(designMatrix x, euclidean (designFirst x), euclidean (designSecond x))‖ ≤ max hi R := by
    simp only [Prod.norm_def]
    exact max_le (hM.trans (le_max_left _ _))
      ((max_le hx.2.1 hx.2.2).trans (le_max_right _ _))
  rw [← designPacking_reconstruct x]
  exact (designPackingCLM n).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_left hd (norm_nonneg _))

 def packedDesignPopulation (A : Parameters) (μ : Measure (Covariate A.d))
    (g a b : Covariate A.d → ℝ) {n : ℕ} (z : Fin n → Covariate A.d → ℝ) :
    Fin (designMomentDimension n) → ℝ :=
  fun j => designPopulation A μ g a b z ((designMomentCoordinate n).symm j)

lemma packedDesignPopulation_gram (A : Parameters) (μ : Measure (Covariate A.d))
    (g a b : Covariate A.d → ℝ) {n : ℕ} (z : Fin n → Covariate A.d → ℝ) :
    designMatrix (packedDesignPopulation A μ g a b z) = designGram μ g z := by
  ext i j
  simp only [designMatrix, Matrix.map_apply, designGramPolynomial, MvPolynomial.eval_X,
    packedDesignPopulation, Equiv.symm_apply_apply]
  change designGram μ g z (min i j) (max i j) = designGram μ g z i j
  by_cases hij : i ≤ j
  · simp [min_eq_left hij, max_eq_right hij]
  · rw [min_eq_right (le_of_not_ge hij), max_eq_left (le_of_not_ge hij)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)

lemma packedDesignPopulation_first (A : Parameters) (μ : Measure (Covariate A.d))
    (g a b : Covariate A.d → ℝ) {n : ℕ} (z : Fin n → Covariate A.d → ℝ) :
    designFirst (packedDesignPopulation A μ g a b z) = designMoment μ g z a := by
  funext i
  simp [designFirst, designFirstPolynomial, packedDesignPopulation, designPopulation]

lemma packedDesignPopulation_second (A : Parameters) (μ : Measure (Covariate A.d))
    (g a b : Covariate A.d → ℝ) {n : ℕ} (z : Fin n → Covariate A.d → ℝ) :
    designSecond (packedDesignPopulation A μ g a b z) = designMoment μ g z b := by
  funext i
  simp [designSecond, designSecondPolynomial, packedDesignPopulation, designPopulation]

end RoughRegime.Model
