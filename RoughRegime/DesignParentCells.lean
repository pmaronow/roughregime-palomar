module

public import RoughRegime.DesignCells


@[expose] public section
/-! Actual weighted parent polynomial spaces and their Taylor members. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model
variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}

def dyadicParentBasisFunction {d j : ℕ} (k : ℕ) (c : DyadicCell d j)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) : Covariate d → ℝ :=
  polynomialEvaluation (rectanglePolynomial (dyadicOrigin c) (dyadicSides c) (basisPolynomial d k i))

theorem dyadicParentBasisFunction_measurable {d j : ℕ} (k : ℕ) (c : DyadicCell d j)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) : Measurable (dyadicParentBasisFunction k c i) :=
  (polynomialEvaluation_continuous _).measurable

theorem dyadicParentBasisFunction_uniform_bound (d k : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (j : ℕ) (c : DyadicCell d j) i x, x ∈ dyadicRectangle c →
      |dyadicParentBasisFunction k c i x| ≤ B := by
  obtain ⟨B, hB, hb⟩ := rectangleBasis_uniform_bound (d := d) k
  exact ⟨B, hB, fun j c i x hx => by
    unfold dyadicParentBasisFunction
    rw [rectanglePolynomial_eval]
    exact hb _ _ (dyadicSides_pos c) i x (by rwa [← dyadicRectangle_eq_rectangle])⟩

theorem ModelWitness.parentFunction_memLp (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (i : Fin (Module.finrank ℝ (polynomialLpSpace A.d k))) :
    MemLp (dyadicParentBasisFunction k c i) 2 (W.cellDesignMeasure c) := by
  haveI := W.cellDesignMeasure_finite c
  obtain ⟨B, _, hb⟩ := dyadicParentBasisFunction_uniform_bound A.d k
  apply MemLp.of_bound (dyadicParentBasisFunction_measurable k c i).aestronglyMeasurable B
  filter_upwards [W.cellDesign_ae_rectangle c] with x hx
  simpa only [Real.norm_eq_abs] using hb j c i x hx

def ModelWitness.weightedParentBasis (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (i : Fin (Module.finrank ℝ (polynomialLpSpace A.d k))) :
    Lp ℝ 2 (W.cellDesignMeasure c) :=
  (W.parentFunction_memLp k c i).toLp (dyadicParentBasisFunction k c i)

theorem ModelWitness.weightedParentBasis_ae (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) (i : Fin (Module.finrank ℝ (polynomialLpSpace A.d k))) :
    W.weightedParentBasis k c i =ᵐ[W.cellDesignMeasure c] dyadicParentBasisFunction k c i :=
  (W.parentFunction_memLp k c i).coeFn_toLp

theorem dyadicParentBasis_ae_function {d j : ℕ} (k : ℕ) (c : DyadicCell d j)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    dyadicParentBasis k c i =ᵐ[rectangleVolume (dyadicOrigin c) (dyadicSides c)] dyadicParentBasisFunction k c i :=
  rectangleBasis_ae k _ _ (dyadicSides_pos c) i

theorem ModelWitness.weighted_polynomial_parent_member (W : ModelWitness A F P) {j k : ℕ}
    (c : DyadicCell A.d j) (p : MvPolynomial (Fin A.d) ℝ) (hp : p.totalDegree ≤ k)
    (hmem : MemLp (polynomialEvaluation p) 2 (W.cellDesignMeasure c)) :
    hmem.toLp (polynomialEvaluation p) ∈ HilbertGram.basisSpan (W.weightedParentBasis k c) := by
  exact transfer_parentSpan _ _ (W.cellDesignMeasure_ac c)
    (dyadicParentBasis k c) (W.weightedParentBasis k c) (dyadicParentBasisFunction k c)
    (dyadicParentBasis_ae_function k c) (W.weightedParentBasis_ae k c)
    (dyadicPolynomialLp c p) (hmem.toLp (polynomialEvaluation p)) (polynomialEvaluation p)
    (dyadicPolynomialLp_ae c p) hmem.coeFn_toLp (dyadicPolynomialLp_mem_parentSpan c p hp)

theorem ModelWitness.weighted_parent_span_mono (W : ModelWitness A F P) {j k l : ℕ}
    (c : DyadicCell A.d j) (hkl : k ≤ l) :
    HilbertGram.basisSpan (W.weightedParentBasis k c) ≤ HilbertGram.basisSpan (W.weightedParentBasis l c) := by
  apply Submodule.span_le.mpr
  rintro f ⟨i, rfl⟩
  exact W.weighted_polynomial_parent_member c _
    (((rectanglePolynomial_degree _ _ _).trans (basisPolynomial_degree _ _ _)).trans hkl)
    (W.parentFunction_memLp k c i)

theorem ModelWitness.actual_holder_parent_approximation (W : ModelWitness A F P) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (c : DyadicCell A.d j) (f : Covariate A.d → ℝ)
      (hf : Measurable f) (hh : f ∈ holderBall t A.H),
      ∃ q : Lp ℝ 2 (W.cellDesignMeasure c),
        q ∈ HilbertGram.basisSpan (W.weightedParentBasis (holderOrder t) c) ∧
        ‖(W.holder_memLp_cell c f hf t hh).toLp f - q‖ ≤ C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ t := by
  obtain ⟨C, hC, hb⟩ := W.actual_holder_cell_approximation t
  refine ⟨C, hC, ?_⟩
  intro j c f hf hh
  obtain ⟨hq, hdegree, herror⟩ := hb j c f hf hh
  exact ⟨hq.toLp _, W.weighted_polynomial_parent_member c _ hdegree hq, herror⟩

end RoughRegime.Model
