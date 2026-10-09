module

public import RoughRegime.DyadicFiniteBasis


@[expose] public section
/-! Genuine nesting and polynomial membership of the transported parent spaces. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

theorem holderOrder_monotone : Monotone holderOrder := by
  intro s t hst
  exact Nat.sub_le_sub_right (Nat.ceil_mono hst) 1

theorem dyadicParentBasis_eq_polynomial {d j : ℕ} (k : ℕ) (c : DyadicCell d j)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    dyadicParentBasis k c i = dyadicPolynomialLp c
      (rectanglePolynomial (dyadicOrigin c) (dyadicSides c) (basisPolynomial d k i)) := by
  apply Lp.ext
  exact (rectangleBasis_ae k _ _ (dyadicSides_pos c) i).trans
    (dyadicPolynomialLp_ae c _).symm

theorem dyadicParentBasis_span_mono {d j : ℕ} (c : DyadicCell d j) {k l : ℕ} (hkl : k ≤ l) :
    HilbertGram.basisSpan (dyadicParentBasis k c) ≤ HilbertGram.basisSpan (dyadicParentBasis l c) := by
  apply Submodule.span_le.mpr
  rintro f ⟨i, rfl⟩
  rw [dyadicParentBasis_eq_polynomial]
  apply dyadicPolynomialLp_mem_parentSpan
  exact ((rectanglePolynomial_degree _ _ _).trans (basisPolynomial_degree _ _ _)).trans hkl

theorem dyadicTaylorPolynomial_mem_parentSpan {d j : ℕ} (c : DyadicCell d j)
    (f : Covariate d → ℝ) (t : ℝ) :
    dyadicPolynomialLp c (holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)) ∈
      HilbertGram.basisSpan (dyadicParentBasis (holderOrder t) c) :=
  dyadicPolynomialLp_mem_parentSpan c _ (holderTaylorPolynomial_degree _ _ _)

theorem dyadic_parent_matrices_nested {d j k l : ℕ} (hd : 0 < d) (c : DyadicCell d j)
    (hkl : k ≤ l) :
    ∃ (La : Matrix (Fin (dyadicChildDimension d l)) (Fin (Module.finrank ℝ (polynomialLpSpace d k))) ℝ)
      (Lb : Matrix (Fin (dyadicChildDimension d l)) (Fin (Module.finrank ℝ (polynomialLpSpace d l))) ℝ),
      La.transpose * La = 1 ∧ Lb.transpose * Lb = 1 ∧
      HilbertGram.parentBasis (dyadicFinChildBasis hd l c) La = dyadicParentBasis k c ∧
      HilbertGram.parentBasis (dyadicFinChildBasis hd l c) Lb = dyadicParentBasis l c ∧
      HilbertGram.basisSpan (HilbertGram.parentBasis (dyadicFinChildBasis hd l c) La) ≤
        HilbertGram.basisSpan (HilbertGram.parentBasis (dyadicFinChildBasis hd l c) Lb) := by
  obtain ⟨La, hLa, ha⟩ := dyadic_parent_matrix hd c hkl
  obtain ⟨Lb, hLb, hb⟩ := dyadic_parent_matrix hd c (le_refl l)
  refine ⟨La, Lb, hLa, hLb, ha, hb, ?_⟩
  rw [ha, hb]
  exact dyadicParentBasis_span_mono c hkl

end RoughRegime.Model
