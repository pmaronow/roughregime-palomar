module

public import RoughRegime.RectangleTransport
public import RoughRegime.ProjectionPolynomial


@[expose] public section
/-! Actual polynomial representatives under the source affine cell transport. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators ENNReal
namespace RoughRegime.Model

def rectangleCoordinatePolynomial {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (i : Fin d) : MvPolynomial (Fin d) ℝ := C ((s i)⁻¹) * (X i - C (o i))

theorem rectangleCoordinatePolynomial_degree {d : ℕ} (o : Covariate d)
    (s : Fin d → ℝ) (i : Fin d) : (rectangleCoordinatePolynomial o s i).totalDegree ≤ 1 := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_sub _ _).trans (by simp)

@[simp] theorem rectangleCoordinatePolynomial_eval {d : ℕ} (o : Covariate d)
    (s : Fin d → ℝ) (i : Fin d) (x : Covariate d) :
    polynomialEvaluation (rectangleCoordinatePolynomial o s i) x = rectangleCoords o s x i := by
  simp [polynomialEvaluation, rectangleCoordinatePolynomial, rectangleCoords, mul_sub]

def rectanglePolynomial {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  eval₂Hom C (rectangleCoordinatePolynomial o s) p

theorem rectanglePolynomial_degree {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) : (rectanglePolynomial o s p).totalDegree ≤ p.totalDegree :=
  ProjectionPolynomial.affine_substitution_degree p (rectangleCoordinatePolynomial o s)
    (rectangleCoordinatePolynomial_degree o s)

@[simp] theorem rectanglePolynomial_eval {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (x : Covariate d) :
    polynomialEvaluation (rectanglePolynomial o s p) x =
      polynomialEvaluation p (rectangleCoords o s x) := by
  change eval₂ (RingHom.id ℝ) (fun i => x i)
    (eval₂ C (rectangleCoordinatePolynomial o s) p) = _
  rw [← eval₂_assoc]
  have he : (fun i => eval₂ (RingHom.id ℝ) (fun j => x j)
      (rectangleCoordinatePolynomial o s i)) = (fun i => rectangleCoords o s x i) := by
    funext i
    exact rectangleCoordinatePolynomial_eval o s i x
  rw [he]
  rfl

theorem rectangleBasis_ae {d : ℕ} (k : ℕ) (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    rectangleBasis k o s hs i =ᵐ[rectangleVolume o s]
      polynomialEvaluation (rectanglePolynomial o s (basisPolynomial d k i)) := by
  have h1 := Lp.coeFn_compMeasurePreserving
    (polynomialToLp d (basisPolynomial d k i)) (rectangleCoords_preserving o s hs)
  have h2 := (rectangleCoords_preserving o s hs).quasiMeasurePreserving.ae_eq_comp
    (polynomialToLp_ae (basisPolynomial d k i))
  exact h1.trans (h2.trans (Filter.Eventually.of_forall (fun x => (rectanglePolynomial_eval o s _ x).symm)))

end RoughRegime.Model
