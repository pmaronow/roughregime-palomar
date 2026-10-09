module

public import RoughRegime.RectanglePolynomials


@[expose] public section
/-! Exact polynomial expansion in the actual finite orthonormal reference basis. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem basisPolynomial_expansion {d k : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (hp : p.totalDegree ≤ k) :
    ∃ c : Fin (Module.finrank ℝ (polynomialLpSpace d k)) → ℝ,
      (∑ i, c i • basisPolynomial d k i) = p := by
  classical
  have hm : polynomialToLp d p ∈ polynomialLpSpace d k :=
    ⟨p, mem_polynomialSpace_of_degree p hp, rfl⟩
  let v : polynomialLpSpace d k := ⟨polynomialToLp d p, hm⟩
  refine ⟨fun i => (polynomialLpBasis d k).repr v i, ?_⟩
  apply polynomialToLp_injective d
  rw [map_sum]
  simp only [map_smul, basisPolynomial_toLp]
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using
    congrArg (fun x : polynomialLpSpace d k => (x : Lp ℝ 2 (cubeVolume d)))
      ((polynomialLpBasis d k).sum_repr v)

theorem basisPolynomial_evaluation_expansion {d k : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (hp : p.totalDegree ≤ k) :
    ∃ c : Fin (Module.finrank ℝ (polynomialLpSpace d k)) → ℝ,
      ∀ x, polynomialEvaluation p x = ∑ i, c i * polynomialEvaluation (basisPolynomial d k i) x := by
  obtain ⟨c, hc⟩ := basisPolynomial_expansion p hp
  refine ⟨c, fun x => ?_⟩
  rw [← hc]
  simp [polynomialEvaluation, map_sum, Algebra.smul_def]

def rectangleEmbedCoordinatePolynomial {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (i : Fin d) : MvPolynomial (Fin d) ℝ := C (o i) + C (s i) * X i

theorem rectangleEmbedCoordinatePolynomial_degree {d : ℕ} (o : Covariate d)
    (s : Fin d → ℝ) (i : Fin d) : (rectangleEmbedCoordinatePolynomial o s i).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · exact (totalDegree_mul _ _).trans (by simp)

@[simp] theorem rectangleEmbedCoordinatePolynomial_eval {d : ℕ} (o : Covariate d)
    (s : Fin d → ℝ) (i : Fin d) (x : Covariate d) :
    polynomialEvaluation (rectangleEmbedCoordinatePolynomial o s i) x = rectangleEmbed o s x i := by
  simp [polynomialEvaluation, rectangleEmbedCoordinatePolynomial, rectangleEmbed]

def rectangleEmbedPolynomial {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  eval₂Hom C (rectangleEmbedCoordinatePolynomial o s) p

theorem rectangleEmbedPolynomial_degree {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) : (rectangleEmbedPolynomial o s p).totalDegree ≤ p.totalDegree :=
  ProjectionPolynomial.affine_substitution_degree p (rectangleEmbedCoordinatePolynomial o s)
    (rectangleEmbedCoordinatePolynomial_degree o s)

@[simp] theorem rectangleEmbedPolynomial_eval {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (x : Covariate d) :
    polynomialEvaluation (rectangleEmbedPolynomial o s p) x =
      polynomialEvaluation p (rectangleEmbed o s x) := by
  change eval₂ (RingHom.id ℝ) (fun i => x i)
    (eval₂ C (rectangleEmbedCoordinatePolynomial o s) p) = _
  rw [← eval₂_assoc]
  have he : (fun i => eval₂ (RingHom.id ℝ) (fun j => x j)
      (rectangleEmbedCoordinatePolynomial o s i)) = (fun i => rectangleEmbed o s x i) := by
    funext i
    exact rectangleEmbedCoordinatePolynomial_eval o s i x
  rw [he]
  rfl

end RoughRegime.Model
