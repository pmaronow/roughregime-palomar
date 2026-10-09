module

public import RoughRegime.ProductBrackets
public import RoughRegime.ModelMainLowerConsequences


@[expose] public section
/-! All four literal product/conditional covariance rows, including the
original rough probability clause, on actual bounded real response classes. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Products

theorem bilinear_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    Model.Bracket (bilinearTarget A) (bilinearClass A) A.bracketParameters (A.nu : ℝ) := by
  let F := pairProductObservables A hM
  have h := Model.model_bracket A F boundedPairBaseline 1
    (bounded_pair_baseline_nondegenerate A F rfl rfl rfl hlo hhi) zero_lt_one
    (Model.modelClass A F) (by rintro P ⟨W,_⟩; exact ⟨W⟩) (fun _ h => h)
  rw [pairProduct_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

theorem conditionalCovariance_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    Model.Bracket (conditionalCovarianceTarget A) (bilinearClass A) A.bracketParameters (A.nu : ℝ) := by
  let F := pairCovarianceObservables A hM
  have h := Model.model_bracket A F boundedPairBaseline 1
    (bounded_pair_baseline_nondegenerate A F rfl rfl rfl hlo hhi) zero_lt_one
    (Model.modelClass A F) (by rintro P ⟨W,_⟩; exact ⟨W⟩) (fun _ h => h)
  rw [pairCovariance_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

theorem quadratic_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    Model.Bracket (quadraticTarget A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) := by
  let F := quadraticObservables A hM
  have h := Model.model_bracket A F boundedDiagonalBaseline 1
    (bounded_diagonal_baseline_nondegenerate A F rfl rfl rfl hlo hhi hab) zero_lt_one
    (Model.modelClass A F) (by rintro P ⟨W,_⟩; exact ⟨W⟩) (fun _ h => h)
  rw [quadratic_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

theorem conditionalVariance_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    Model.Bracket (conditionalVarianceTarget A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) := by
  let F := varianceObservables A hM
  have h := Model.model_bracket A F boundedDiagonalBaseline 1
    (bounded_diagonal_baseline_nondegenerate A F rfl rfl rfl hlo hhi hab) zero_lt_one
    (Model.modelClass A F) (by rintro P ⟨W,_⟩; exact ⟨W⟩) (fun _ h => h)
  rw [variance_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

end RoughRegime.Applications.Products
