module

public import RoughRegime.ProductFullBrackets
public import RoughRegime.SmoothBracketTools


@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Products

theorem smooth_bilinear_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    Model.Bracket (bilinearTarget A) (bilinearClass A ∩ Model.smoothDensityClass A.d PairResponse) A.bracketParameters (A.nu : ℝ) := by
  let F := pairProductObservables A hM
  have h := Model.smooth_model_bracket A F boundedPairBaseline
    (bounded_pair_baseline_nondegenerate A F rfl rfl rfl hlo hhi)
  rw [pairProduct_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

theorem smooth_conditionalCovariance_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    Model.Bracket (conditionalCovarianceTarget A) (bilinearClass A ∩ Model.smoothDensityClass A.d PairResponse) A.bracketParameters (A.nu : ℝ) := by
  let F := pairCovarianceObservables A hM
  have h := Model.smooth_model_bracket A F boundedPairBaseline
    (bounded_pair_baseline_nondegenerate A F rfl rfl rfl hlo hhi)
  rw [pairCovariance_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

theorem smooth_quadratic_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    Model.Bracket (quadraticTarget A) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters (A.nu : ℝ) := by
  let F := quadraticObservables A hM
  have h := Model.smooth_model_bracket A F boundedDiagonalBaseline
    (bounded_diagonal_baseline_nondegenerate A F rfl rfl rfl hlo hhi hab)
  rw [quadratic_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

theorem smooth_conditionalVariance_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    Model.Bracket (conditionalVarianceTarget A) (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse) A.bracketParameters (A.nu : ℝ) := by
  let F := varianceObservables A hM
  have h := Model.smooth_model_bracket A F boundedDiagonalBaseline
    (bounded_diagonal_baseline_nondegenerate A F rfl rfl rfl hlo hhi hab)
  rw [variance_target,← modelClass_eq_generic A F rfl ((le_max_left _ _).trans hlo.le)] at h
  exact h

theorem smooth_quadratic_rough_hardness (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n (quadraticTarget A)
      (quadraticClass A ∩ Model.smoothDensityClass A.d BoundedResponse)
      (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  let O := quadraticObservables A hM
  have he := Model.smooth_model_rough_hardness A O boundedDiagonalBaseline
    (bounded_diagonal_baseline_nondegenerate A O rfl rfl rfl hlo hhi hab) hrough
  dsimp only [O] at he
  rw [quadratic_target,←modelClass_eq_generic A (quadraticObservables A hM) rfl
    ((le_max_left _ _).trans hlo.le)] at he
  exact he

end RoughRegime.Applications.Products
