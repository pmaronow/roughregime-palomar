module

public import RoughRegime.ProductResponseBaselines
public import RoughRegime.ModelUpperConsequences


@[expose] public section
/-! Actual upper brackets and parametric lower bounds for bounded-real
bilinear products, quadratic products, conditional covariance and variance. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Products

abbrev pairProductObservables (A : Model.Parameters) (hM : 1 ≤ A.M0) :=
  productObservables A hM firstResponse secondResponse firstResponse_measurable
    secondResponse_measurable firstResponse_bound secondResponse_bound

abbrev pairCovarianceObservables (A : Model.Parameters) (hM : 1 ≤ A.M0) :=
  covarianceObservables A hM firstResponse secondResponse firstResponse_measurable
    secondResponse_measurable firstResponse_bound secondResponse_bound

abbrev quadraticObservables (A : Model.Parameters) (hM : 1 ≤ A.M0) :=
  productObservables A hM (Subtype.val : BoundedResponse → ℝ) Subtype.val
    measurable_subtype_coe measurable_subtype_coe response_bound response_bound

abbrev varianceObservables (A : Model.Parameters) (hM : 1 ≤ A.M0) :=
  covarianceObservables A hM (Subtype.val : BoundedResponse → ℝ) Subtype.val
    measurable_subtype_coe measurable_subtype_coe response_bound response_bound

def bilinearTarget (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A PairResponse)) : ℝ :=
  ∫ o, ((P : Measure (Model.Observation A PairResponse))[firstResponse ∘ Prod.snd |
    Model.covariateInformation A PairResponse]) o *
    ((P : Measure (Model.Observation A PairResponse))[secondResponse ∘ Prod.snd |
      Model.covariateInformation A PairResponse]) o ∂(P : Measure (Model.Observation A PairResponse))

def quadraticTarget (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  ∫ o, ((P : Measure (Model.Observation A BoundedResponse))[
    (Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd |
      Model.covariateInformation A BoundedResponse]) o ^ 2 ∂(P : Measure (Model.Observation A BoundedResponse))

def conditionalCovarianceTarget (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A PairResponse)) : ℝ :=
  ∫ o, ConditionalExamples.conditionalCovariance (Model.covariateInformation A PairResponse)
    (firstResponse ∘ Prod.snd) (secondResponse ∘ Prod.snd)
      (P : Measure (Model.Observation A PairResponse)) o ∂(P : Measure (Model.Observation A PairResponse))

def conditionalVarianceTarget (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A BoundedResponse)) : ℝ :=
  ∫ o, condVar (Model.covariateInformation A BoundedResponse)
    ((Subtype.val : BoundedResponse → ℝ) ∘ Prod.snd)
      (P : Measure (Model.Observation A BoundedResponse)) o ∂(P : Measure (Model.Observation A BoundedResponse))

abbrev bilinearClass (A : Model.Parameters) := modelClass A firstResponse secondResponse
abbrev quadraticClass (A : Model.Parameters) :=
  modelClass A (Subtype.val : BoundedResponse → ℝ) Subtype.val

@[simp] theorem pairProduct_target (A : Model.Parameters) (hM : 1 ≤ A.M0) :
    Model.target A (pairProductObservables A hM) = bilinearTarget A := by
  funext P
  exact target_eq_product A hM _ _ _ _ _ _ P

@[simp] theorem pairCovariance_target (A : Model.Parameters) (hM : 1 ≤ A.M0) :
    Model.target A (pairCovarianceObservables A hM) = conditionalCovarianceTarget A := by
  funext P
  exact target_eq_conditional_covariance A hM _ _ _ _ _ _ P

@[simp] theorem quadratic_target (A : Model.Parameters) (hM : 1 ≤ A.M0) :
    Model.target A (quadraticObservables A hM) = quadraticTarget A := by
  funext P
  simpa only [quadraticTarget, pow_two] using target_eq_product A hM _ _ _ _ _ _ P

@[simp] theorem variance_target (A : Model.Parameters) (hM : 1 ≤ A.M0) :
    Model.target A (varianceObservables A hM) = conditionalVarianceTarget A := by
  funext P
  exact target_eq_conditional_variance A hM _ _ _ P

theorem bilinear_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1) :
    Model.UpperBracket (bilinearTarget A) (bilinearClass A) A.bracketParameters (A.nu : ℝ) := by
  have h := Model.model_upperBracket A (pairProductObservables A hM)
  rw [pairProduct_target, ← modelClass_eq_generic A (pairProductObservables A hM) rfl hd] at h
  exact h

theorem conditionalCovariance_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1) :
    Model.UpperBracket (conditionalCovarianceTarget A) (bilinearClass A) A.bracketParameters (A.nu : ℝ) := by
  have h := Model.model_upperBracket A (pairCovarianceObservables A hM)
  rw [pairCovariance_target, ← modelClass_eq_generic A (pairCovarianceObservables A hM) rfl hd] at h
  exact h

theorem quadratic_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1) :
    Model.UpperBracket (quadraticTarget A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) := by
  have h := Model.model_upperBracket A (quadraticObservables A hM)
  rw [quadratic_target, ← modelClass_eq_generic A (quadraticObservables A hM) rfl hd] at h
  exact h

theorem conditionalVariance_upperBracket (A : Model.Parameters) (hM : 1 ≤ A.M0) (hd : A.δ ≤ 1) :
    Model.UpperBracket (conditionalVarianceTarget A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) := by
  have h := Model.model_upperBracket A (varianceObservables A hM)
  rw [variance_target, ← modelClass_eq_generic A (varianceObservables A hM) rfl hd] at h
  exact h

theorem bilinear_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        Model.minimaxRMSE n (bilinearTarget A) (bilinearClass A) := by
  have h := bounded_pair_class_parametric_lower A (pairProductObservables A hM) rfl rfl rfl hlo hhi
  rw [pairProduct_target] at h
  simpa only [pairProductObservables, productObservables] using h

theorem conditionalCovariance_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        Model.minimaxRMSE n (conditionalCovarianceTarget A) (bilinearClass A) := by
  have h := bounded_pair_class_parametric_lower A (pairCovarianceObservables A hM) rfl rfl rfl hlo hhi
  rw [pairCovariance_target] at h
  simpa only [pairCovarianceObservables, covarianceObservables] using h

theorem quadratic_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        Model.minimaxRMSE n (quadraticTarget A) (quadraticClass A) := by
  have h := bounded_diagonal_class_parametric_lower A (quadraticObservables A hM) rfl rfl rfl hlo hhi hab
  rw [quadratic_target] at h
  simpa only [quadraticObservables, productObservables] using h

theorem conditionalVariance_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        Model.minimaxRMSE n (conditionalVarianceTarget A) (quadraticClass A) := by
  have h := bounded_diagonal_class_parametric_lower A (varianceObservables A hM) rfl rfl rfl hlo hhi hab
  rw [variance_target] at h
  simpa only [varianceObservables, covarianceObservables] using h

theorem parametric_lowerBracket {Ω : Type*} [MeasurableSpace Ω]
    (A : Model.Parameters) (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (htheta : 1 / 2 ≤ A.theta)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C) :
    Model.LowerBracket T C A.bracketParameters := by
  obtain ⟨c, hc, he⟩ := h
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 he
  refine ⟨c, hc, max 3 n0, le_max_left _ _, ?_⟩
  intro n hn
  refine ⟨?_, ?_⟩
  · dsimp only [Model.lowerBracketScale, Model.Parameters.bracketParameters]
    rw [ite_eq_right (not_lt.mpr htheta)]
    exact hn0 n ((le_max_right _ _).trans hn)
  · intro hsub
    exact False.elim ((not_lt.mpr htheta) hsub)

theorem bilinear_parametric_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (htheta : 1 / 2 ≤ A.theta) :
    Model.Bracket (bilinearTarget A) (bilinearClass A) A.bracketParameters (A.nu : ℝ) :=
  ⟨parametric_lowerBracket A _ _ htheta (bilinear_parametric_lower A hM hlo hhi),
    bilinear_upperBracket A hM ((le_max_left _ _).trans hlo.le)⟩

theorem conditionalCovariance_parametric_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (htheta : 1 / 2 ≤ A.theta) :
    Model.Bracket (conditionalCovarianceTarget A) (bilinearClass A) A.bracketParameters (A.nu : ℝ) :=
  ⟨parametric_lowerBracket A _ _ htheta (conditionalCovariance_parametric_lower A hM hlo hhi),
    conditionalCovariance_upperBracket A hM ((le_max_left _ _).trans hlo.le)⟩

theorem quadratic_parametric_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) (htheta : 1 / 2 ≤ A.theta) :
    Model.Bracket (quadraticTarget A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) :=
  ⟨parametric_lowerBracket A _ _ htheta (quadratic_parametric_lower A hM hlo hhi hab),
    quadratic_upperBracket A hM ((le_max_left _ _).trans hlo.le)⟩

theorem conditionalVariance_parametric_bracket (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hlo : max A.δ A.gminus < 1) (hhi : 1 < A.gplus) (hab : A.α = A.β) (htheta : 1 / 2 ≤ A.theta) :
    Model.Bracket (conditionalVarianceTarget A) (quadraticClass A) A.bracketParameters (A.nu : ℝ) :=
  ⟨parametric_lowerBracket A _ _ htheta (conditionalVariance_parametric_lower A hM hlo hhi hab),
    conditionalVariance_upperBracket A hM ((le_max_left _ _).trans hlo.le)⟩

end RoughRegime.Applications.Products
