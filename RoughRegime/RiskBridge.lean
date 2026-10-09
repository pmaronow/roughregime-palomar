module

public import RoughRegime.Model
public import RoughRegime.Applications


@[expose] public section
/-!
# Risk transfer on the actual randomized iid experiment

The model's minimax L² error equals the square root of the minimax extended
mean squared error. The hardness-to-risk theorem therefore applies directly
to the model's arbitrary measurable estimators, including their seed coordinate.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace RoughRegime.Model

/-- The RMS error in the product experiment is precisely the square root of
its nonnegative squared-error integral, including infinite errors. -/
theorem randomizedExperiment_rmse_eq_squaredIntegral {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (P : ProbabilityMeasure Ω) (f : Estimator Ω n) (T : ℝ) :
    eLpNorm (fun o => f.val o - T) 2 (randomizedExperiment n P) =
      (∫⁻ o, ENNReal.ofReal ((f.val o - T) ^ 2) ∂randomizedExperiment n P) ^ (1 / 2 : ℝ) :=
  Applications.eLpNorm_two_eq_squaredIntegral _ _ (f.property.sub measurable_const)

/-- Equality of the two minimax RMSE conventions on the same experiment,
parameter class, and full space of measurable randomized estimators. -/
theorem minimaxRMSE_eq_squaredRisk {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) :
    minimaxRMSE n T C =
      Applications.minimaxRMSE (randomizedExperiment n) T C := by
  exact (Applications.minimaxRMSE_eq_eLpNorm (randomizedExperiment n) T C).symm

/-- The model and general experiment frameworks use the same tail risk. -/
theorem minimaxTail_eq_experimentTail {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) (t : ℝ) :
    minimaxTail n T C t =
      Applications.minimaxTail (randomizedExperiment n) T C t := rfl

/-- Lemma 18 instantiated in the actual iid observations with independent
uniform estimator randomness. -/
theorem hardness_to_risk {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω → ℝ) (Cn : ℕ → Set (ProbabilityMeasure Ω))
    (C : Set (ProbabilityMeasure Ω)) (tn : ℕ → ℝ)
    (ht : ∀ n, 0 ≤ tn n) (hC : ∀ᶠ n in atTop, Cn n ⊆ C)
    (hhard : (3 / 8 : ℝ≥0∞) ≤
      Filter.liminf (fun n => minimaxTail n T (Cn n) (tn n)) atTop) :
    ∀ᶠ n in atTop,
      (1 / 4 : ℝ≥0∞) ≤ minimaxTail n T C (tn n) ∧
      ENNReal.ofReal (tn n / 2) ≤ minimaxRMSE n T C := by
  have h := Applications.hardness_to_risk
    (fun n => randomizedExperiment n) T Cn C tn ht hC hhard
  simpa only [← minimaxTail_eq_experimentTail, ← minimaxRMSE_eq_squaredRisk] using h

/-- In particular the hard shrinking local classes imply eventual risk
bounds over the entire statistical model. -/
theorem local_hardness_to_model_risk (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (rn tn : ℕ → ℝ)
    (ht : ∀ n, 0 ≤ tn n)
    (hhard : (3 / 8 : ℝ≥0∞) ≤ Filter.liminf
      (fun n => minimaxTail n (target A F) (localClass A F π (rn n)) (tn n)) atTop) :
    ∀ᶠ n in atTop,
      (1 / 4 : ℝ≥0∞) ≤ minimaxTail n (target A F) (modelClass A F) (tn n) ∧
      ENNReal.ofReal (tn n / 2) ≤ minimaxRMSE n (target A F) (modelClass A F) := by
  apply hardness_to_risk (target A F) (fun n => localClass A F π (rn n))
    (modelClass A F) tn ht _ hhard
  exact Filter.Eventually.of_forall (fun n => localClass_subset A F π (rn n))

/-- Increasing a local neighborhood radius increases the corresponding class. -/
theorem localClass_mono_radius (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) {s r : ℝ} (hsr : s ≤ r) :
    localClass A F π s ⊆ localClass A F π r := by
  intro P hP
  obtain ⟨h, hh⟩ := hP
  refine ⟨h, hh.mono ?_⟩
  intro x hx
  exact ⟨hx.1.trans hsr, hx.2.1.trans hsr, hx.2.2.trans hsr⟩

/-- The same transfer holds over every class containing a fixed local
neighborhood once the hard neighborhoods shrink inside that radius. -/
theorem local_hardness_to_intermediate_risk (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (rn tn : ℕ → ℝ) (r : ℝ)
    (C : Set (ProbabilityMeasure (Observation A Z)))
    (hlocal : localClass A F π r ⊆ C)
    (hr : ∀ᶠ n in atTop, rn n ≤ r) (ht : ∀ n, 0 ≤ tn n)
    (hhard : (3 / 8 : ℝ≥0∞) ≤ Filter.liminf
      (fun n => minimaxTail n (target A F) (localClass A F π (rn n)) (tn n)) atTop) :
    ∀ᶠ n in atTop,
      (1 / 4 : ℝ≥0∞) ≤ minimaxTail n (target A F) C (tn n) ∧
      ENNReal.ofReal (tn n / 2) ≤ minimaxRMSE n (target A F) C := by
  apply hardness_to_risk (target A F) (fun n => localClass A F π (rn n)) C tn ht _ hhard
  filter_upwards [hr] with n hn
  exact (localClass_mono_radius A F π hn).trans hlocal

end RoughRegime.Model
