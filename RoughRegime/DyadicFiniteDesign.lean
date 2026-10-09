module

public import RoughRegime.DesignFiniteStatistics
public import RoughRegime.DesignDyadicPopulation


@[expose] public section
/-! The paper's literal finite-dimensional known dyadic observable and its mean. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

 def dyadicFinDesignStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    Observation A Z → EuclideanSpace ℝ (Fin (designMomentDimension (dyadicChildDimension A.d k))) :=
  fun o => designFinReindex (dyadicChildDimension A.d k) (dyadicDesignStatistic A F k c o)

 theorem dyadicFinDesignStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    Measurable (dyadicFinDesignStatistic A F k c) :=
  (designFinReindex _).continuous.measurable.comp (dyadicDesignStatistic_measurable A F k c)

 theorem dyadicFinDesignStatistic_norm_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) (o : Observation A Z) :
    ‖dyadicFinDesignStatistic A F k c o‖ ≤ dyadicDesignConstant A k * (2 : ℝ) ^ j *
      (dyadicPartitionCell c).indicator (fun _ => (1 : ℝ)) o.1 := by
  exact ((designFinReindex (dyadicChildDimension A.d k)).norm_map
    (dyadicDesignStatistic A F k c o)).le.trans (dyadicDesignStatistic_norm_bound A F k c o)

 theorem dyadicFinDesignStatistic_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    (∫ o, dyadicFinDesignStatistic A F k c o ∂(P : Measure (Observation A Z))) =
      WithLp.toLp 2 (dyadicDesignMean A F P k c) := by
  change (∫ o, (designFinReindex _).toLinearIsometry (dyadicDesignStatistic A F k c o)
    ∂(P : Measure (Observation A Z))) = _
  rw [(designFinReindex _).toLinearIsometry.integral_comp_comm]
  rfl

 theorem dyadicFinDesignStatistic_integrable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    Integrable (dyadicFinDesignStatistic A F k c) (P : Measure (Observation A Z)) := by
  have hr : Integrable (dyadicDesignStatistic A F k c) (P : Measure (Observation A Z)) :=
    designStatistic_integrable A F P _ (dyadicFinChildBasisFunction_measurable _ _ _)
      _ (dyadicDesignBasisBound_ge_one _ _) (dyadicFinChildBasisFunction_bound _ _ _)
      _ (dyadicPartitionCell_measurable c) _ (by positivity)
  exact (designFinReindex _).integrable_comp_iff.mpr hr

end RoughRegime.Model
