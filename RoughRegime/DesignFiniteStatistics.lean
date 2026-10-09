module

public import RoughRegime.DesignStatistics


@[expose] public section
/-! Isometric finite-coordinate reindexing of the literal design statistics. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory
open scoped ENNReal

 def designFinReindex (n : ℕ) : EuclideanSpace ℝ (DesignMomentIndex n) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (Fintype.card (DesignMomentIndex n))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (DesignMomentIndex n))

 def designFinStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (C : Set (Covariate A.d)) (K : ℝ) : Observation A Z →
    EuclideanSpace ℝ (Fin (Fintype.card (DesignMomentIndex n))) :=
  fun o => designFinReindex n (designStatistic A F z C K o)

 def designFinPopulation (A : Parameters) (μ : Measure (Covariate A.d))
    (g a b : Covariate A.d → ℝ) {n : ℕ} (z : Fin n → Covariate A.d → ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card (DesignMomentIndex n))) :=
  designFinReindex n (designPopulation A μ g a b z)

 theorem designFinPopulation_apply (A : Parameters) (μ : Measure (Covariate A.d))
    (g a b : Covariate A.d → ℝ) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (i : Fin (Fintype.card (DesignMomentIndex n))) :
    designFinPopulation A μ g a b z i =
      designPopulation A μ g a b z ((Fintype.equivFin (DesignMomentIndex n)).symm i) := rfl

 theorem designFinStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (hz : ∀ i, Measurable (z i)) (C : Set (Covariate A.d)) (hC : MeasurableSet C) (K : ℝ) :
    Measurable (designFinStatistic A F z C K) :=
  (designFinReindex n).continuous.measurable.comp (designStatistic_measurable A F z hz C hC K)

 theorem designFinStatistic_norm (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (C : Set (Covariate A.d)) (K : ℝ) (o : Observation A Z) :
    ‖designFinStatistic A F z C K o‖ = ‖designStatistic A F z C K o‖ :=
  (designFinReindex n).norm_map _

 theorem designFinStatistic_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    {n : ℕ} (z : Fin n → Covariate A.d → ℝ) (hz : ∀ i, Measurable (z i))
    (B : ℝ) (hB : 1 ≤ B) (hzB : ∀ i x, |z i x| ≤ B)
    (C : Set (Covariate A.d)) (hC : MeasurableSet C) (K : ℝ) (hK : 0 ≤ K) :
    (∫ o, designFinStatistic A F z C K o ∂(P : Measure (Observation A Z))) =
      designFinPopulation A (ENNReal.ofReal K • (cubeVolume A.d).restrict C)
        (fun x => h.w x * h.p x) h.a h.b z := by
  change (∫ o, (designFinReindex n).toLinearIsometry (designStatistic A F z C K o) ∂(P : Measure (Observation A Z))) = _
  rw [(designFinReindex n).toLinearIsometry.integral_comp_comm,
    designStatistic_integral A F P h z hz B hB hzB C hC K hK]
  rfl

end RoughRegime.Model
