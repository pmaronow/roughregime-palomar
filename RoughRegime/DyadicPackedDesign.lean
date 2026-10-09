module

public import RoughRegime.ModelLocalLemma
public import RoughRegime.DyadicFiniteDesign
public import RoughRegime.PolynomialCells
public import RoughRegime.LiftVariance


@[expose] public section
/-! Actual exclusive dyadic-cell observables and their literal aggregate packing. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

 def dyadicCellEquiv (A : Parameters) (j : ℕ) : Fin (2 ^ j) ≃ DyadicCell A.d j :=
  (Fintype.equivFinOfCardEq (dyadicCell_card A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd))).symm

 def dyadicPackedStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (j : ℕ) (o : Observation A Z) : Fin ((2 ^ j) * localMomentDimension A) → ℝ :=
  fun i => localDesignStatistic A F (dyadicCellEquiv A j (finProdFinEquiv.symm i).1) o (finProdFinEquiv.symm i).2

 def dyadicPackedMean (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (j : ℕ) :
    Fin ((2 ^ j) * localMomentDimension A) → ℝ :=
  fun i => dyadicDesignMean A F P (holderOrder A.β)
    (dyadicCellEquiv A j (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

 def dyadicPackedSelector (A : Parameters) {Z : Type*} [MeasurableSpace Z] (j : ℕ)
    (o : Observation A Z) : Fin (2 ^ j) :=
  (dyadicCellEquiv A j).symm (dyadicSelection A.d j o.1)

 theorem dyadicPackedStatistic_projection (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (j : ℕ) (c : Fin (2 ^ j)) (o : Observation A Z) :
    RoughRegime.PolynomialCells.cellProjection c (dyadicPackedStatistic A F j o) =
      WithLp.ofLp (localDesignStatistic A F (dyadicCellEquiv A j c) o) := by
  funext i
  simp only [RoughRegime.PolynomialCells.cellProjection_apply, dyadicPackedStatistic, Equiv.symm_apply_apply]

 theorem dyadicPackedMean_projection (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (j : ℕ) (c : Fin (2 ^ j)) :
    RoughRegime.PolynomialCells.cellProjection c (dyadicPackedMean A F P j) =
      dyadicDesignMean A F P (holderOrder A.β) (dyadicCellEquiv A j c) := by
  funext i
  simp only [RoughRegime.PolynomialCells.cellProjection_apply, dyadicPackedMean, Equiv.symm_apply_apply]

 theorem dyadicPackedSelector_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z] (j : ℕ) :
    Measurable (@dyadicPackedSelector A Z _ j) :=
  (measurable_of_countable (dyadicCellEquiv A j).symm).comp
    ((dyadicSelection_measurable A.d j).comp measurable_fst)

 theorem dyadicPackedSelector_eq_iff (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (j : ℕ) (o : Observation A Z) (c : Fin (2 ^ j)) :
    dyadicPackedSelector A j o = c ↔ dyadicSelection A.d j o.1 = dyadicCellEquiv A j c := by
  unfold dyadicPackedSelector
  constructor
  · intro h
    apply_fun dyadicCellEquiv A j at h
    simpa only [Equiv.apply_symm_apply] using h
  · intro h
    rw [h, Equiv.symm_apply_apply]

 theorem localDesignStatistic_integrable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) {j : ℕ} (c : DyadicCell A.d j) :
    Integrable (localDesignStatistic A F c) (P : Measure (Observation A Z)) :=
  dyadicFinDesignStatistic_integrable A F P (holderOrder A.β) c

 theorem dyadicPackedStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (j : ℕ) : Measurable (dyadicPackedStatistic A F j) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (PiLp.proj (p := 2) (β := fun _ : Fin (localMomentDimension A) => ℝ) (𝕜 := ℝ)
    (finProdFinEquiv.symm i).2).continuous.measurable.comp
      (localDesignStatistic_measurable A F (dyadicCellEquiv A j (finProdFinEquiv.symm i).1))

 theorem dyadicPackedStatistic_integrable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (j : ℕ) :
    Integrable (dyadicPackedStatistic A F j) (P : Measure (Observation A Z)) := by
  apply Integrable.of_eval
  intro i
  exact (PiLp.proj (p := 2) (β := fun _ : Fin (localMomentDimension A) => ℝ) (𝕜 := ℝ)
    (finProdFinEquiv.symm i).2).integrable_comp
      (localDesignStatistic_integrable A F P (dyadicCellEquiv A j (finProdFinEquiv.symm i).1))

 theorem dyadicPackedStatistic_coordinate_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (j : ℕ)
    (i : Fin ((2 ^ j) * localMomentDimension A)) :
    (∫ o, dyadicPackedStatistic A F j o i ∂(P : Measure (Observation A Z))) = dyadicPackedMean A F P j i := by
  let c := dyadicCellEquiv A j (finProdFinEquiv.symm i).1
  have he := (PiLp.proj (p := 2) (β := fun _ : Fin (localMomentDimension A) => ℝ) (𝕜 := ℝ)
    (finProdFinEquiv.symm i).2).integral_comp_comm (localDesignStatistic_integrable A F P c)
  change (∫ o, localDesignStatistic A F c o (finProdFinEquiv.symm i).2 ∂(P : Measure (Observation A Z))) =
    (∫ o, localDesignStatistic A F c o ∂(P : Measure (Observation A Z))) (finProdFinEquiv.symm i).2 at he
  exact he.trans (congrFun (localDesignStatistic_mean A F P c) (finProdFinEquiv.symm i).2)

 theorem dyadicPackedStatistic_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (j : ℕ) :
    (∫ o, dyadicPackedStatistic A F j o ∂(P : Measure (Observation A Z))) = dyadicPackedMean A F P j := by
  funext i
  let L : (Fin ((2 ^ j) * localMomentDimension A) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := L.integral_comp_comm (dyadicPackedStatistic_integrable A F P j)
  change (∫ o, dyadicPackedStatistic A F j o i ∂(P : Measure (Observation A Z))) =
    (∫ o, dyadicPackedStatistic A F j o ∂(P : Measure (Observation A Z))) i at h
  exact h.symm.trans (dyadicPackedStatistic_coordinate_integral A F P j i)

 theorem dyadicPartition_indicator_le_selector (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (j : ℕ) (c : Fin (2 ^ j)) (o : Observation A Z) :
    (dyadicPartitionCell (dyadicCellEquiv A j c)).indicator (fun _ => (1 : ℝ)) o.1 ≤
      RoughRegime.LiftVariance.cellIndicator (dyadicPackedSelector A j) c o := by
  by_cases hx : o.1 ∈ dyadicPartitionCell (dyadicCellEquiv A j c)
  · have hs : dyadicPackedSelector A j o = c := (dyadicPackedSelector_eq_iff A j o c).mpr hx.2
    simp [indicator_of_mem hx, RoughRegime.LiftVariance.cellIndicator, hs]
  · simp only [indicator_of_notMem hx]
    unfold RoughRegime.LiftVariance.cellIndicator
    split_ifs <;> norm_num

 theorem dyadicPackedStatistic_norm_support (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (j : ℕ) (c : Fin (2 ^ j)) (o : Observation A Z) :
    ‖(WithLp.toLp 2 (RoughRegime.PolynomialCells.cellProjection c (dyadicPackedStatistic A F j o)) :
      EuclideanSpace ℝ (Fin (localMomentDimension A)))‖ ≤
      dyadicDesignConstant A (holderOrder A.β) * (2 : ℝ) ^ j *
        RoughRegime.LiftVariance.cellIndicator (dyadicPackedSelector A j) c o := by
  rw [dyadicPackedStatistic_projection, WithLp.toLp_ofLp]
  exact (localDesignStatistic_norm_bound A F (dyadicCellEquiv A j c) o).trans
    (mul_le_mul_of_nonneg_left (dyadicPartition_indicator_le_selector A j c o)
      (mul_nonneg (zero_le_one.trans (dyadicDesignConstant_ge_one _ _)) (by positivity)))

 theorem dyadicPackedStatistic_coordinate_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (j : ℕ) (o : Observation A Z)
    (i : Fin ((2 ^ j) * localMomentDimension A)) :
    |dyadicPackedStatistic A F j o i| ≤ dyadicDesignConstant A (holderOrder A.β) * (2 : ℝ) ^ j := by
  let c := dyadicCellEquiv A j (finProdFinEquiv.symm i).1
  have hcoord := PiLp.norm_apply_le (localDesignStatistic A F c o) (finProdFinEquiv.symm i).2
  have hcell : (dyadicPartitionCell c).indicator (fun _ => (1 : ℝ)) o.1 ≤ 1 := by
    by_cases hx : o.1 ∈ dyadicPartitionCell c <;> simp [hx]
  have hnonneg : 0 ≤ dyadicDesignConstant A (holderOrder A.β) * (2 : ℝ) ^ j := by
    exact mul_nonneg (zero_le_one.trans (dyadicDesignConstant_ge_one _ _)) (by positivity)
  exact hcoord.trans ((localDesignStatistic_norm_bound A F c o).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcell hnonneg))

 theorem ModelWitness.covariate_mem_cube_ae {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)} (W : ModelWitness A F P) :
    ∀ᵐ o ∂(P : Measure (Observation A Z)), o.1 ∈ cube A.d := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  rw [W.marginal]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cube A.d))

 theorem dyadicPackedSelector_probability (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
    (j : ℕ) (c : Fin (2 ^ j)) :
    (P : Measure (Observation A Z)).real {o | dyadicPackedSelector A j o = c} ≤
      dyadicDesignConstant A (holderOrder A.β) / (2 : ℝ) ^ j := by
  have he : {o : Observation A Z | dyadicPackedSelector A j o = c} =ᵐ[(P : Measure (Observation A Z))]
      Prod.fst ⁻¹' dyadicPartitionCell (dyadicCellEquiv A j c) := by
    filter_upwards [W.covariate_mem_cube_ae] with o ho
    apply propext
    change (dyadicPackedSelector A j o = c) ↔
      o.1 ∈ cube A.d ∧ dyadicSelection A.d j o.1 = dyadicCellEquiv A j c
    rw [dyadicPackedSelector_eq_iff, and_iff_right ho]
  have hr := congrArg ENNReal.toReal (measure_congr he)
  change (P : Measure (Observation A Z)).real {o | dyadicPackedSelector A j o = c} =
    (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' dyadicPartitionCell (dyadicCellEquiv A j c)) at hr
  rw [hr]
  exact dyadicDesign_cell_probability A F P W (holderOrder A.β) (dyadicCellEquiv A j c)

end RoughRegime.Model
