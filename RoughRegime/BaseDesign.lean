module

public import RoughRegime.DesignChildBlocks
public import RoughRegime.DesignPolynomial
public import RoughRegime.DesignFiniteStatistics
public import RoughRegime.DesignProjection


@[expose] public section
/-! Actual nonsplit base-cell observable and genuine base projection moments. -/
noncomputable section
namespace RoughRegime.Model
variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : MeasureTheory.ProbabilityMeasure (Observation A Z)}
open MeasureTheory Matrix Set
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

 def dyadicBaseCell (d : ℕ) : DyadicCell d 0 := fun i => ⟨0, by simp [axisDepth]⟩
 theorem dyadicBaseCell_unique {d : ℕ} (c : DyadicCell d 0) : c = dyadicBaseCell d := by
  funext i
  apply Fin.ext
  have h : (c i).val < 1 := by simpa [axisDepth] using (c i).isLt
  change (c i).val = 0
  omega

 theorem dyadicBaseCell_partition (d : ℕ) : dyadicPartitionCell (dyadicBaseCell d) = cube d := by
  ext x
  change (x ∈ cube d ∧ dyadicSelection d 0 x = dyadicBaseCell d) ↔ x ∈ cube d
  simp only [dyadicBaseCell_unique, and_true]

 theorem dyadicBaseCell_measure {d : ℕ} (hd : 0 < d) :
    rectangleVolume (dyadicOrigin (dyadicBaseCell d)) (dyadicSides (dyadicBaseCell d)) = cubeVolume d := by
  rw [dyadicRectangle_normalizedVolume hd, dyadicBaseCell_partition]
  simp only [pow_zero, ENNReal.ofReal_one, one_smul, cubeVolume]
  rw [Measure.restrict_restrict (measurableSet_cube d), inter_self]

 abbrev baseDimension (d k : ℕ) : ℕ := Module.finrank ℝ (polynomialLpSpace d k)
 theorem baseDimension_eq (d k : ℕ) : baseDimension d k = (d + k).choose d := polynomialLpSpace_finrank d k
 theorem baseDimension_pos (d k : ℕ) : 0 < baseDimension d k := by
  rw [baseDimension_eq]
  exact Nat.choose_pos (Nat.le_add_right d k)

 def baseBasisFunction (d k : ℕ) (i : Fin (baseDimension d k)) : Covariate d → ℝ :=
  (cube d).indicator (dyadicParentBasisFunction k (dyadicBaseCell d) i)
 def baseBasisBound (d k : ℕ) : ℝ := Classical.choose (dyadicParentBasisFunction_uniform_bound d k)
 theorem baseBasisBound_ge_one (d k : ℕ) : 1 ≤ baseBasisBound d k :=
  (Classical.choose_spec (dyadicParentBasisFunction_uniform_bound d k)).1
 theorem baseBasisFunction_measurable (d k : ℕ) (i : Fin (baseDimension d k)) :
    Measurable (baseBasisFunction d k i) :=
  (dyadicParentBasisFunction_measurable k (dyadicBaseCell d) i).indicator (measurableSet_cube d)
 theorem dyadicBaseCell_rectangle (d : ℕ) : dyadicRectangle (dyadicBaseCell d) = cube d := by
  ext x
  simp [dyadicRectangle, dyadicBaseCell, axisDepth, cube]
 theorem baseBasisFunction_bound (d k : ℕ) (i : Fin (baseDimension d k)) (x : Covariate d) :
    |baseBasisFunction d k i x| ≤ baseBasisBound d k := by
  by_cases hx : x ∈ cube d
  · unfold baseBasisFunction
    rw [indicator_of_mem hx]
    exact (Classical.choose_spec (dyadicParentBasisFunction_uniform_bound d k)).2 0 (dyadicBaseCell d)
      i x (by rwa [dyadicBaseCell_rectangle])
  · simp only [baseBasisFunction, indicator_of_notMem hx, abs_zero]
    exact zero_le_one.trans (baseBasisBound_ge_one d k)
 theorem baseBasisFunction_ae (d k : ℕ) (i : Fin (baseDimension d k)) :
    baseBasisFunction d k i =ᵐ[cubeVolume d] dyadicParentBasisFunction k (dyadicBaseCell d) i := by
  filter_upwards [ae_restrict_mem (measurableSet_cube d)] with x hx
  exact indicator_of_mem hx _
 theorem baseBasisFunction_orthogonality {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ∀ i l, (∫ x, baseBasisFunction d k i x * baseBasisFunction d k l x ∂cubeVolume d) =
      if i = l then 1 else 0 := by
  have hcube : ∀ᵐ x ∂rectangleVolume (dyadicOrigin (dyadicBaseCell d)) (dyadicSides (dyadicBaseCell d)),
      x ∈ cube d := by
    rw [dyadicBaseCell_measure hd]
    exact ae_restrict_mem (measurableSet_cube d)
  have hr (i : Fin (baseDimension d k)) : dyadicParentBasis k (dyadicBaseCell d) i =ᵐ[
      rectangleVolume (dyadicOrigin (dyadicBaseCell d)) (dyadicSides (dyadicBaseCell d))]
      baseBasisFunction d k i := by
    filter_upwards [dyadicParentBasis_ae_function k (dyadicBaseCell d) i, hcube] with x hp hx
    rw [hp, baseBasisFunction, indicator_of_mem hx]
  have ho := orthogonality_integrals_of_orthonormal _ _ _ hr (dyadicParentBasis_orthonormal k (dyadicBaseCell d))
  rw [dyadicBaseCell_measure hd] at ho
  exact ho

 def baseDesignStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) :
    Observation A Z → EuclideanSpace ℝ (Fin (designMomentDimension (baseDimension A.d k))) :=
  designFinStatistic A F (baseBasisFunction A.d k) (cube A.d) 1
 def baseDesignMean (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (k : ℕ) :
    Fin (designMomentDimension (baseDimension A.d k)) → ℝ :=
  fun i => (∫ o, baseDesignStatistic A F k o ∂(P : Measure (Observation A Z))) i
 def baseDesignConstant (A : Parameters) (k : ℕ) : ℝ := max 1
  (Real.sqrt (Fintype.card (DesignMomentIndex (baseDimension A.d k))) * (A.M0 * baseBasisBound A.d k ^ 2))
 theorem baseDesignConstant_ge_one (A : Parameters) (k : ℕ) : 1 ≤ baseDesignConstant A k := le_max_left _ _
 theorem baseDesignStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) : Measurable (baseDesignStatistic A F k) :=
  designFinStatistic_measurable A F _ (baseBasisFunction_measurable _ _) _ (measurableSet_cube _) _
 theorem baseDesignStatistic_norm_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) (o : Observation A Z) :
    ‖baseDesignStatistic A F k o‖ ≤ baseDesignConstant A k * (cube A.d).indicator (fun _ => (1 : ℝ)) o.1 := by
  rw [baseDesignStatistic, designFinStatistic_norm]
  have h := designStatistic_norm_bound A F _ _ (baseBasisBound_ge_one A.d k)
    (baseBasisFunction_bound _ _) (cube A.d) 1 zero_le_one o
  simp only [mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (indicator_nonneg (fun _ _ => zero_le_one) _))

 theorem baseDesignMean_eq_population (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (k : ℕ) :
    baseDesignMean A F P k = packedDesignPopulation A (cubeVolume A.d)
      W.designDensity W.a W.b (baseBasisFunction A.d k) := by
  have h := designFinStatistic_integral A F P W (baseBasisFunction A.d k)
    (baseBasisFunction_measurable _ _) _ (baseBasisBound_ge_one _ _) (baseBasisFunction_bound _ _)
    (cube A.d) (measurableSet_cube A.d) 1 zero_le_one
  have hm : ENNReal.ofReal (1 : ℝ) • (cubeVolume A.d).restrict (cube A.d) = cubeVolume A.d := by
    simp only [ENNReal.ofReal_one, one_smul, cubeVolume]
    rw [Measure.restrict_restrict (measurableSet_cube A.d), inter_self]
  rw [hm] at h
  funext i
  exact congrArg (fun x : EuclideanSpace ℝ (Fin (designMomentDimension (baseDimension A.d k))) => x i) h

 theorem baseDesignMean_mem (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (k : ℕ) :
    baseDesignMean A F P k ∈ designMomentSet (baseDimension A.d k) A.gminus A.gplus (A.H * A.gplus) := by
  rw [baseDesignMean_eq_population A F P W]
  change spectrum ℝ (designMatrix _) ⊆ Icc A.gminus A.gplus ∧
    ‖RoughRegime.ProjectionFrame.euclidean (designFirst _)‖ ≤ A.H * A.gplus ∧
    ‖RoughRegime.ProjectionFrame.euclidean (designSecond _)‖ ≤ A.H * A.gplus
  rw [packedDesignPopulation_gram, packedDesignPopulation_first, packedDesignPopulation_second]
  refine ⟨designGram_spectrum_subset _ _ W.designDensity_measurable _ _ A.hgminus.le
    W.densityBounds _ (baseBasisFunction_measurable _ _) _
    (zero_le_one.trans (baseBasisBound_ge_one _ _)) (baseBasisFunction_bound _ _)
    (baseBasisFunction_orthogonality (lt_of_lt_of_le Nat.zero_lt_one A.hd) k), ?_⟩
  have hgB : ∀ᵐ x ∂cubeVolume A.d, |W.designDensity x| ≤ A.gplus := W.densityBounds.mono
    (fun x hx => by
      change |W.w x * W.p x| ≤ _
      rw [abs_of_nonneg (A.hgminus.le.trans hx.1)]; exact hx.2)
  constructor
  · rw [mul_comm A.H A.gplus]
    exact designMoment_norm_le _ W.designDensity W.a W.designDensity_measurable W.measurableA
      A.gplus A.H (A.hgminus.trans A.hgplus).le A.hH.le hgB
      ((ae_restrict_mem (measurableSet_cube A.d)).mono
        (fun x hx => holderNorm_bounds_values W.a A.α A.H A.hH.le W.smoothA x hx))
      _ (baseBasisFunction_measurable _ _) _ (baseBasisFunction_bound _ _)
      (baseBasisFunction_orthogonality (lt_of_lt_of_le Nat.zero_lt_one A.hd) k)
  · rw [mul_comm A.H A.gplus]
    exact designMoment_norm_le _ W.designDensity W.b W.designDensity_measurable W.measurableB
      A.gplus A.H (A.hgminus.trans A.hgplus).le A.hH.le hgB
      ((ae_restrict_mem (measurableSet_cube A.d)).mono
        (fun x hx => holderNorm_bounds_values W.b A.β A.H A.hH.le W.smoothB x hx))
      _ (baseBasisFunction_measurable _ _) _ (baseBasisFunction_bound _ _)
      (baseBasisFunction_orthogonality (lt_of_lt_of_le Nat.zero_lt_one A.hd) k)

 theorem baseDesignStatistic_integrable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (k : ℕ) :
    Integrable (baseDesignStatistic A F k) (P : Measure (Observation A Z)) := by
  apply Integrable.of_bound (baseDesignStatistic_measurable A F k).aestronglyMeasurable (baseDesignConstant A k)
  apply Filter.Eventually.of_forall
  intro o
  have h := baseDesignStatistic_norm_bound A F k o
  by_cases ho : o.1 ∈ cube A.d
  · simpa only [indicator_of_mem ho, mul_one] using h
  · simp only [indicator_of_notMem ho, mul_zero] at h
    exact h.trans (zero_le_one.trans (baseDesignConstant_ge_one A k))

 theorem baseDesignStatistic_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (k : ℕ) :
    (∫ o, baseDesignStatistic A F k o ∂(P : Measure (Observation A Z))) =
      WithLp.toLp 2 (baseDesignMean A F P k) := by
  ext i
  rfl

 theorem baseDesignMean_gram (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (k : ℕ) :
    designMatrix (baseDesignMean A F P k) = Matrix.gram ℝ (W.weightedParentBasis k (dyadicBaseCell A.d)) := by
  rw [baseDesignMean_eq_population A F P W, packedDesignPopulation_gram]
  ext i l
  rw [W.parentGram_integral, dyadicBaseCell_measure (lt_of_lt_of_le Nat.zero_lt_one A.hd)]
  apply integral_congr_ae
  filter_upwards [baseBasisFunction_ae A.d k i, baseBasisFunction_ae A.d k l] with x hi hl
  rw [hi, hl]
  ring

 theorem baseDesignMoment_eq (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
    (k : ℕ) (f : Covariate A.d → ℝ) (hf : MemLp f 2 (W.cellDesignMeasure (dyadicBaseCell A.d))) :
    designMoment (cubeVolume A.d) W.designDensity (baseBasisFunction A.d k) f =
      HilbertGram.moments (W.weightedParentBasis k (dyadicBaseCell A.d)) (hf.toLp f) := by
  funext i
  rw [W.parentMoments_integral, dyadicBaseCell_measure (lt_of_lt_of_le Nat.zero_lt_one A.hd)]
  apply integral_congr_ae
  filter_upwards [baseBasisFunction_ae A.d k i] with x hi
  rw [hi]
  ring

 theorem baseDesignMean_first (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (k : ℕ) :
    designFirst (baseDesignMean A F P k) =
      HilbertGram.moments (W.weightedParentBasis k (dyadicBaseCell A.d)) (W.cellALp (dyadicBaseCell A.d)) := by
  rw [baseDesignMean_eq_population A F P W, packedDesignPopulation_first]
  exact baseDesignMoment_eq A F P W k W.a _

 theorem baseDesignMean_second (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (k : ℕ) :
    designSecond (baseDesignMean A F P k) =
      HilbertGram.moments (W.weightedParentBasis k (dyadicBaseCell A.d)) (W.cellBLp (dyadicBaseCell A.d)) := by
  rw [baseDesignMean_eq_population A F P W, packedDesignPopulation_second]
  exact baseDesignMoment_eq A F P W k W.b _

 theorem ModelWitness.base_response_norm (W : ModelWitness A F P)
    (f : Covariate A.d → ℝ) (hf : Measurable f) (t : ℝ) (hh : f ∈ holderBall t A.H) :
    ‖(W.holder_memLp_cell (dyadicBaseCell A.d) f hf t hh).toLp f‖ ≤ Real.sqrt A.gplus * A.H := by
  let c := dyadicBaseCell A.d
  haveI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  haveI := W.cellDesignMeasure_finite c
  apply weightedLp_norm_le_of_ae_bound _ W.designDensity A.gplus (A.hgminus.trans A.hgplus).le
    ((W.dyadic_density_bounds c).mono (fun _ hx => hx.2)) A.H A.hH.le
  filter_upwards [(W.holder_memLp_cell c f hf t hh).coeFn_toLp, W.cellDesign_ae_rectangle c] with x he hx
  rw [he]
  exact holderNorm_bounds_values f t A.H A.hH.le hh x (dyadicRectangle_subset_cube c hx)

 theorem ModelWitness.base_response_norms (W : ModelWitness A F P) :
    ‖W.cellALp (dyadicBaseCell A.d)‖ ≤ Real.sqrt A.gplus * A.H ∧
      ‖W.cellBLp (dyadicBaseCell A.d)‖ ≤ Real.sqrt A.gplus * A.H :=
  ⟨W.base_response_norm W.a W.measurableA A.α W.smoothA,
    W.base_response_norm W.b W.measurableB A.β W.smoothB⟩

 theorem ModelWitness.base_level_projection (W : ModelWitness A F P) (k : ℕ) :
    W.levelProjectionTarget k 0 = W.cellProjectionTarget k (dyadicBaseCell A.d) := by
  unfold levelProjectionTarget
  rw [Finset.sum_eq_single (dyadicBaseCell A.d)]
  · simp
  · intro c _ hc
    exact False.elim (hc (dyadicBaseCell_unique c))
  · simp

 theorem base_projection_energy (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (k : ℕ) :
    W.levelProjectionTarget k 0 =
      designFirst (baseDesignMean A F P k) ⬝ᵥ (designMatrix (baseDesignMean A F P k))⁻¹.mulVec
        (designSecond (baseDesignMean A F P k)) := by
  rw [W.base_level_projection, W.cellProjectionTarget_energy,
    baseDesignMean_gram A F P W, baseDesignMean_first A F P W, baseDesignMean_second A F P W]

end RoughRegime.Model
