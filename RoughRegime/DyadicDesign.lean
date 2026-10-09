module

public import RoughRegime.DesignStatistics
public import RoughRegime.DyadicFiniteBasis


@[expose] public section
/-! Actual finite dyadic cell design, known observables, and uniform source bounds. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory Matrix
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

 def dyadicFinChildBasisFunction {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j)
    (i : Fin (dyadicChildDimension d k)) : Covariate d → ℝ :=
  dyadicChildBasisFunction hd k c ((Fintype.equivFin (SplitIndex d k)).symm i)

 theorem dyadicFinChildBasisFunction_measurable {d j : ℕ} (hd : 0 < d) (k : ℕ)
    (c : DyadicCell d j) (i : Fin (dyadicChildDimension d k)) :
    Measurable (dyadicFinChildBasisFunction hd k c i) := dyadicChildBasisFunction_measurable _ _ _ _

 theorem dyadicFinChildBasisFunction_ae {d j : ℕ} (hd : 0 < d) (k : ℕ)
    (c : DyadicCell d j) (i : Fin (dyadicChildDimension d k)) :
    dyadicFinChildBasis hd k c i =ᵐ[rectangleVolume (dyadicOrigin c) (dyadicSides c)]
      dyadicFinChildBasisFunction hd k c i := dyadicChildBasis_ae _ _ _ _

 theorem dyadicFinChildBasisFunction_orthogonality {d j : ℕ} (hd : 0 < d) (k : ℕ)
    (c : DyadicCell d j) :
    ∀ i l, (∫ x, dyadicFinChildBasisFunction hd k c i x *
      dyadicFinChildBasisFunction hd k c l x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c)) =
        if i = l then 1 else 0 :=
  orthogonality_integrals_of_orthonormal _ _ _ (dyadicFinChildBasisFunction_ae hd k c)
    (dyadicFinChildBasis_orthonormal hd k c)

 def dyadicDesignBasisBound (d k : ℕ) : ℝ :=
  Classical.choose (dyadicChildBasisFunction_uniform_bound d k)

 theorem dyadicDesignBasisBound_ge_one (d k : ℕ) : 1 ≤ dyadicDesignBasisBound d k :=
  (Classical.choose_spec (dyadicChildBasisFunction_uniform_bound d k)).1

 theorem dyadicFinChildBasisFunction_bound {d j : ℕ} (hd : 0 < d) (k : ℕ)
    (c : DyadicCell d j) (i : Fin (dyadicChildDimension d k)) (x : Covariate d) :
    |dyadicFinChildBasisFunction hd k c i x| ≤ dyadicDesignBasisBound d k :=
  (Classical.choose_spec (dyadicChildBasisFunction_uniform_bound d k)).2 hd j c _ x

 theorem dyadicCellMeasure_ac {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    rectangleVolume (dyadicOrigin c) (dyadicSides c) ≪ cubeVolume d := by
  rw [dyadicRectangle_normalizedVolume hd c]
  exact Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict

 def dyadicDesignStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    Observation A Z → EuclideanSpace ℝ (DesignMomentIndex (dyadicChildDimension A.d k)) :=
  designStatistic A F (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c)
    (dyadicPartitionCell c) ((2 : ℝ) ^ j)

 def dyadicDesignConstant (A : Parameters) (k : ℕ) : ℝ := max 1
  (max (Real.sqrt (Fintype.card (DesignMomentIndex (dyadicChildDimension A.d k))) *
    (A.M0 * dyadicDesignBasisBound A.d k ^ 2)) (A.gplus / A.δ))

 theorem dyadicDesignConstant_ge_one (A : Parameters) (k : ℕ) : 1 ≤ dyadicDesignConstant A k := le_max_left _ _

 theorem dyadicDesignStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    Measurable (dyadicDesignStatistic A F k c) :=
  designStatistic_measurable A F _ (dyadicFinChildBasisFunction_measurable _ _ _)
    _ (dyadicPartitionCell_measurable c) _

 theorem dyadicDesignStatistic_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    (∫ o, dyadicDesignStatistic A F k c o ∂(P : Measure (Observation A Z))) =
      designPopulation A (rectangleVolume (dyadicOrigin c) (dyadicSides c))
        (fun x => h.w x * h.p x) h.a h.b
          (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c) := by
  rw [dyadicRectangle_normalizedVolume (lt_of_lt_of_le Nat.zero_lt_one A.hd) c]
  exact designStatistic_integral A F P h _ (dyadicFinChildBasisFunction_measurable _ _ _)
    _ (dyadicDesignBasisBound_ge_one _ _) (dyadicFinChildBasisFunction_bound _ _ _)
    _ (dyadicPartitionCell_measurable c) _ (by positivity)

 theorem dyadicDesignStatistic_norm_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) (o : Observation A Z) :
    ‖dyadicDesignStatistic A F k c o‖ ≤ dyadicDesignConstant A k * (2 : ℝ) ^ j *
      (dyadicPartitionCell c).indicator (fun _ => (1 : ℝ)) o.1 := by
  have hb := designStatistic_norm_bound A F
    (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c)
    (dyadicDesignBasisBound A.d k) (dyadicDesignBasisBound_ge_one A.d k)
    (dyadicFinChildBasisFunction_bound (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c) (dyadicPartitionCell c) ((2 : ℝ) ^ j) (by positivity) o
  apply hb.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · positivity
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

 theorem dyadicDesign_cell_probability (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    (P : Measure (Observation A Z)).real (Prod.fst ⁻¹' dyadicPartitionCell c) ≤
      dyadicDesignConstant A k / (2 : ℝ) ^ j := by
  have hh := design_cell_probability A F P h _ (dyadicPartitionCell_measurable c)
  have hc : (cubeVolume A.d).real (dyadicPartitionCell c) = 1 / (2 : ℝ) ^ j := by
    rw [Measure.real, dyadicPartitionCell_cubeVolume (lt_of_lt_of_le Nat.zero_lt_one A.hd) c,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hc, ← div_eq_mul_one_div] at hh
  exact hh.trans (div_le_div_of_nonneg_right
    ((le_max_right _ _).trans (le_max_right _ _)) (by positivity))

 theorem dyadicDesign_density_bounds (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    {j : ℕ} (c : DyadicCell A.d j) :
    ∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c),
      A.gminus ≤ h.w x * h.p x ∧ h.w x * h.p x ≤ A.gplus :=
  (dyadicCellMeasure_ac (lt_of_lt_of_le Nat.zero_lt_one A.hd) c).ae_le h.densityBounds

 theorem dyadicDesign_spectrum (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    spectrum ℝ (designGram (rectangleVolume (dyadicOrigin c) (dyadicSides c))
      (fun x => h.w x * h.p x)
      (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c)) ⊆
        Set.Icc A.gminus A.gplus := by
  letI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  exact designGram_spectrum_subset _ _ (h.measurableW.mul h.measurableP) _ _ A.hgminus.le
    (dyadicDesign_density_bounds A F P h c) _ (dyadicFinChildBasisFunction_measurable _ _ _)
    _ (le_trans zero_le_one (dyadicDesignBasisBound_ge_one _ _)) (dyadicFinChildBasisFunction_bound _ _ _)
    (dyadicFinChildBasisFunction_orthogonality _ _ _)

 theorem dyadicDesign_moment_norms (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    ‖WithLp.toLp 2 (designMoment (rectangleVolume (dyadicOrigin c) (dyadicSides c))
      (fun x => h.w x * h.p x)
      (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c) h.a)‖ ≤ A.H * A.gplus ∧
    ‖WithLp.toLp 2 (designMoment (rectangleVolume (dyadicOrigin c) (dyadicSides c))
      (fun x => h.w x * h.p x)
      (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c) h.b)‖ ≤ A.H * A.gplus := by
  letI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  have hgB : ∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c), |h.w x * h.p x| ≤ A.gplus :=
    (dyadicDesign_density_bounds A F P h c).mono (fun x hx => by
    rw [abs_of_nonneg (A.hgminus.le.trans hx.1)]; exact hx.2)
  have hcube : ∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c), x ∈ cube A.d :=
    (dyadicCellMeasure_ac (lt_of_lt_of_le Nat.zero_lt_one A.hd) c).ae_le
      (ae_restrict_mem (measurableSet_cube A.d))
  constructor
  · rw [mul_comm A.H A.gplus]
    exact designMoment_norm_le _ (fun x => h.w x * h.p x) h.a
      (h.measurableW.mul h.measurableP) h.measurableA A.gplus A.H
      (A.hgminus.trans A.hgplus).le A.hH.le hgB
      (hcube.mono (fun x hx => holderNorm_bounds_values h.a A.α A.H A.hH.le h.smoothA x hx))
      _ (dyadicFinChildBasisFunction_measurable _ _ _) _ (dyadicFinChildBasisFunction_bound _ _ _)
      (dyadicFinChildBasisFunction_orthogonality _ _ _)
  · rw [mul_comm A.H A.gplus]
    exact designMoment_norm_le _ (fun x => h.w x * h.p x) h.b
      (h.measurableW.mul h.measurableP) h.measurableB A.gplus A.H
      (A.hgminus.trans A.hgplus).le A.hH.le hgB
      (hcube.mono (fun x hx => holderNorm_bounds_values h.b A.β A.H A.hH.le h.smoothB x hx))
      _ (dyadicFinChildBasisFunction_measurable _ _ _) _ (dyadicFinChildBasisFunction_bound _ _ _)
      (dyadicFinChildBasisFunction_orthogonality _ _ _)

end RoughRegime.Model
