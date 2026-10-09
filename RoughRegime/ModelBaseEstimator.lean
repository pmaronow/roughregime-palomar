module

public import RoughRegime.ModelBaseLemma
public import RoughRegime.ModelLocalEstimator


@[expose] public section
/-! The explicit nonsplit base estimator in the genuine iid experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
open RoughRegime.PolynomialCells RoughRegime.IIDPolynomialEstimator
open RoughRegime.Upper RoughRegime.UpperDegreeRules RoughRegime.LiftVariance
open RoughRegime.ComplexDerivativeBridge RoughRegime.ProjectionIncrementComplex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev baseMomentDimension (A : Parameters) := designMomentDimension (baseDimension A.d (holderOrder A.β))

 def basePackedStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (o : Observation A Z) : Fin (1 * baseMomentDimension A) → ℝ :=
  fun i => baseDesignStatistic A F (holderOrder A.β) o (finProdFinEquiv.symm i).2
 def basePackedMean (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) : Fin (1 * baseMomentDimension A) → ℝ :=
  fun i => baseDesignMean A F P (holderOrder A.β) (finProdFinEquiv.symm i).2
 def basePackedSelector (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (_o : Observation A Z) : Fin 1 := 0

 theorem basePackedStatistic_projection (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (c : Fin 1) (o : Observation A Z) :
    cellProjection c (basePackedStatistic A F o) = WithLp.ofLp (baseDesignStatistic A F (holderOrder A.β) o) := by
  funext i
  simp only [cellProjection_apply, basePackedStatistic, Equiv.symm_apply_apply]
 theorem basePackedMean_projection (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (c : Fin 1) :
    cellProjection c (basePackedMean A F P) = baseDesignMean A F P (holderOrder A.β) := by
  funext i
  simp only [cellProjection_apply, basePackedMean, Equiv.symm_apply_apply]
 theorem basePackedStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) : Measurable (basePackedStatistic A F) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (PiLp.proj (p := 2) (β := fun _ : Fin (baseMomentDimension A) => ℝ) (𝕜 := ℝ)
    (finProdFinEquiv.symm i).2).continuous.measurable.comp (baseDesignStatistic_measurable A F _)
 theorem basePackedStatistic_coordinate_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (i : Fin (1 * baseMomentDimension A)) :
    (∫ o, basePackedStatistic A F o i ∂(P : Measure (Observation A Z))) = basePackedMean A F P i := by
  exact (PiLp.proj (p := 2) (β := fun _ : Fin (baseMomentDimension A) => ℝ) (𝕜 := ℝ)
    (finProdFinEquiv.symm i).2).integral_comp_comm (baseDesignStatistic_integrable A F P _)
 theorem basePackedStatistic_coordinate_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (o : Observation A Z) (i : Fin (1 * baseMomentDimension A)) :
    |basePackedStatistic A F o i| ≤ baseDesignConstant A (holderOrder A.β) := by
  have hb := PiLp.norm_apply_le (baseDesignStatistic A F (holderOrder A.β) o) (finProdFinEquiv.symm i).2
  have hi : (cube A.d).indicator (fun _ => (1 : ℝ)) o.1 ≤ 1 := by
    by_cases hx : o.1 ∈ cube A.d <;> simp [hx]
  exact hb.trans ((baseDesignStatistic_norm_bound A F _ o).trans
    (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hi
      (zero_le_one.trans (baseDesignConstant_ge_one A _)))))

 def baseLevelPolynomial (A : Parameters) (m : ℕ) : MvPolynomial (Fin (1 * baseMomentDimension A)) ℝ :=
  cellMomentPolynomial (fun _ : Fin 1 => baseIncrementPolynomial A m)
 def baseLevelEstimator (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (m n : ℕ) (xs : Fin n → Observation A Z) : ℝ :=
  sampleLift (baseLevelPolynomial A m) (basePackedStatistic A F) xs

 theorem baseLevelPolynomial_degree (A : Parameters) (m : ℕ) :
    (baseLevelPolynomial A m).totalDegree ≤ m + 2 :=
  cellMomentPolynomial_degree _ (fun _ => baseIncrementPolynomial_degree A m)
 theorem baseLevelEstimator_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (m n : ℕ) : Measurable (baseLevelEstimator A F m n) :=
  sampleLift_measurable _ _ (basePackedStatistic_measurable A F)
 theorem baseLevelEstimator_memLp (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (m n : ℕ) :
    MemLp (baseLevelEstimator A F m n) 2 (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) :=
  sampleLift_memLp _ _ _ (basePackedStatistic_measurable A F) (baseDesignConstant A (holderOrder A.β))
    (zero_le_one.trans (baseDesignConstant_ge_one A _)) (basePackedStatistic_coordinate_bound A F)
 theorem baseLevelEstimator_mean (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (m n : ℕ) (hn : m + 2 ≤ n) :
    (∫ xs, baseLevelEstimator A F m n xs ∂Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) =
      MvPolynomial.eval (basePackedMean A F P) (baseLevelPolynomial A m) := by
  have hm := sampleLift_mean (P : Measure (Observation A Z)) (baseLevelPolynomial A m)
    (basePackedStatistic A F) (basePackedStatistic_measurable A F)
    ((baseLevelPolynomial_degree A m).trans hn) (baseDesignConstant A (holderOrder A.β))
    (zero_le_one.trans (baseDesignConstant_ge_one A _)) (basePackedStatistic_coordinate_bound A F)
  simpa only [baseLevelEstimator, basePackedStatistic_coordinate_integral] using hm

 theorem uniform_baseLevelEstimator_bias (A : Parameters) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (m n : ℕ),
      m + A.nu + 2 ≤ n →
      |(∫ xs, baseLevelEstimator A F m n xs ∂Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) -
        W.levelProjectionTarget (holderOrder A.β) 0| ≤
      C * approximationWeight 1 A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu m := by
  obtain ⟨C, hC, hb⟩ := uniform_model_base_lemma.{u} A
  refine ⟨C, hC, ?_⟩
  intro Z _ F P W m n hn
  rw [baseLevelEstimator_mean A F P m n (by omega), baseLevelPolynomial, cellMomentPolynomial_eval]
  simp only [Nat.cast_one, inv_one, Fin.sum_univ_one, one_mul, basePackedMean_projection]
  have he := (hb Z F P W).2.2.2.2 m |>.2.1
  have hp : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ A.nu := one_le_pow₀ (by exact_mod_cast Nat.succ_pos m)
  have hρ := (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le
  calc
    _ ≤ C * intervalRho A.gminus A.gplus ^ m := by simpa only [Real.norm_eq_abs, abs_sub_comm] using he
    _ ≤ C * ((m + 1 : ℕ) : ℝ) ^ A.nu * intervalRho A.gminus A.gplus ^ m :=
      mul_le_mul_of_nonneg_right (by nlinarith [zero_le_one.trans hC]) (pow_nonneg hρ m)
    _ = _ := by rw [intervalRho_pow_eq_exp_tau]; simp only [approximationWeight, Real.one_rpow, one_mul]; ring

 theorem uniform_baseLevelEstimator_variance (A : Parameters) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (m n : ℕ),
      2 * (m + A.nu + 2) ≤ n →
      variance (baseLevelEstimator A F m n) (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
        varianceConstant C0 / n + ∑ k ∈ Finset.range (m + A.nu + 2 - 1),
          varianceTerm (varianceConstant C0) 1 n (k + 2) := by
  obtain ⟨Cp, hCp, hb⟩ := uniform_model_base_lemma.{u} A
  let Co := baseDesignConstant A (holderOrder A.β)
  let C0 := max Cp Co
  have hpC : Cp ≤ C0 := le_max_left _ _
  have hoC : Co ≤ C0 := le_max_right _ _
  have hC0 : 1 ≤ C0 := hCp.trans hpC
  have hrad : 1 / C0 ≤ 1 / Cp := one_div_le_one_div_of_le (zero_lt_one.trans_le hCp) hpC
  refine ⟨C0, hC0, ?_⟩
  intro Z _ F P W m n hn
  let q := baseIncrementPolynomial A m
  let z := basePackedStatistic A F
  have hm : (fun k => ∫ o, z o k ∂(P : Measure (Observation A Z))) = basePackedMean A F P := by
    funext k
    exact basePackedStatistic_coordinate_integral A F P k
  have hcomplex (c : Fin 1) (y : Fin (baseMomentDimension A) → ℂ)
      (hy : ‖y - (fun k => (cellProjection c (fun l => ∫ o, z o l ∂(P : Measure (Observation A Z))) k : ℂ))‖ < 1 / C0) :
      ‖MvPolynomial.eval y (complexify q)‖ ≤ C0 := by
    rw [hm, basePackedMean_projection] at hy
    exact (((hb Z F P W).2.2.2.2 m |>.2.2.1) y (hy.trans_le hrad)).trans hpC
  have hgrad (c : Fin 1) :
      ‖(WithLp.toLp 2 (fun k => fderiv ℝ (fun y => MvPolynomial.eval y q)
        (cellProjection c (fun l => ∫ o, z o l ∂(P : Measure (Observation A Z)))) (Pi.single k 1)) :
          EuclideanSpace ℝ (Fin (baseMomentDimension A)))‖ ≤ C0 * (1 : ℝ) ^ (1 : ℝ) := by
    rw [hm, basePackedMean_projection]
    change ‖polynomialGradient (baseIncrementPolynomial A m) (baseDesignMean A F P (holderOrder A.β))‖ ≤
      C0 * (1 : ℝ) ^ (1 : ℝ)
    rw [Real.one_rpow, mul_one]
    exact ((hb Z F P W).2.2.2.2 m |>.2.2.2).trans hpC
  have hz (o : Observation A Z) (c : Fin 1) :
      ‖(WithLp.toLp 2 (cellProjection c (z o)) : EuclideanSpace ℝ (Fin (baseMomentDimension A)))‖ ≤
        C0 * (1 : ℕ) * cellIndicator (basePackedSelector A) c o := by
    rw [basePackedStatistic_projection, WithLp.toLp_ofLp]
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    simp only [Nat.cast_one, mul_one, cellIndicator, basePackedSelector, ite_true]
    have hi : (cube A.d).indicator (fun _ => (1 : ℝ)) o.1 ≤ 1 := by
      by_cases hx : o.1 ∈ cube A.d <;> simp [hx]
    exact (baseDesignStatistic_norm_bound A F _ o).trans
      ((mul_le_mul_of_nonneg_left hi (zero_le_one.trans (baseDesignConstant_ge_one A _))).trans
        (by simpa only [mul_one] using hoC))
  have hprob (c : Fin 1) :
      (P : Measure (Observation A Z)).real {o | basePackedSelector A o = c} ≤ C0 / (1 : ℕ) := by
    simp only [Nat.cast_one, div_one]
    exact measureReal_le_one.trans hC0
  have hv := sampleLift_variance_cells (P : Measure (Observation A Z)) zero_lt_one
    (by omega : 0 < m + A.nu + 2) hn (fun _ : Fin 1 => q)
    (fun _ => (baseIncrementPolynomial_degree A m).trans (by omega)) z
    (basePackedStatistic_measurable A F) (basePackedSelector A) measurable_const C0 1 1
    hC0 zero_lt_one le_rfl zero_lt_one hcomplex hgrad hz hprob
  simp only [Real.one_rpow, mul_one] at hv
  have hsum : (1 / (n : ℝ)) * ∑ k ∈ Finset.range (m + A.nu + 2 - 1),
      varianceConstant C0 ^ (k + 2) * ((k + 2).factorial : ℝ) *
        ((1 : ℕ) / (n : ℝ)) ^ (k + 1) =
      ∑ k ∈ Finset.range (m + A.nu + 2 - 1), varianceTerm (varianceConstant C0) 1 n (k + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold varianceTerm
    rw [show k + 2 - 1 = k + 1 by omega]
    ring
  rw [hsum] at hv
  exact hv

end RoughRegime.Model
