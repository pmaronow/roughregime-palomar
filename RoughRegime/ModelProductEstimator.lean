module

public import RoughRegime.ModelLocalEstimator
public import RoughRegime.ModelBaseEstimator
public import RoughRegime.UpperSubcriticalTuning


@[expose] public section
/-! The literal finite dyadic polynomial estimator on the shared iid sample.
Its population and variance bounds are derived from the concrete model. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
open RoughRegime.UpperDegreeRules RoughRegime.UpperTuning RoughRegime.LiftVariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def levelEstimator (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (J : ℕ)
    (m : Fin (J + 1) → ℕ) (n : ℕ) (j : Fin (J + 1)) : (Fin n → Observation A Z) → ℝ :=
  Fin.cases (baseLevelEstimator A F (m 0) n)
    (fun i => localLevelEstimator A hαβ F i.val (m i.succ) n) j

 def productEstimator (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (J : ℕ)
    (m : Fin (J + 1) → ℕ) (n : ℕ) (xs : Fin n → Observation A Z) : ℝ :=
  ∑ j, levelEstimator A hαβ F J m n j xs

 def populationLevel {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) (J : ℕ) (j : Fin (J + 1)) : ℝ :=
  Fin.cases (W.levelProjectionTarget (holderOrder A.β) 0)
    (fun i => W.levelProjectionIncrement i.val) j

 theorem levelEstimator_measurable (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (J : ℕ)
    (m : Fin (J + 1) → ℕ) (n : ℕ) (j : Fin (J + 1)) :
    Measurable (levelEstimator A hαβ F J m n j) := by
  refine Fin.cases ?_ ?_ j
  · exact baseLevelEstimator_measurable A F (m 0) n
  · intro i
    exact localLevelEstimator_measurable A hαβ F i.val (m i.succ) n

 theorem productEstimator_measurable (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (J : ℕ)
    (m : Fin (J + 1) → ℕ) (n : ℕ) : Measurable (productEstimator A hαβ F J m n) :=
  Finset.measurable_sum _ (fun j _ => levelEstimator_measurable A hαβ F J m n j)

 theorem levelEstimator_memLp (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (P : ProbabilityMeasure (Observation A Z)) (J : ℕ) (m : Fin (J + 1) → ℕ) (n : ℕ)
    (j : Fin (J + 1)) : MemLp (levelEstimator A hαβ F J m n j) 2
      (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) := by
  refine Fin.cases ?_ ?_ j
  · exact baseLevelEstimator_memLp A F P (m 0) n
  · intro i
    exact localLevelEstimator_memLp A hαβ F P i.val (m i.succ) n

 theorem productEstimator_memLp (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (P : ProbabilityMeasure (Observation A Z)) (J : ℕ) (m : Fin (J + 1) → ℕ) (n : ℕ) :
    MemLp (productEstimator A hαβ F J m n) 2
      (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) :=
  memLp_finsetSum _ (fun j _ => levelEstimator_memLp A hαβ F P J m n j)

 theorem populationLevel_sum {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) (J : ℕ) :
    ∑ j, populationLevel W J j = W.levelProjectionTarget (holderOrder A.β) J := by
  rw [W.projection_telescope J,Fin.sum_univ_succ]
  change W.levelProjectionTarget (holderOrder A.β) 0 +
      (∑ j : Fin J, W.levelProjectionIncrement j.val) = _
  rw [Fin.sum_univ_eq_sum_range]

 theorem varianceTerm_mono_constant (Cv D K n : ℝ) (r : ℕ)
    (hCv : 0 ≤ Cv) (hCD : Cv ≤ D) (hK : 0 ≤ K) (hn : 0 ≤ n) :
    varianceTerm Cv K n r ≤ varianceTerm D K n r := by
  unfold varianceTerm
  apply div_le_div_of_nonneg_right _ hn
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (div_nonneg hK hn) _)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCv hCD _) (Nat.cast_nonneg _)

 theorem varianceConstant_ge_one (C : ℝ) (hC : 1 ≤ C) : 1 ≤ varianceConstant C :=
  (one_le_pow₀ hC (n := 4)).trans (first_order_constant_le_varianceConstant C hC)

 theorem variance_display_mono_constant (v Cv D K n q : ℝ) (R : ℕ)
    (hCv : 0 ≤ Cv) (hCD : Cv ≤ D) (hK : 0 ≤ K) (hn : 0 ≤ n)
    (hv : v ≤ Cv * K ^ (-2 * q) / n +
      ∑ k ∈ Finset.range (R - 1), varianceTerm Cv K n (k + 2)) :
    v ≤ D * K ^ (-2 * q) / n +
      ∑ k ∈ Finset.range (R - 1), varianceTerm D K n (k + 2) := by
  apply hv.trans
  apply add_le_add
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hK _)) hn
  · exact Finset.sum_le_sum (fun k _ => varianceTerm_mono_constant Cv D K n (k + 2) hCv hCD hK hn)

/-- Full finite-level model estimator risk assembly, with all constants
chosen before the response type, observable functions and model. The input
degree condition is the explicit sample-admissibility condition used by both
derived numerical tuning rules. -/
 theorem uniform_productEstimator_risk (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ Cb Cv Cproj : ℝ, 1 ≤ Cb ∧ 1 ≤ Cv ∧ 0 < Cproj ∧
      ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
        (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
        (J : ℕ) (m : Fin (J + 1) → ℕ) (n : ℕ),
        (∀ j, 2 * (m j + A.nu + 2) ≤ n) →
        lpNorm (fun xs => productEstimator A hαβ F J m n xs - W.productTarget) 2
            (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
          Cproj * ((2 : ℝ) ^ J) ^ (-A.theta) +
            Cb * (∑ j, approximationWeight (parentCells J j) A.theta
              (RoughRegime.Rates.tau A.gminus A.gplus) A.nu (m j)) +
            ∑ j, Real.sqrt (variance (levelEstimator A hαβ F J m n j)
              (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z))))) ∧
        (∀ j, variance (levelEstimator A hαβ F J m n j)
            (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
          Cv * (parentCells J j : ℝ) ^ (-2 * (min (min A.α A.β) 1 / A.d)) / n +
            ∑ k ∈ Finset.range (m j + A.nu + 2 - 1),
              varianceTerm Cv (parentCells J j) n (k + 2)) := by
  obtain ⟨Cb0,hCb0,hbias0⟩ := uniform_baseLevelEstimator_bias.{u} A
  obtain ⟨Cb1,hCb1,hbias1⟩ := uniform_localLevelEstimator_bias.{u} A hαβ
  obtain ⟨C0,hC0,hvar0⟩ := uniform_baseLevelEstimator_variance.{u} A
  obtain ⟨C1,hC1,hvar1⟩ := uniform_localLevelEstimator_variance.{u} A hαβ
  obtain ⟨Cproj,hCproj,hproj⟩ := uniform_projection_telescope_resolution_bias.{u} A hαβ
  let Cb := max Cb0 Cb1
  let Cv := max (varianceConstant C0) (varianceConstant C1)
  have hCb : 1 ≤ Cb := hCb0.trans (le_max_left _ _)
  have hCv : 1 ≤ Cv := (varianceConstant_ge_one C0 hC0).trans (le_max_left _ _)
  refine ⟨Cb,Cv,Cproj,hCb,hCv,hCproj,?_⟩
  intro Z _ F P W J m n hdegree
  let μ := Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))
  have hn : 0 < n := by have := hdegree 0; omega
  have hnr : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hL (j : Fin (J + 1)) : MemLp (levelEstimator A hαβ F J m n j) 2 μ :=
    levelEstimator_memLp A hαβ F P J m n j
  have he (j : Fin (J + 1)) :
      |(∫ xs, levelEstimator A hαβ F J m n j xs ∂μ) - populationLevel W J j| ≤
        Cb * approximationWeight (parentCells J j) A.theta
          (RoughRegime.Rates.tau A.gminus A.gplus) A.nu (m j) := by
    refine Fin.cases ?_ ?_ j
    · have ht := hbias0 Z F P W (m 0) n (by have := hdegree 0; omega)
      change |(∫ xs, baseLevelEstimator A F (m 0) n xs ∂μ) - W.levelProjectionTarget (holderOrder A.β) 0| ≤ _
      simp only [parentCells, Fin.val_zero, ite_true, Nat.cast_one]
      exact ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by unfold approximationWeight; positivity))
    · intro i
      have ht := hbias1 Z F P W i.val (m i.succ) n (by have := hdegree i.succ; omega)
      have hcp : (parentCells J i.succ : ℝ) = (2 : ℝ) ^ i.val := by
        simp [parentCells,Fin.val_succ]
      change |(∫ xs, localLevelEstimator A hαβ F i.val (m i.succ) n xs ∂μ) - W.levelProjectionIncrement i.val| ≤ _
      rw [hcp]
      exact ht.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by unfold approximationWeight; positivity))
  have hb : |(∫ xs, productEstimator A hαβ F J m n xs ∂μ) - W.productTarget| ≤
      Cproj * ((2 : ℝ) ^ J) ^ (-A.theta) +
        Cb * (∑ j, approximationWeight (parentCells J j) A.theta
          (RoughRegime.Rates.tau A.gminus A.gplus) A.nu (m j)) := by
    change |(∫ xs, ∑ j, levelEstimator A hαβ F J m n j xs ∂μ) - W.productTarget| ≤ _
    rw [integral_finsetSum Finset.univ (fun j _ => (hL j).integrable (by norm_num))]
    rw [Finset.mul_sum]
    apply approximation_sum_bias _ (populationLevel W J)
      (fun j => Cb * approximationWeight (parentCells J j) A.theta
        (RoughRegime.Rates.tau A.gminus A.gplus) A.nu (m j)) W.productTarget
      (Cproj * ((2 : ℝ) ^ J) ^ (-A.theta)) he
    rw [populationLevel_sum,abs_sub_comm]
    have ht := hproj Z F P W J
    rw [← W.projection_telescope J] at ht
    exact ht
  refine ⟨(root_mean_square_le_bias_add_sd μ _
    (productEstimator_memLp A hαβ F P J m n) W.productTarget).trans
      (add_le_add hb (sqrt_variance_sum_le μ _ hL)),?_⟩
  intro j
  refine Fin.cases ?_ ?_ j
  · change variance (baseLevelEstimator A F (m 0) n) μ ≤ _
    simp only [parentCells, Fin.val_zero, ite_true, Nat.cast_one]
    have ht := hvar0 Z F P W (m 0) n (hdegree 0)
    have ht' : variance (baseLevelEstimator A F (m 0) n) μ ≤
        varianceConstant C0 * (1 : ℝ) ^ (-2 * (min (min A.α A.β) 1 / A.d)) / n +
          ∑ k ∈ Finset.range (m 0 + A.nu + 2 - 1), varianceTerm (varianceConstant C0) 1 n (k + 2) := by
      simpa only [Real.one_rpow,mul_one] using ht
    exact variance_display_mono_constant _ _ Cv 1 n _ _
      (zero_le_one.trans (varianceConstant_ge_one C0 hC0)) (le_max_left _ _)
      (by norm_num) hnr ht'
  · intro i
    have ht := hvar1 Z F P W i.val (m i.succ) n (hdegree i.succ)
    have hcp : (parentCells J i.succ : ℝ) = (2 : ℝ) ^ i.val := by simp [parentCells,Fin.val_succ]
    change variance (localLevelEstimator A hαβ F i.val (m i.succ) n) μ ≤ _
    rw [hcp]
    exact variance_display_mono_constant _ _ Cv ((2 : ℝ) ^ i.val) n _ _
      (zero_le_one.trans (varianceConstant_ge_one C1 hC1)) (le_max_right _ _)
      (by positivity) hnr ht

end RoughRegime.Model
