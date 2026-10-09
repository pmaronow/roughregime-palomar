module

public import RoughRegime.DyadicPackedDesign
public import RoughRegime.IIDPolynomialEstimator
public import RoughRegime.ModelRateConstants
public import RoughRegime.UpperDegreeRules


@[expose] public section
/-! The explicit local-level estimator of the actual model, with all
statistical and approximation hypotheses derived from its known observable. -/
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

 def localLevelPolynomial (A : Parameters) (hαβ : A.α ≤ A.β) (j m : ℕ) :
    MvPolynomial (Fin ((2 ^ j) * localMomentDimension A)) ℝ :=
  cellMomentPolynomial (fun _ : Fin (2 ^ j) => localIncrementPolynomial A hαβ
    (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)) m)

 def localLevelEstimator (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (j m n : ℕ)
    (xs : Fin n → Observation A Z) : ℝ :=
  sampleLift (localLevelPolynomial A hαβ j m) (dyadicPackedStatistic A F j) xs

 theorem localLevelPolynomial_degree (A : Parameters) (hαβ : A.α ≤ A.β) (j m : ℕ) :
    (localLevelPolynomial A hαβ j m).totalDegree ≤ m + A.nu + 2 :=
  cellMomentPolynomial_degree _ (fun _ => localIncrementPolynomial_degree A hαβ _ m)

 theorem localLevelEstimator_measurable (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) (j m n : ℕ) :
    Measurable (localLevelEstimator A hαβ F j m n) :=
  sampleLift_measurable _ _ (dyadicPackedStatistic_measurable A F j)

 theorem localLevelEstimator_memLp (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (P : ProbabilityMeasure (Observation A Z)) (j m n : ℕ) :
    MemLp (localLevelEstimator A hαβ F j m n) 2
      (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) :=
  sampleLift_memLp _ _ _ (dyadicPackedStatistic_measurable A F j)
    (dyadicDesignConstant A (holderOrder A.β) * (2 : ℝ) ^ j)
    (mul_nonneg (zero_le_one.trans (dyadicDesignConstant_ge_one _ _)) (by positivity))
    (dyadicPackedStatistic_coordinate_bound A F j)

 theorem localLevelEstimator_mean (A : Parameters) (hαβ : A.α ≤ A.β)
    {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (P : ProbabilityMeasure (Observation A Z)) (j m n : ℕ) (hn : m + A.nu + 2 ≤ n) :
    (∫ xs, localLevelEstimator A hαβ F j m n xs
      ∂Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) =
      MvPolynomial.eval (dyadicPackedMean A F P j) (localLevelPolynomial A hαβ j m) := by
  have hm := sampleLift_mean (P : Measure (Observation A Z))
    (localLevelPolynomial A hαβ j m) (dyadicPackedStatistic A F j)
    (dyadicPackedStatistic_measurable A F j)
    ((localLevelPolynomial_degree A hαβ j m).trans hn)
    (dyadicDesignConstant A (holderOrder A.β) * (2 : ℝ) ^ j)
    (mul_nonneg (zero_le_one.trans (dyadicDesignConstant_ge_one _ _)) (by positivity))
    (dyadicPackedStatistic_coordinate_bound A F j)
  simpa only [localLevelEstimator,dyadicPackedStatistic_coordinate_integral] using hm

 theorem cell_average_error {K : ℕ} (hK : 0 < K) (a b : Fin K → ℝ) (E : ℝ)
    (hab : ∀ c, |a c - b c| ≤ E) :
    |(K : ℝ)⁻¹ * ∑ c, a c - (K : ℝ)⁻¹ * ∑ c, b c| ≤ E := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_pos (inv_pos.mpr hKr)]
  calc
    _ ≤ (K : ℝ)⁻¹ * ∑ c, |a c - b c| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hKr.le)
    _ ≤ (K : ℝ)⁻¹ * ∑ _c : Fin K, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hab c)) (inv_nonneg.mpr hKr.le)
    _ = E := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp

 theorem intervalRho_pow_eq_exp_tau (A : Parameters) (m : ℕ) :
    intervalRho A.gminus A.gplus ^ m = Real.exp (-RoughRegime.Rates.tau A.gminus A.gplus * m) := by
  have hρ := intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus
  change RoughRegime.Rates.rho A.gminus A.gplus ^ m = _
  unfold RoughRegime.Rates.tau
  have hρ' : 0 < RoughRegime.Rates.rho A.gminus A.gplus := hρ
  rw [neg_neg, mul_comm,Real.exp_nat_mul,Real.exp_log hρ']

/-- One class constant controls the actual local estimator bias, uniformly
before all response spaces, models, levels and truncation orders. -/
 theorem uniform_localLevelEstimator_bias (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j m n : ℕ), m + A.nu + 2 ≤ n →
      |(∫ xs, localLevelEstimator A hαβ F j m n xs
          ∂Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) -
        W.levelProjectionIncrement j| ≤
          C * approximationWeight ((2 : ℝ) ^ j) A.theta
            (RoughRegime.Rates.tau A.gminus A.gplus) A.nu m := by
  obtain ⟨C,hC,hlocal⟩ := uniform_model_local_lemma.{u} A hαβ
  refine ⟨C,hC,?_⟩
  intro Z _ F P W j m n hn
  rw [localLevelEstimator_mean A hαβ F P j m n hn,
    localLevelPolynomial,cellMomentPolynomial_eval]
  have ht : W.levelProjectionIncrement j = (2 ^ j : ℝ)⁻¹ *
      ∑ c : Fin (2 ^ j), W.localProjectionIncrement (dyadicCellEquiv A j c) := by
    unfold ModelWitness.levelProjectionIncrement
    rw [← (dyadicCellEquiv A j).sum_comp (fun c => (1 / (2 : ℝ) ^ j) * W.localProjectionIncrement c),
      ← Finset.mul_sum]
    simp only [one_div]
  rw [ht]
  have hb (c : Fin (2 ^ j)) :=
    (hlocal Z F P W j (dyadicCellEquiv A j c)).2.2.2.2.2.2 m |>.2.1
  have he := cell_average_error (by positivity : 0 < 2 ^ j)
    (fun c => MvPolynomial.eval (cellProjection c (dyadicPackedMean A F P j))
      (localIncrementPolynomial A hαβ (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)) m))
    (fun c => W.localProjectionIncrement (dyadicCellEquiv A j c))
    (C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ (A.α + A.β) * ((m + 1 : ℕ) : ℝ) ^ A.nu * intervalRho A.gminus A.gplus ^ m)
    (fun c => by
      rw [dyadicPackedMean_projection]
      rw [abs_sub_comm]
      exact hb c)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at he
  simpa only [approximationWeight,dyadic_product_scale_eq_resolution,
    intervalRho_pow_eq_exp_tau,mul_assoc,Nat.cast_pow,Nat.cast_ofNat] using he

 theorem dyadic_derivative_scale (A : Parameters) (j : ℕ) (s : ℝ) :
    ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ (2 * s) =
      ((2 : ℝ) ^ j) ^ (-2 * (s / A.d)) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Genuine local model estimator variance at every admissible degree. Its
complex, gradient, support and cell-probability bounds are proved from the
model and the explicit class observables. -/
 theorem uniform_localLevelEstimator_variance (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j m n : ℕ), 2 * (m + A.nu + 2) ≤ n →
      variance (localLevelEstimator A hαβ F j m n)
        (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
          varianceConstant C0 * ((2 : ℝ) ^ j) ^
            (-2 * (min (min A.α A.β) 1 / A.d)) / n +
              ∑ k ∈ Finset.range (m + A.nu + 2 - 1),
                varianceTerm (varianceConstant C0) (2 ^ j) n (k + 2) := by
  obtain ⟨Cp,hCp,hlocal⟩ := uniform_model_local_lemma.{u} A hαβ
  let Co := dyadicDesignConstant A (holderOrder A.β)
  let C0 := max Cp Co
  have hpC : Cp ≤ C0 := le_max_left _ _
  have hoC : Co ≤ C0 := le_max_right _ _
  have hC0 : 1 ≤ C0 := hCp.trans hpC
  have hrad : 1 / C0 ≤ 1 / Cp := one_div_le_one_div_of_le (zero_lt_one.trans_le hCp) hpC
  refine ⟨C0,hC0,?_⟩
  intro Z _ F P W j m n hn
  let q := localIncrementPolynomial A hαβ
    (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)) m
  let z := dyadicPackedStatistic A F j
  have hm : (fun k => ∫ o, z o k ∂(P : Measure (Observation A Z))) = dyadicPackedMean A F P j := by
    funext k
    exact dyadicPackedStatistic_coordinate_integral A F P j k
  have hcomplex (c : Fin (2 ^ j)) (y : Fin (localMomentDimension A) → ℂ)
      (hy : ‖y - (fun k => (cellProjection c (fun l => ∫ o, z o l ∂(P : Measure (Observation A Z))) k : ℂ))‖ < 1 / C0) :
      ‖MvPolynomial.eval y (complexify q)‖ ≤ C0 := by
    rw [hm,dyadicPackedMean_projection] at hy
    have hp := (hlocal Z F P W j (dyadicCellEquiv A j c)).2.2.2.2.2.2 m |>.2.2.1
    exact (hp y (hy.trans_le hrad)).trans hpC
  have hgrad (c : Fin (2 ^ j)) :
      ‖(WithLp.toLp 2 (fun k => fderiv ℝ (fun y => MvPolynomial.eval y q)
        (cellProjection c (fun l => ∫ o, z o l ∂(P : Measure (Observation A Z)))) (Pi.single k 1)) :
          EuclideanSpace ℝ (Fin (localMomentDimension A)))‖ ≤
        C0 * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ min (min A.α A.β) 1 := by
    rw [hm,dyadicPackedMean_projection]
    have hp := (hlocal Z F P W j (dyadicCellEquiv A j c)).2.2.2.2.2.2 m |>.2.2.2
    exact hp.trans (mul_le_mul_of_nonneg_right hpC (by positivity))
  have hz (o : Observation A Z) (c : Fin (2 ^ j)) :
      ‖(WithLp.toLp 2 (cellProjection c (z o)) : EuclideanSpace ℝ (Fin (localMomentDimension A)))‖ ≤
        C0 * (2 ^ j : ℕ) * cellIndicator (dyadicPackedSelector A j) c o := by
    have hp := dyadicPackedStatistic_norm_support A F j c o
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hoC (by positivity))
      (by unfold cellIndicator; split_ifs <;> norm_num))
  have hprob (c : Fin (2 ^ j)) :
      (P : Measure (Observation A Z)).real {o | dyadicPackedSelector A j o = c} ≤ C0 / (2 ^ j : ℕ) := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact (dyadicPackedSelector_probability A F P W j c).trans
      (div_le_div_of_nonneg_right hoC (by positivity))
  have hh : 0 < (2 : ℝ) ^ (-(j : ℝ) / A.d) := Real.rpow_pos_of_pos (by norm_num) _
  have hh1 : (2 : ℝ) ^ (-(j : ℝ) / A.d) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by norm_num) (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) (Nat.cast_nonneg A.d))
  have hs0 : 0 < min (min A.α A.β) 1 := lt_min (lt_min A.hα A.hβ) (by norm_num)
  have hv := sampleLift_variance_cells (P : Measure (Observation A Z))
    (by positivity : 0 < 2 ^ j) (by omega : 0 < m + A.nu + 2) hn
    (fun _ : Fin (2 ^ j) => q) (fun _ => localIncrementPolynomial_degree A hαβ _ m)
    z (dyadicPackedStatistic_measurable A F j) (dyadicPackedSelector A j)
    (dyadicPackedSelector_measurable A j) C0 ((2 : ℝ) ^ (-(j : ℝ) / A.d))
    (min (min A.α A.β) 1) hC0 hh hh1 hs0 hcomplex hgrad hz hprob
  rw [dyadic_derivative_scale] at hv
  have hsum : (1 / (n : ℝ)) * ∑ k ∈ Finset.range (m + A.nu + 2 - 1),
        varianceConstant C0 ^ (k + 2) * ((k + 2).factorial : ℝ) *
          ((2 ^ j : ℕ) / (n : ℝ)) ^ (k + 1) =
      ∑ k ∈ Finset.range (m + A.nu + 2 - 1),
        varianceTerm (varianceConstant C0) (2 ^ j) n (k + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold varianceTerm
    rw [show k + 2 - 1 = k + 1 by omega]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [hsum] at hv
  exact hv

end RoughRegime.Model
