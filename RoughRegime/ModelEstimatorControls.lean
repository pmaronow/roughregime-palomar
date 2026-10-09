module

public import RoughRegime.ModelProductEstimator


@[expose] public section
/-! Explicit population polynomial controls imply the actual finite-sample
estimator bias and variance bounds. These controls are the approximation,
complex-neighborhood and gradient conclusions of the proved model lemma. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
open RoughRegime.PolynomialCells RoughRegime.IIDPolynomialEstimator
open RoughRegime.Upper RoughRegime.UpperDegreeRules RoughRegime.LiftVariance
open RoughRegime.ComplexDerivativeBridge RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.UpperTuning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def LocalPolynomialControl (A : Parameters) (hαβ : A.α≤A.β) (C : ℝ) : Prop :=
  ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z A)(P:ProbabilityMeasure (Observation A Z))
    (W:ModelWitness A F P)(j:ℕ)(c:DyadicCell A.d j)(m:ℕ),
    let x:=dyadicDesignMean A F P (holderOrder A.β) c
    let h:=(2:ℝ)^(-(j:ℝ)/A.d)
    let q:=localIncrementPolynomial A hαβ (dyadicSplitAxis A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd)) m
    ‖W.localProjectionIncrement c-MvPolynomial.eval x q‖≤
      C*h^(A.α+A.β)*((m+1:ℕ):ℝ)^A.nu*intervalRho A.gminus A.gplus^m ∧
    (∀t:Fin (localMomentDimension A)→ℂ,
      ‖t-realParametersCLM (localMomentDimension A) x‖<1/C→
        ‖MvPolynomial.eval t (complexify q)‖≤C) ∧
    ‖polynomialGradient q x‖≤C*h^min (min A.α A.β) 1

def BasePolynomialControl (A : Parameters) (C : ℝ) : Prop :=
  ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z A)(P:ProbabilityMeasure (Observation A Z))
    (W:ModelWitness A F P)(m:ℕ),
    let x:=baseDesignMean A F P (holderOrder A.β)
    let q:=baseIncrementPolynomial A m
    ‖W.levelProjectionTarget (holderOrder A.β) 0-MvPolynomial.eval x q‖≤
      C*intervalRho A.gminus A.gplus^m ∧
    (∀t,‖t-realParametersCLM (baseMomentDimension A) x‖<1/C→
      ‖MvPolynomial.eval t (complexify q)‖≤C) ∧
    ‖polynomialGradient q x‖≤C
 theorem localLevelEstimator_bias_from_control (A : Parameters) (hαβ : A.α ≤ A.β) (C : ℝ)
    (hcontrol : LocalPolynomialControl.{u} A hαβ C) :
    ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j m n : ℕ), m + A.nu + 2 ≤ n →
      |(∫ xs, localLevelEstimator A hαβ F j m n xs
          ∂Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) -
        W.levelProjectionIncrement j| ≤
          C * approximationWeight ((2 : ℝ) ^ j) A.theta
            (RoughRegime.Rates.tau A.gminus A.gplus) A.nu m := by
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
    (hcontrol Z F P W j (dyadicCellEquiv A j c) m).1
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

 theorem localLevelEstimator_variance_from_control (A : Parameters) (hαβ : A.α ≤ A.β) (Cp Co : ℝ)
    (hCp : 1≤Cp) (hobs : dyadicDesignConstant A (holderOrder A.β)≤Co)
    (hcontrol : LocalPolynomialControl.{u} A hαβ Cp) :
    ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j m n : ℕ), 2 * (m + A.nu + 2) ≤ n →
      variance (localLevelEstimator A hαβ F j m n)
        (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
          varianceConstant (max Cp Co) * ((2 : ℝ) ^ j) ^
            (-2 * (min (min A.α A.β) 1 / A.d)) / n +
              ∑ k ∈ Finset.range (m + A.nu + 2 - 1),
                varianceTerm (varianceConstant (max Cp Co)) (2 ^ j) n (k + 2) := by
  let C0 := max Cp Co
  have hpC : Cp ≤ C0 := le_max_left _ _
  have hoC : dyadicDesignConstant A (holderOrder A.β) ≤ C0 := hobs.trans (le_max_right _ _)
  have hC0 : 1 ≤ C0 := hCp.trans hpC
  have hrad : 1 / C0 ≤ 1 / Cp := one_div_le_one_div_of_le (zero_lt_one.trans_le hCp) hpC
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
    have hp := (hcontrol Z F P W j (dyadicCellEquiv A j c) m).2.1
    exact (hp y (hy.trans_le hrad)).trans hpC
  have hgrad (c : Fin (2 ^ j)) :
      ‖(WithLp.toLp 2 (fun k => fderiv ℝ (fun y => MvPolynomial.eval y q)
        (cellProjection c (fun l => ∫ o, z o l ∂(P : Measure (Observation A Z)))) (Pi.single k 1)) :
          EuclideanSpace ℝ (Fin (localMomentDimension A)))‖ ≤
        C0 * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ min (min A.α A.β) 1 := by
    rw [hm,dyadicPackedMean_projection]
    have hp := (hcontrol Z F P W j (dyadicCellEquiv A j c) m).2.2
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
 theorem baseLevelEstimator_bias_from_control (A : Parameters) (C : ℝ) (hC : 1≤C)
    (hcontrol : BasePolynomialControl.{u} A C) :
    ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (m n : ℕ),
      m + A.nu + 2 ≤ n →
      |(∫ xs, baseLevelEstimator A F m n xs ∂Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) -
        W.levelProjectionTarget (holderOrder A.β) 0| ≤
      C * approximationWeight 1 A.theta (RoughRegime.Rates.tau A.gminus A.gplus) A.nu m := by
  intro Z _ F P W m n hn
  rw [baseLevelEstimator_mean A F P m n (by omega), baseLevelPolynomial, cellMomentPolynomial_eval]
  simp only [Nat.cast_one, inv_one, Fin.sum_univ_one, one_mul, basePackedMean_projection]
  have he := (hcontrol Z F P W m).1
  have hp : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ A.nu := one_le_pow₀ (by exact_mod_cast Nat.succ_pos m)
  have hρ := (intervalRho_pos A.gminus A.gplus A.hgminus A.hgplus).le
  calc
    _ ≤ C * intervalRho A.gminus A.gplus ^ m := by simpa only [Real.norm_eq_abs, abs_sub_comm] using he
    _ ≤ C * ((m + 1 : ℕ) : ℝ) ^ A.nu * intervalRho A.gminus A.gplus ^ m :=
      mul_le_mul_of_nonneg_right (by nlinarith [zero_le_one.trans hC]) (pow_nonneg hρ m)
    _ = _ := by rw [intervalRho_pow_eq_exp_tau]; simp only [approximationWeight, Real.one_rpow, one_mul]; ring


 theorem baseLevelEstimator_variance_from_control (A : Parameters) (Cp Co : ℝ)
    (hCp : 1≤Cp) (hobs : baseDesignConstant A (holderOrder A.β)≤Co)
    (hcontrol : BasePolynomialControl.{u} A Cp) :
    ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (m n : ℕ),
      2 * (m + A.nu + 2) ≤ n →
      variance (baseLevelEstimator A F m n) (Measure.pi (fun _ : Fin n => (P : Measure (Observation A Z)))) ≤
        varianceConstant (max Cp Co) / n + ∑ k ∈ Finset.range (m + A.nu + 2 - 1),
          varianceTerm (varianceConstant (max Cp Co)) 1 n (k + 2) := by
  let C0 := max Cp Co
  have hpC : Cp ≤ C0 := le_max_left _ _
  have hoC : baseDesignConstant A (holderOrder A.β)≤C0 := hobs.trans (le_max_right _ _)
  have hC0 : 1 ≤ C0 := hCp.trans hpC
  have hrad : 1 / C0 ≤ 1 / Cp := one_div_le_one_div_of_le (zero_lt_one.trans_le hCp) hpC
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
    exact (((hcontrol Z F P W m).2.1) y (hy.trans_le hrad)).trans hpC
  have hgrad (c : Fin 1) :
      ‖(WithLp.toLp 2 (fun k => fderiv ℝ (fun y => MvPolynomial.eval y q)
        (cellProjection c (fun l => ∫ o, z o l ∂(P : Measure (Observation A Z)))) (Pi.single k 1)) :
          EuclideanSpace ℝ (Fin (baseMomentDimension A)))‖ ≤ C0 * (1 : ℝ) ^ (1 : ℝ) := by
    rw [hm, basePackedMean_projection]
    change ‖polynomialGradient (baseIncrementPolynomial A m) (baseDesignMean A F P (holderOrder A.β))‖ ≤
      C0 * (1 : ℝ) ^ (1 : ℝ)
    rw [Real.one_rpow, mul_one]
    exact ((hcontrol Z F P W m).2.2).trans hpC
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
 theorem productEstimator_risk_from_controls (A : Parameters) (hαβ : A.α ≤ A.β)
    (Cp Co Cproj : ℝ) (hCp : 1≤Cp) (hCproj : 0<Cproj)
    (hobsLocal : dyadicDesignConstant A (holderOrder A.β)≤Co)
    (hobsBase : baseDesignConstant A (holderOrder A.β)≤Co)
    (hlocal : LocalPolynomialControl.{u} A hαβ Cp)
    (hbase : BasePolynomialControl.{u} A Cp)
    (hproj : ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z A)
      (P:ProbabilityMeasure (Observation A Z))(W:ModelWitness A F P)(J:ℕ),
      |W.productTarget-(W.levelProjectionTarget (holderOrder A.β) 0+
        ∑j∈Finset.range J,W.levelProjectionIncrement j)|≤Cproj*((2:ℝ)^J)^(-A.theta)) :
    let Cb:=max Cp Cp
    let Cv:=max (varianceConstant (max Cp Co)) (varianceConstant (max Cp Co))
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
  have hbias0:=baseLevelEstimator_bias_from_control.{u} A Cp hCp hbase
  have hbias1:=localLevelEstimator_bias_from_control.{u} A hαβ Cp hlocal
  have hvar0:=baseLevelEstimator_variance_from_control.{u} A Cp Co hCp hobsBase hbase
  have hvar1:=localLevelEstimator_variance_from_control.{u} A hαβ Cp Co hCp hobsLocal hlocal
  let Cb0:=Cp
  let Cb1:=Cp
  let C0:=max Cp Co
  let C1:=max Cp Co
  have hCb0:=hCp
  have hCb1:=hCp
  have hC0:1≤C0:=hCp.trans (le_max_left _ _)
  have hC1:1≤C1:=hCp.trans (le_max_left _ _)
  let Cb := max Cb0 Cb1
  let Cv := max (varianceConstant C0) (varianceConstant C1)
  have hCb : 1 ≤ Cb := hCb0.trans (le_max_left _ _)
  have hCv : 1 ≤ Cv := (varianceConstant_ge_one C0 hC0).trans (le_max_left _ _)
  dsimp only
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
