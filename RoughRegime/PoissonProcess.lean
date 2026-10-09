module

public import RoughRegime.PoissonMixtures


@[expose] public section
/-! Actual count-and-mark probability space for a finite-intensity Poisson
point process, and normalized likelihoods on that observation space. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace RoughRegime.PoissonMeasure

set_option backward.isDefEq.respectTransparency false

variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]

abbrev PointConfiguration (Y : Type*) := Σ n : ℕ, Fin n → Y

theorem measurable_point_mk (n : ℕ) : Measurable (@Sigma.mk ℕ (fun k => Fin k → Y) n : (Fin n → Y) → PointConfiguration Y) := by
  intro s hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) n

theorem measurable_point_function (f : PointConfiguration Y → ℝ)
    (hf : ∀ n, Measurable (fun xs : Fin n → Y => f ⟨n, xs⟩)) : Measurable f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr fun n => hf n hs

def referenceProcess (rate : ℝ≥0) : Measure (PointConfiguration Y) :=
  Measure.sum fun n => ENNReal.ofReal (Lower.poissonMass rate n) •
    (Measure.pi (fun _ : Fin n => μ)).map (Sigma.mk n)

instance referenceProcess_isProbabilityMeasure (rate : ℝ≥0) :
    IsProbabilityMeasure (referenceProcess μ rate) where
  measure_univ := by
    rw [referenceProcess, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, smul_eq_mul]
    simp only [Measure.map_apply (measurable_point_mk _) MeasurableSet.univ, Set.preimage_univ,
      measure_univ, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => Lower.poissonMass_nonneg rate rate.2 n)
      (Lower.poissonMass_hasSum rate).summable, (Lower.poissonMass_hasSum rate).tsum_eq]
    norm_num

omit [IsProbabilityMeasure μ] in
theorem integral_referenceProcess (rate : ℝ≥0) (f : PointConfiguration Y → ℝ)
    (hf : Measurable f) (hi : Integrable f (referenceProcess μ rate)) :
    (∫ x, f x ∂referenceProcess μ rate) =
      ∑' n, Lower.poissonMass rate n * ∫ xs : Fin n → Y, f ⟨n, xs⟩ ∂Measure.pi (fun _ => μ) := by
  rw [referenceProcess, integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_map (measurable_point_mk n).aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal (Lower.poissonMass_nonneg rate rate.2 n)]
  rfl

def processDensityLaw (rate : ℝ≥0)
    (L : ∀ n, GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)))
    (hL : ∀ n xs, 0 ≤ (L n).density xs) : GeneralTesting.DensityLaw (referenceProcess μ rate) where
  density x := (L x.1).density x.2
  measurable := measurable_point_function _ fun n => (L n).measurable
  integrable := by
    have hm : Measurable (fun x : PointConfiguration Y => (L x.1).density x.2) :=
      measurable_point_function _ fun n => (L n).measurable
    have hi (n : ℕ) : Integrable (fun x : PointConfiguration Y => (L x.1).density x.2)
        ((Measure.pi (fun _ : Fin n => μ)).map (Sigma.mk n)) := by
      apply (integrable_map_measure hm.aestronglyMeasurable (measurable_point_mk n).aemeasurable).2
      exact (L n).integrable
    apply integrable_sum_measure
    · intro n
      exact (hi n).smul_measure ENNReal.ofReal_ne_top
    · have he (n : ℕ) : (∫ x : PointConfiguration Y, ‖(L x.1).density x.2‖
          ∂ENNReal.ofReal (Lower.poissonMass rate n) •
            (Measure.pi (fun _ : Fin n => μ)).map (Sigma.mk n)) = Lower.poissonMass rate n := by
        rw [integral_smul_measure,
          integral_map (measurable_point_mk n).aemeasurable hm.norm.aestronglyMeasurable,
          ENNReal.toReal_ofReal (Lower.poissonMass_nonneg rate rate.2 n)]
        have heq : (fun xs : Fin n → Y => |(L n).density xs|) = (L n).density := by
          funext xs
          rw [abs_of_nonneg (hL n xs)]
        simp [heq, (L n).integral_one]
      simp_rw [he]
      exact (Lower.poissonMass_hasSum rate).summable
  nonneg := Filter.Eventually.of_forall fun x => hL x.1 x.2
  integral_one := by
    have hm : Measurable (fun x : PointConfiguration Y => (L x.1).density x.2) :=
      measurable_point_function _ fun n => (L n).measurable
    have hi : Integrable (fun x : PointConfiguration Y => (L x.1).density x.2)
        (referenceProcess μ rate) := by
      have hfi (n : ℕ) : Integrable (fun x : PointConfiguration Y => (L x.1).density x.2)
          ((Measure.pi (fun _ : Fin n => μ)).map (Sigma.mk n)) :=
        (integrable_map_measure hm.aestronglyMeasurable (measurable_point_mk n).aemeasurable).2
          (L n).integrable
      apply integrable_sum_measure
      · intro n
        exact (hfi n).smul_measure ENNReal.ofReal_ne_top
      · have he (n : ℕ) : (∫ x : PointConfiguration Y, ‖(L x.1).density x.2‖
            ∂ENNReal.ofReal (Lower.poissonMass rate n) •
              (Measure.pi (fun _ : Fin n => μ)).map (Sigma.mk n)) = Lower.poissonMass rate n := by
          rw [integral_smul_measure,
            integral_map (measurable_point_mk n).aemeasurable hm.norm.aestronglyMeasurable,
            ENNReal.toReal_ofReal (Lower.poissonMass_nonneg rate rate.2 n)]
          have heq : (fun xs : Fin n → Y => |(L n).density xs|) = (L n).density := by
            funext xs
            rw [abs_of_nonneg (hL n xs)]
          simp [heq, (L n).integral_one]
        simp_rw [he]
        exact (Lower.poissonMass_hasSum rate).summable
    rw [integral_referenceProcess μ rate _ hm hi]
    simp only [(L _).integral_one, mul_one]
    exact (Lower.poissonMass_hasSum rate).tsum_eq

omit [IsProbabilityMeasure μ] in
theorem processDensityLaw_hellinger (rate : ℝ≥0)
    (L R : ∀ n, GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)))
    (hL : ∀ n xs, 0 ≤ (L n).density xs) (hR : ∀ n xs, 0 ≤ (R n).density xs) :
    GeneralTesting.hellingerSquared (processDensityLaw μ rate L hL) (processDensityLaw μ rate R hR) =
      ∫ n : ℕ, GeneralTesting.hellingerSquared (L n) (R n) ∂ProbabilityTheory.poissonMeasure rate := by
  let LA := processDensityLaw μ rate L hL
  let LB := processDensityLaw μ rate R hR
  have hm : Measurable (fun x : PointConfiguration Y =>
      (Real.sqrt (LA.density x) - Real.sqrt (LB.density x)) ^ 2) :=
    (LA.measurable.sqrt.sub LB.measurable.sqrt).pow_const 2
  unfold GeneralTesting.hellingerSquared
  rw [integral_referenceProcess μ rate _ hm (GeneralTesting.hellinger_integrable LA LB),
    ProbabilityTheory.integral_poissonMeasure]
  apply tsum_congr
  intro n
  rfl

theorem hellinger_bounds {S : Type*} [MeasurableSpace S] {ν : Measure S}
    (L R : GeneralTesting.DensityLaw ν) :
    0 ≤ GeneralTesting.hellingerSquared L R ∧ GeneralTesting.hellingerSquared L R ≤ 2 := by
  constructor
  · exact integral_nonneg fun _ => sq_nonneg _
  · have hp : ∀ᵐ x ∂ν, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ≤
        L.density x + R.density x := by
      filter_upwards [L.nonneg, R.nonneg] with x hx hy
      nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
        mul_nonneg (Real.sqrt_nonneg (L.density x)) (Real.sqrt_nonneg (R.density x))]
    have h := integral_mono_ae (GeneralTesting.hellinger_integrable L R)
      (L.integrable.add R.integrable) hp
    change (∫ x, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂ν) ≤
      ∫ x, L.density x + R.density x ∂ν at h
    rw [integral_add L.integrable R.integrable, L.integral_one, R.integral_one] at h
    norm_num at h
    exact h

variable {W : Type*} [MeasurableSpace W] (prior : Measure W) [IsProbabilityMeasure prior]

theorem conditionalMixture_nonneg (A : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C)
    (hψ0 : ∀ w y, 0 ≤ ψ w y) (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) :
    ∀ n xs, 0 ≤ (conditionalMixtureLaw prior μ A ψ hψ V C hV hC hbA hbψ hψ0 hmean n).density xs := by
  intro n xs
  apply integral_nonneg_of_ae
  filter_upwards [A.nonneg] with w hw
  exact mul_nonneg hw (tensor_nonneg ψ hψ0 n w xs)

def markedMixtureLaw (A : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C)
    (hψ0 : ∀ w y, 0 ≤ ψ w y) (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) (rate : ℝ≥0) :
    GeneralTesting.DensityLaw (referenceProcess μ rate) :=
  processDensityLaw μ rate (conditionalMixtureLaw prior μ A ψ hψ V C hV hC hbA hbψ hψ0 hmean)
    (conditionalMixture_nonneg μ prior A ψ hψ V C hV hC hbA hbψ hψ0 hmean)

/-- The general weighted Hellinger estimate in the Poisson comparison, now
for actual probability laws on count-and-mark configurations. -/
theorem markedMixture_hellinger_weighted_le (A B : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbB : ∀ w, |B.density w| ≤ V)
    (hbψ : ∀ w y, |ψ w y| ≤ C)
    (hψ0 : ∀ w y, 0 ≤ ψ w y) (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1)
    (rate : ℝ≥0) (c : ℝ) (hc : 0 < c) (hlow : ∀ w y, c ≤ ψ w y) :
    GeneralTesting.hellingerSquared
      (markedMixtureLaw μ prior A ψ hψ V C hV hC hbA hbψ hψ0 hmean rate)
      (markedMixtureLaw μ prior B ψ hψ V C hV hC hbB hbψ hψ0 hmean rate) ≤
      (1 / 4) * ∫ n : ℕ, (c⁻¹) ^ n * tensorNormSquared prior μ
        (fun w => A.density w - B.density w) ψ n ∂ProbabilityTheory.poissonMeasure rate := by
  let L := conditionalMixtureLaw prior μ A ψ hψ V C hV hC hbA hbψ hψ0 hmean
  let R := conditionalMixtureLaw prior μ B ψ hψ V C hV hC hbB hbψ hψ0 hmean
  let v := fun w => A.density w - B.density w
  have hvb (w : W) : |v w| ≤ 2 * V := by
    have h : |A.density w - B.density w| ≤ |A.density w| + |B.density w| := by
      simpa using abs_sub_le (A.density w) 0 (B.density w)
    dsimp [v]
    linarith [hbA w, hbB w]
  have hs := (poisson_likelihood_square_hasSum prior μ v ψ (A.measurable.sub B.measurable) hψ
    (2 * V) C rate c (by positivity) hC hvb hbψ).summable
  have hni (n : ℕ) : 0 ≤ (c⁻¹) ^ n * tensorNormSquared prior μ v ψ n :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt hc)) n) (tensorNormSquared_nonneg prior μ v ψ n)
  have hwi : Integrable (fun n : ℕ => (c⁻¹) ^ n * tensorNormSquared prior μ v ψ n)
      (ProbabilityTheory.poissonMeasure rate) := by
    apply ProbabilityTheory.integrable_poissonMeasure_iff.mpr
    change Summable (fun n => Lower.poissonMass rate n *
      ‖(c⁻¹) ^ n * tensorNormSquared prior μ v ψ n‖)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hni _)]
    simpa only [mul_assoc] using hs
  have hHi : Integrable (fun n : ℕ => GeneralTesting.hellingerSquared (L n) (R n))
      (ProbabilityTheory.poissonMeasure rate) := by
    apply bounded_integrable _ _ Measurable.of_discrete 2
    intro n
    rw [abs_of_nonneg (hellinger_bounds (L n) (R n)).1]
    exact (hellinger_bounds (L n) (R n)).2
  have hpoint : ∀ᵐ n ∂ProbabilityTheory.poissonMeasure rate,
      GeneralTesting.hellingerSquared (L n) (R n) ≤
        (1 / 4) * ((c⁻¹) ^ n * tensorNormSquared prior μ v ψ n) :=
    Filter.Eventually.of_forall fun n => by
      simpa [L, R, v, mul_assoc] using conditionalMixture_hellinger_le prior μ A B ψ hψ V C
        hV hC hbA hbB hbψ hψ0 hmean c hc hlow n
  have h := integral_mono_ae hHi (hwi.const_mul (1 / 4)) hpoint
  rw [integral_const_mul] at h
  rw [markedMixtureLaw, markedMixtureLaw, processDensityLaw_hellinger]
  exact h

/-- Genuine marked-Poisson mixture comparison by its centered likelihood
chaos coefficients. This is the general-measure analytic core of Lemma 11. -/
theorem markedMixture_hellinger_chaos_le (A B : GeneralTesting.DensityLaw prior)
    (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbA : ∀ w, |A.density w| ≤ V) (hbB : ∀ w, |B.density w| ≤ V)
    (hbψ : ∀ w y, |ψ w y| ≤ C)
    (hψ0 : ∀ w y, 0 ≤ ψ w y) (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1)
    (rate : ℝ≥0) (c : ℝ) (hc : 0 < c) (hlow : ∀ w y, c ≤ ψ w y) :
    GeneralTesting.hellingerSquared
      (markedMixtureLaw μ prior A ψ hψ V C hV hC hbA hbψ hψ0 hmean rate)
      (markedMixtureLaw μ prior B ψ hψ V C hV hC hbB hbψ hψ0 hmean rate) ≤
      (1 / 4) * Real.exp ((rate : ℝ) * (c⁻¹ - 1)) *
        ∑' k, ((rate : ℝ) * c⁻¹) ^ (k + 1) / (k + 1).factorial *
          tensorNormSquared prior μ (fun w => A.density w - B.density w)
            (fun w y => ψ w y - 1) (k + 1) := by
  let v := fun w => A.density w - B.density w
  let φ := fun w y => ψ w y - 1
  have hv : Measurable v := A.measurable.sub B.measurable
  have hφ : Measurable (Function.uncurry φ) := hψ.sub measurable_const
  have hvb (w : W) : |v w| ≤ 2 * V := by
    have h : |A.density w - B.density w| ≤ |A.density w| + |B.density w| := by
      simpa using abs_sub_le (A.density w) 0 (B.density w)
    dsimp [v]
    linarith [hbA w, hbB w]
  have hφb (w : W) (y : Y) : |φ w y| ≤ C + 1 := by
    have h : |ψ w y - 1| ≤ |ψ w y| + |(1 : ℝ)| := by
      simpa using abs_sub_le (ψ w y) 0 1
    dsimp [φ]
    norm_num at h
    linarith [hbψ w y]
  have hφmean (w : W) : (∫ y, φ w y ∂μ) = 0 := by
    have hi : Integrable (ψ w) μ := bounded_integrable μ (ψ w)
      (hψ.comp (measurable_const.prodMk measurable_id)) C (hbψ w)
    simp [φ, integral_sub hi (integrable_const 1), hmean]
  have hvmean : (∫ w, v w ∂prior) = 0 := by
    simp [v, integral_sub A.integrable B.integrable, A.integral_one, B.integral_one]
  have hid := poisson_chaos_identity_positive_orders prior μ v φ hv hφ (2 * V) (C + 1) rate c
    (by positivity) (by positivity) hvb hφb hφmean hvmean
  have he : (fun w y => 1 + φ w y) = ψ := by funext w y; dsimp [φ]; ring
  rw [he] at hid
  have hh := markedMixture_hellinger_weighted_le μ prior A B ψ hψ V C hV hC hbA hbB hbψ
    hψ0 hmean rate c hc hlow
  change _ ≤ (1 / 4) * ∫ n : ℕ, (c⁻¹) ^ n * tensorNormSquared prior μ v ψ n
    ∂ProbabilityTheory.poissonMeasure rate at hh
  rw [hid] at hh
  simpa only [mul_assoc] using hh

end RoughRegime.PoissonMeasure
