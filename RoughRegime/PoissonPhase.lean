module

public import RoughRegime.PoissonSpectral


@[expose] public section
/-! Actual continuous phase priors with correlated signs from assumption A5. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace RoughRegime.PoissonMeasure

set_option backward.isDefEq.respectTransparency false

def uniformSigns : Measure (Bool × Bool) := (1 / 4 : ℝ≥0∞) • Measure.count

instance uniformSigns_isProbabilityMeasure : IsProbabilityMeasure uniformSigns where
  measure_univ := by
    have hc : (Measure.count : Measure (Bool × Bool)) Set.univ = 4 := by
      simp
    rw [uniformSigns, Measure.smul_apply, hc]
    simpa using ENNReal.inv_mul_cancel (a := (4 : ℝ≥0∞)) (by norm_num) (by norm_num)

theorem uniformSigns_integral (f : Bool × Bool → ℝ) :
    (∫ s, f s ∂uniformSigns) = (1 / 4) * ∑ s : Bool, ∑ t : Bool, f (s, t) := by
  rw [uniformSigns, integral_smul_measure, integral_count]
  simp [Fintype.sum_prod_type, smul_eq_mul]

variable {H : Type*} [MeasurableSpace H] (ν : Measure H) [IsProbabilityMeasure ν]

abbrev PhaseParameter (H : Type*) := (H × ℝ) × (Bool × Bool)

def phaseBase : Measure (PhaseParameter H) := (ν.prod LatticePriors.angleUniform).prod uniformSigns

instance phaseBase_isProbabilityMeasure : IsProbabilityMeasure (phaseBase ν) := by
  unfold phaseBase
  infer_instance

def phaseDensity (M : ℕ) (ε : ℝ) (q : PhaseParameter H) : ℝ :=
  1 + ε * Lower.sign q.2.1 * Lower.sign q.2.2 * Real.cos ((M : ℝ) * q.1.2)

theorem phaseDensity_measurable (M : ℕ) (ε : ℝ) : Measurable (phaseDensity (H := H) M ε) := by
  unfold phaseDensity
  have hs : Measurable Lower.sign := Measurable.of_discrete
  fun_prop

omit [MeasurableSpace H] in
theorem phaseDensity_bound (M : ℕ) (ε : ℝ) (hε : |ε| ≤ 1) (q : PhaseParameter H) :
    0 ≤ phaseDensity M ε q ∧ |phaseDensity M ε q| ≤ 2 := by
  have he : |ε * Lower.sign q.2.1 * Lower.sign q.2.2 * Real.cos ((M : ℝ) * q.1.2)| ≤ 1 := by
    cases hs : q.2.1 <;> cases ht : q.2.2 <;>
      simpa [Lower.sign, hs, ht, abs_mul] using
        mul_le_mul hε (Real.abs_cos_le_one ((M : ℝ) * q.1.2)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  unfold phaseDensity
  rw [abs_le] at he
  constructor
  · linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

def phasePrior (M : ℕ) (ε : ℝ) (hε : |ε| ≤ 1) : GeneralTesting.DensityLaw (phaseBase ν) where
  density := phaseDensity M ε
  measurable := phaseDensity_measurable M ε
  integrable := bounded_integrable (phaseBase ν) _ (phaseDensity_measurable M ε) 2
    (fun q => (phaseDensity_bound M ε hε q).2)
  nonneg := Filter.Eventually.of_forall fun q => (phaseDensity_bound M ε hε q).1
  integral_one := by
    have hi : Integrable (phaseDensity (H := H) M ε) (phaseBase ν) :=
      bounded_integrable (phaseBase ν) _ (phaseDensity_measurable M ε) 2
        (fun q => (phaseDensity_bound M ε hε q).2)
    rw [phaseBase, integral_prod _ hi]
    have he (p : H × ℝ) : (∫ s : Bool × Bool, phaseDensity M ε (p, s) ∂uniformSigns) = 1 := by
      rw [uniformSigns_integral]
      simp [phaseDensity, Lower.sign]
      ring
    simp_rw [he]
    simp


theorem densityLaw_integral {W : Type*} [MeasurableSpace W] (μ : Measure W)
    (L : GeneralTesting.DensityLaw μ) (f : W → ℝ) :
    (∫ w, f w ∂L.measure) = ∫ w, L.density w * f w ∂μ := by
  unfold GeneralTesting.DensityLaw.measure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun w => ENNReal.ofReal (L.density w))
    (ENNReal.measurable_ofReal.comp L.measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [L.nonneg] with w hw
  change 0 ≤ L.density w at hw
  simp [ENNReal.toReal_ofReal hw]

omit [MeasurableSpace H] in
theorem sign_power_abs (s : Bool) (k : ℕ) : |Lower.sign s ^ k| = 1 := by
  cases s <;> simp [Lower.sign, abs_pow]

theorem phaseDensity_signed_integrable (M ku kv : ℕ) (ε : ℝ) (hε : |ε| ≤ 1)
    (f : H × ℝ → ℝ) (hf : Measurable f) (B : ℝ) (_hB : 0 ≤ B)
    (hfb : ∀ p, |f p| ≤ B) :
    Integrable (fun q : PhaseParameter H => phaseDensity M ε q *
      (Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv * f q.1)) (phaseBase ν) := by
  have hs : Measurable Lower.sign := Measurable.of_discrete
  apply bounded_integrable _ _ (by unfold phaseDensity; fun_prop) (2 * B)
  intro q
  rw [abs_mul, abs_mul, abs_mul, sign_power_abs, sign_power_abs, one_mul, one_mul]
  exact mul_le_mul (phaseDensity_bound M ε hε q).2 (hfb q.1) (abs_nonneg _) (by norm_num)

omit [MeasurableSpace H] in
theorem uniformSigns_signed_density (M ku kv : ℕ) (ε : ℝ) (p : H × ℝ)
    (v : ℝ) :
    (∫ st : Bool × Bool, phaseDensity M ε (p, st) *
      (Lower.sign st.1 ^ ku * Lower.sign st.2 ^ kv * v) ∂uniformSigns) =
      Lower.signMoment (ε * Real.cos ((M : ℝ) * p.2)) ku kv * v := by
  rw [uniformSigns_integral]
  simp [phaseDensity, Lower.signMoment, Lower.signWeight, Lower.sign]
  ring

theorem phasePrior_signed_integral (M ku kv : ℕ) (ε : ℝ) (hε : |ε| ≤ 1)
    (f : H × ℝ → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ p, |f p| ≤ B) :
    (∫ q : PhaseParameter H, Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv * f q.1
      ∂(phasePrior ν M ε hε).measure) =
      ∫ p, Lower.signMoment (ε * Real.cos ((M : ℝ) * p.2)) ku kv * f p
        ∂ν.prod LatticePriors.angleUniform := by
  unfold GeneralTesting.DensityLaw.measure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun q => ENNReal.ofReal ((phasePrior ν M ε hε).density q))
    (ENNReal.measurable_ofReal.comp (phasePrior ν M ε hε).measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun q : PhaseParameter H =>
      (ENNReal.ofReal ((phasePrior ν M ε hε).density q)).toReal •
        (Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv * f q.1)) =
      fun q => phaseDensity M ε q *
        (Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv * f q.1) := by
    funext q
    change (ENNReal.ofReal (phaseDensity M ε q)).toReal * _ = _
    rw [ENNReal.toReal_ofReal (phaseDensity_bound M ε hε q).1]
  rw [he, phaseBase, integral_prod _ (phaseDensity_signed_integrable ν M ku kv ε hε f hf B hB hfb)]
  simp_rw [uniformSigns_signed_density]

theorem phasePrior_signed_difference (M ku kv : ℕ)
    (f : H × ℝ → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ p, |f p| ≤ B) :
    (∫ q : PhaseParameter H, Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv * f q.1
      ∂(phasePrior ν M 1 (by norm_num)).measure) -
    (∫ q : PhaseParameter H, Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv * f q.1
      ∂(phasePrior ν M (-1) (by norm_num)).measure) =
    if Odd ku ∧ Odd kv then
      2 * ∫ p, Real.cos ((M : ℝ) * p.2) * f p ∂ν.prod LatticePriors.angleUniform
    else 0 := by
  rw [phasePrior_signed_integral ν M ku kv 1 (by norm_num) f hf B hB hfb,
    phasePrior_signed_integral ν M ku kv (-1) (by norm_num) f hf B hB hfb]
  have hip := (phaseDensity_signed_integrable ν M ku kv 1 (by norm_num) f hf B hB hfb).integral_prod_left
  have him := (phaseDensity_signed_integrable ν M ku kv (-1) (by norm_num) f hf B hB hfb).integral_prod_left
  simp only [uniformSigns_signed_density, one_mul, neg_one_mul] at hip him ⊢
  exact Lower.phase_sign_difference _ _ _ ku kv hip him


/-- Actual signed-prior Gamma cancellation: every affine angular product of
fewer than M density factors has zero difference under the two priors. -/
theorem phasePrior_signed_affine_zero (ku kv j M : ℕ) (hj : j < M)
    (w : H → ℝ) (c a b : Fin j → H → ℝ)
    (hw : Measurable w) (hc : ∀ i, Measurable (c i))
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbw : ∀ h, |w h| ≤ A) (hbc : ∀ i h, |c i h| ≤ C)
    (hba : ∀ i h, |a i h| ≤ C) (hbb : ∀ i h, |b i h| ≤ C) :
    (∫ q : PhaseParameter H, Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv *
      (w q.1.1 * ∏ i, (c i q.1.1 + a i q.1.1 * Real.cos q.1.2 +
        b i q.1.1 * Real.sin q.1.2)) ∂(phasePrior ν M 1 (by norm_num)).measure) -
    (∫ q : PhaseParameter H, Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv *
      (w q.1.1 * ∏ i, (c i q.1.1 + a i q.1.1 * Real.cos q.1.2 +
        b i q.1.1 * Real.sin q.1.2)) ∂(phasePrior ν M (-1) (by norm_num)).measure) = 0 := by
  let f := fun p : H × ℝ => w p.1 * ∏ i,
    (c i p.1 + a i p.1 * Real.cos p.2 + b i p.1 * Real.sin p.2)
  have hm : Measurable f := by
    apply (hw.comp measurable_fst).mul
    apply Finset.measurable_prod
    intro i _
    exact ((hc i).comp measurable_fst).add
      (((ha i).comp measurable_fst).mul measurable_snd.cos) |>.add
        (((hb i).comp measurable_fst).mul measurable_snd.sin)
  have hbound : ∀ p, |f p| ≤ A * (3 * C) ^ j := by
    rintro ⟨h, θ⟩
    have hp : |∏ i, (c i h + a i h * Real.cos θ + b i h * Real.sin θ)| ≤ (3 * C) ^ j := by
      rw [Finset.abs_prod]
      have hi := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun i : Fin j => |c i h + a i h * Real.cos θ + b i h * Real.sin θ|)
        (g := fun _ => 3 * C) (fun _ _ => abs_nonneg _)
        (fun i _ => affine_factor_bound _ _ _ _ C hC (hbc i h) (hba i h) (hbb i h))
      simpa using hi
    change |w h * _| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hbw h) hp (abs_nonneg _) hA
  have hd := phasePrior_signed_difference ν M ku kv f hm (A * (3 * C) ^ j)
    (by positivity) hbound
  have hz := latent_affine_angular_zero ν j M hj w c a b hw hc ha hb A C hA hC hbw hbc hba hbb
  have hmul : (fun p : H × ℝ => Real.cos ((M : ℝ) * p.2) * f p) =
      fun p => w p.1 * Real.cos ((M : ℝ) * p.2) *
        ∏ i, (c i p.1 + a i p.1 * Real.cos p.2 + b i p.1 * Real.sin p.2) := by
    funext p
    dsimp [f]
    ring
  rw [hmul, hz] at hd
  simpa only [f, mul_zero, ite_self] using hd

end RoughRegime.PoissonMeasure
