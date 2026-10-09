module

public import RoughRegime.ApplicationsRisk
public import RoughRegime.KernelSeedBridge
public import RoughRegime.Model


@[expose] public section
/-! Actual iid sample means for the additive observable part of the target. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.Applications

theorem empiricalMean_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (f : Ω→ℝ) (hf : Measurable f) : Measurable (empiricalMean (n:=n) f) := by
  unfold empiricalMean
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i)))

theorem bounded_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω→ℝ) (hf : Measurable f) (M : ℝ)
    (hb : ∀ x, |f x|≤M) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable M (ae_of_all μ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem empiricalMean_error_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (f : Ω→ℝ) (hf : Measurable f) (M : ℝ)
    (hb : ∀ x, |f x|≤M) :
    MemLp (fun x => empiricalMean (n:=n) f x-∫ y, f y ∂μ) 2 (Measure.pi (fun _ : Fin n => μ)) :=
  (empiricalMean_memLp μ f (bounded_memLp μ f hf M hb)).sub (memLp_const _)

theorem empiricalMean_mse_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n) (f : Ω→ℝ) (hf : Measurable f)
    (M : ℝ) (_hM : 0≤M) (hb : ∀ x, |f x|≤M) :
    (∫ x, (empiricalMean (n:=n) f x-∫ y, f y ∂μ)^2 ∂Measure.pi (fun _ : Fin n => μ))≤M^2/n := by
  have hm := bounded_memLp μ f hf M hb
  rw [empiricalMean_mse μ hn.ne' f hm,← variance_eq_integral hm.aemeasurable]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hv := variance_le_sq_of_bounded (μ:=μ) (a:=-M) (b:=M)
    (ae_of_all μ (fun x => abs_le.mp (hb x))) hf.aemeasurable
  convert hv using 1; ring

theorem empiricalMean_variance_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n) (f : Ω→ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ x, |f x|≤M) :
    variance (empiricalMean (n:=n) f) (Measure.pi (fun _ : Fin n => μ))≤M^2/n := by
  rw [variance_eq_integral (empiricalMean_measurable f hf).aemeasurable,
    empiricalMean_expectation μ hn.ne' f (bounded_memLp μ f hf M hb)]
  exact empiricalMean_mse_bound μ hn f hf M hM hb

theorem empiricalMean_eLpNorm_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n) (f : Ω→ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ x, |f x|≤M) :
    eLpNorm (fun x => empiricalMean (n:=n) f x-∫ y, f y ∂μ) 2
      (Measure.pi (fun _ : Fin n => μ))≤ENNReal.ofReal (M/Real.sqrt n) :=
  eLpNorm_two_le_of_mse _ _ ((empiricalMean_measurable f hf).sub measurable_const)
    (empiricalMean_error_memLp μ f hf M hb).integrable_sq M n hM (Nat.cast_pos.mpr hn)
    (empiricalMean_mse_bound μ hn f hf M hM hb)

theorem empiricalMean_lpNorm_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n) (f : Ω→ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ x, |f x|≤M) :
    lpNorm (fun x => empiricalMean (n:=n) f x-∫ y, f y ∂μ) 2
      (Measure.pi (fun _ : Fin n => μ))≤M/Real.sqrt n := by
  have he := empiricalMean_eLpNorm_error μ hn f hf M hM hb
  rw [← ofReal_lpNorm (empiricalMean_error_memLp μ f hf M hb)] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he

end RoughRegime.Applications
namespace RoughRegime.Model

def sampleMeanEstimator {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (f : Ω→ℝ) (hf : Measurable f) : Estimator Ω n :=
  ⟨fun o => Applications.empiricalMean f o.1,(Applications.empiricalMean_measurable f hf).comp measurable_fst⟩

theorem sampleMeanEstimator_eLpNorm_error {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (hn : 0<n) (P : ProbabilityMeasure Ω) (f : Ω→ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ x, |f x|≤M) :
    eLpNorm (fun o => (sampleMeanEstimator n f hf).val o-∫ x, f x ∂(P:Measure Ω)) 2
      (randomizedExperiment n P)≤ENNReal.ofReal (M/Real.sqrt n) := by
  have hm : Measurable (fun x : Fin n→Ω => Applications.empiricalMean f x-∫ y, f y ∂(P:Measure Ω)) :=
    (Applications.empiricalMean_measurable (n:=n) f hf).sub measurable_const
  change eLpNorm ((fun x => Applications.empiricalMean f x-∫ y, f y ∂(P:Measure Ω))∘Prod.fst) 2
    ((Measure.pi (fun _ : Fin n => (P:Measure Ω))).prod KernelSeedBridge.seedLaw)≤_
  rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable measurePreserving_fst]
  exact Applications.empiricalMean_eLpNorm_error (P:Measure Ω) hn f hf M hM hb

end RoughRegime.Model
