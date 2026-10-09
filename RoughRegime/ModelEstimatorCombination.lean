module

public import RoughRegime.SampleMeanBound
public import RoughRegime.ModelSwap


@[expose] public section
/-! The actual measurable estimator for the complete generic target combines
the empirical observable mean with the constructed mean-product estimator. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RoughRegime.Model

def combinedEstimator (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (n : ℕ) (E : (Fin n→Observation A Z)→ℝ) (hE : Measurable E) :
    Estimator (Observation A Z) n :=
  ⟨fun o => Applications.empiricalMean (F.W∘Prod.snd) o.1+F.lam*E o.1,
    ((Applications.empiricalMean_measurable _ (F.measurableW.comp measurable_snd)).comp measurable_fst).add
      (measurable_const.mul (hE.comp measurable_fst))⟩

theorem combinedEstimator_sample_memLp (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (n : ℕ)
    (E : (Fin n→Observation A Z)→ℝ)
    (hmem : MemLp E 2 (Measure.pi (fun _ : Fin n => (P:Measure (Observation A Z))))) :
    MemLp (fun xs => Applications.empiricalMean (F.W∘Prod.snd) xs+F.lam*E xs) 2
      (Measure.pi (fun _ : Fin n => (P:Measure (Observation A Z)))) := by
  obtain ⟨M,_,hM⟩ := F.boundW
  exact (Applications.empiricalMean_memLp (P:Measure (Observation A Z)) _
    (Applications.bounded_memLp _ _ (F.measurableW.comp measurable_snd) M (fun o => hM o.2))).add
      (hmem.const_mul _)

theorem combinedEstimator_eLpNorm_error (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
    (n : ℕ) (hn : 0<n) (E : (Fin n→Observation A Z)→ℝ) (hE : Measurable E)
    (hmem : MemLp E 2 (Measure.pi (fun _ : Fin n => (P:Measure (Observation A Z)))))
    (MW : ℝ) (hMW : ∀ z, |F.W z|≤MW) :
    eLpNorm (fun o => (combinedEstimator A F n E hE).val o-target A F P) 2 (randomizedExperiment n P)≤
      ENNReal.ofReal (|MW| / Real.sqrt n+|F.lam| *
        lpNorm (fun xs => E xs-W.productTarget) 2 (Measure.pi (fun _ : Fin n => (P:Measure (Observation A Z))))) := by
  let μ := Measure.pi (fun _ : Fin n => (P:Measure (Observation A Z)))
  let meanError : (Fin n→Observation A Z)→ℝ :=
    fun xs => Applications.empiricalMean (F.W∘Prod.snd) xs-∫ o, F.W o.2 ∂(P:Measure (Observation A Z))
  let productError : (Fin n→Observation A Z)→ℝ := fun xs => E xs-W.productTarget
  have hmean := Applications.empiricalMean_eLpNorm_error (P:Measure (Observation A Z)) hn
    (F.W∘Prod.snd) (F.measurableW.comp measurable_snd) |MW| (abs_nonneg _)
    (fun o => (hMW o.2).trans (le_abs_self MW))
  have hprodMem : MemLp productError 2 μ := hmem.sub (memLp_const _)
  have hprod : eLpNorm (fun xs => F.lam*productError xs) 2 μ=
      ENNReal.ofReal (|F.lam| * lpNorm productError 2 μ) := by
    change eLpNorm (F.lam • productError) 2 μ=_
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,← ofReal_lpNorm hprodMem,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
  have herror : (fun o => (combinedEstimator A F n E hE).val o-target A F P)=
      (fun xs => meanError xs+F.lam*productError xs)∘Prod.fst := by
    funext o
    rw [W.target_eq_linear_product]
    dsimp [combinedEstimator,meanError,productError]
    ring
  have hm : Measurable (fun xs => meanError xs+F.lam*productError xs) :=
    ((Applications.empiricalMean_measurable _ (F.measurableW.comp measurable_snd)).sub measurable_const).add
      (measurable_const.mul (hE.sub measurable_const))
  rw [herror]
  change eLpNorm ((fun xs => meanError xs+F.lam*productError xs)∘Prod.fst) 2 (μ.prod KernelSeedBridge.seedLaw)≤_
  rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable measurePreserving_fst]
  calc
    _ ≤ eLpNorm meanError 2 μ+eLpNorm (fun xs => F.lam*productError xs) 2 μ := eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (|MW| / Real.sqrt n)+ENNReal.ofReal (|F.lam| * lpNorm productError 2 μ) := add_le_add hmean hprod.le
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (abs_nonneg _) lpNorm_nonneg)]

end RoughRegime.Model
