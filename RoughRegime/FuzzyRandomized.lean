module

public import RoughRegime.FuzzyTesting
public import RoughRegime.KernelSeedBridge
public import RoughRegime.LowerMeasure


@[expose] public section
/-! Genuine fuzzy-prior testing for arbitrary randomized output rules. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.GeneralTesting
set_option backward.isDefEq.respectTransparency false

 theorem kernel_with_seed_law {W Ω S : Type*} [MeasurableSpace W]
     [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure W) [SFinite P]
     (K : Kernel W Ω) [IsSFiniteKernel K] (ν : Measure S) [SFinite ν] :
     ((Kernel.id ×ₖ Kernel.const Ω ν) ∘ₖ K) ∘ₘ P = (K ∘ₘ P).prod ν := by
   rw [←Measure.comp_assoc,←Measure.compProd_eq_comp_prod,Measure.compProd_const]

/-- Randomized estimators retain the strict margin required for exact 3/8
fixed-sample testing after de-Poissonization. -/
theorem fuzzy_randomized_variance_strong {W Ω : Type*} [MeasurableSpace W]
    [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    (L R : DensityLaw μ) (PL PR : Measure W)
    [IsProbabilityMeasure PL] [IsProbabilityMeasure PR]
    (K : Kernel W Ω) [IsMarkovKernel K]
    (hPL : (PL ⊗ₘ K).map Prod.snd = L.measure)
    (hPR : (PR ⊗ₘ K).map Prod.snd = R.measure)
    (target : W → ℝ) (ht : Measurable target)
    (htL : MemLp target 2 PL) (htR : MemLp target 2 PR)
    (δ : Kernel Ω ℝ) [IsMarkovKernel δ]
    (hH : hellingerSquared L R ≤ 1/128)
    (hsep : 0 < |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|)
    (hvL : variance target PL ≤ |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|^2/1024)
    (hvR : variance target PR ≤ |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|^2/1024) :
    (13/32 : ℝ≥0∞) ≤ ⨆ w, (δ ∘ₖ K) w
      {y | |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|/4 ≤ |y-target w|} := by
  obtain ⟨g,hg,heq⟩ := KernelSeedBridge.kernel_exists_seedRule δ
  let KS : Kernel W (Ω×ℝ) :=
    (Kernel.id ×ₖ Kernel.const Ω KernelSeedBridge.seedLaw) ∘ₖ K
  have hLs : (PL ⊗ₘ KS).map Prod.snd =
      (LowerMeasure.densityLawWithSeed KernelSeedBridge.seedLaw L).measure := by
    rw [←Measure.snd,Measure.snd_compProd,kernel_with_seed_law,
      LowerMeasure.densityLawWithSeed_measure]
    have he : K ∘ₘ PL = L.measure := by
      simpa only [Measure.snd_compProd] using (show (PL ⊗ₘ K).snd = L.measure from hPL)
    rw [he]
  have hRs : (PR ⊗ₘ KS).map Prod.snd =
      (LowerMeasure.densityLawWithSeed KernelSeedBridge.seedLaw R).measure := by
    rw [←Measure.snd,Measure.snd_compProd,kernel_with_seed_law,
      LowerMeasure.densityLawWithSeed_measure]
    have he : K ∘ₘ PR = R.measure := by
      simpa only [Measure.snd_compProd] using (show (PR ⊗ₘ K).snd = R.measure from hPR)
    rw [he]
  have hHs : hellingerSquared (LowerMeasure.densityLawWithSeed KernelSeedBridge.seedLaw L)
      (LowerMeasure.densityLawWithSeed KernelSeedBridge.seedLaw R) ≤ 1/128 := by
    rw [LowerMeasure.hellinger_with_seed]
    exact hH
  have h := fuzzy_kernel_variance_strong
    (LowerMeasure.densityLawWithSeed KernelSeedBridge.seedLaw L)
    (LowerMeasure.densityLawWithSeed KernelSeedBridge.seedLaw R)
    PL PR KS hLs hRs target ht htL htR g hg hHs hsep hvL hvR
  have he (w : W) : KS w = (K w).prod KernelSeedBridge.seedLaw := by
    change (Kernel.id ×ₖ Kernel.const Ω KernelSeedBridge.seedLaw) ∘ₘ K w = _
    rw [←Measure.compProd_eq_comp_prod,Measure.compProd_const]
  have hd (w : W) : (δ ∘ₖ K) w = ((K w).prod KernelSeedBridge.seedLaw).map g := by
    change δ ∘ₘ K w = _
    rw [←heq,KernelSeedBridge.seedRule_law g hg]
  convert h using 1
  apply iSup_congr
  intro w
  rw [he,hd,Measure.map_apply hg]
  · rfl
  · exact measurableSet_le measurable_const ((measurable_id.sub measurable_const).abs)

/-- The fuzzy lower bound holds after the infimum over every real-output
Markov rule, including arbitrary internal randomization. -/
theorem fuzzy_minimaxTail_variance_strong {W Ω : Type*} [MeasurableSpace W]
    [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    (L R : DensityLaw μ) (PL PR : Measure W)
    [IsProbabilityMeasure PL] [IsProbabilityMeasure PR]
    (K : Kernel W Ω) [IsMarkovKernel K]
    (hPL : (PL ⊗ₘ K).map Prod.snd = L.measure)
    (hPR : (PR ⊗ₘ K).map Prod.snd = R.measure)
    (target : W → ℝ) (ht : Measurable target)
    (htL : MemLp target 2 PL) (htR : MemLp target 2 PR)
    (hH : hellingerSquared L R ≤ 1/128)
    (hsep : 0 < |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|)
    (hvL : variance target PL ≤ |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|^2/1024)
    (hvR : variance target PR ≤ |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|^2/1024) :
    (13/32 : ℝ≥0∞) ≤ KernelTransfers.minimaxTail (fun w=>K w) target Set.univ
      (|(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|/4) := by
  rw [KernelTransfers.minimaxTail_eq_probability]
  apply le_iInf
  intro δ
  let : IsMarkovKernel δ.val := δ.property
  simpa only [Set.mem_univ,iSup_true,Kernel.comp_apply] using fuzzy_randomized_variance_strong L R PL PR K hPL hPR target ht htL htR
    δ.val hH hsep hvL hvR

end RoughRegime.GeneralTesting
