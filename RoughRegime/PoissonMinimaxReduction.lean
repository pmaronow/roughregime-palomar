module

public import RoughRegime.DePoissonization
public import RoughRegime.FuzzyRandomized


@[expose] public section
/-! Exact fixed-sample lower risk from the genuine ordered Poisson experiment.
The estimator infima include every measurable independent-seed rule. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem poisson_minimax_to_fixed_tail {W Y : Type*} [MeasurableSpace Y]
    (P : W → ProbabilityMeasure Y) (T : ProbabilityMeasure Y → ℝ)
    (C : Set (ProbabilityMeasure Y)) (hC : ∀ w,P w∈C)
    (rate : ℝ≥0) (n : ℕ) (δ : ℝ)
    (hstrong : (13/32 : ℝ≥0∞)   ≤   KernelTransfers.minimaxTail
      (fun w=>referenceProcess (P w : Measure Y) rate) (fun w=>T (P w)) Set.univ δ)
    (hcount : ProbabilityTheory.poissonMeasure rate {m | m < n}  ≤  (1/32 : ℝ≥0∞)) :
    (3/8 : ℝ≥0∞)   ≤   Model.minimaxTail n T C δ := by
  unfold Model.minimaxTail
  apply le_iInf
  intro g
  have hseed : (13/32 : ℝ≥0∞)   ≤   Applications.minimaxTail
      (fun w=>(referenceProcess (P w : Measure Y) rate).prod KernelSeedBridge.seedLaw)
      (fun w=>T (P w)) Set.univ δ := by
    rw [KernelSeedBridge.seed_minimaxTail_eq_kernel]
    exact hstrong
  let gp : Applications.Estimator (PointConfiguration Y×ℝ) :=
    ⟨liftEstimatorWithSeed n g.val 0,liftEstimatorWithSeed_measurable n g.val g.property 0⟩
  have hs : (13/32 : ℝ≥0∞)   ≤   ⨆ w,
      ((referenceProcess (P w : Measure Y) rate).prod KernelSeedBridge.seedLaw)
        {q | δ  ≤  |liftEstimatorWithSeed n g.val 0 q-T (P w)|} := by
    simpa only [Applications.minimaxTail,Set.mem_univ,iSup_true,gp] using
      hseed.trans (iInf_le _ gp)
  have hf := depoissonized_worst_tail (Y:=Y) (Seed:=ℝ) P KernelSeedBridge.seedLaw
    rate n g.val g.property 0 (fun w=>T (P w)) δ hs hcount
  apply hf.trans
  apply iSup_le
  intro w
  exact le_iSup_of_le (P w) (le_iSup_of_le (hC w) le_rfl)

end RoughRegime.PoissonMeasure

namespace RoughRegime.Model
/-- The strict 3/8 testing bound directly gives a half-threshold RMS bound
on the same actual iid experiment, without an attainment assumption. -/
theorem minimaxRMSE_lower_of_three_eighths {Y : Type*} [MeasurableSpace Y]
    (n : ℕ) (T : ProbabilityMeasure Y → ℝ) (C : Set (ProbabilityMeasure Y))
    (δ : ℝ) (hδ : 0  ≤  δ) (htail : (3/8 : ℝ≥0∞)  ≤  minimaxTail n T C δ) :
    ENNReal.ofReal (δ/2)  ≤  minimaxRMSE n T C := by
  unfold minimaxRMSE
  apply le_iInf
  intro g
  have hs := htail.trans (iInf_le _ g)
  have hq : (1/4 : ℝ≥0∞)<⨆ (P : ProbabilityMeasure Y) (_ : P∈C),
      randomizedExperiment n P {o | δ  ≤  |g.val o-T P|} := by
    have hq0 : (1/4 : ℝ≥0∞)<3/8 := by
      have h := ENNReal.ofReal_lt_ofReal_iff (p := 1/4) (q := 3/8) (by norm_num : (0:ℝ)<3/8)
      have hr : ENNReal.ofReal (1/4:ℝ)<ENNReal.ofReal (3/8:ℝ) := h.mpr (by norm_num)
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8),ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hr
    exact lt_of_lt_of_le hq0 hs
  obtain ⟨P,hP⟩ := (lt_iSup_iff).mp hq
  obtain ⟨hPC,hP⟩ := (lt_iSup_iff).mp hP
  have hd1 : 2*δ/2=δ := by ring
  have hd2 : 2*δ/4=δ/2 := by ring
  have he := GeneralTesting.tail_to_eLpNorm (randomizedExperiment n P) g.val g.property
    (T P) (2*δ) (by positivity) (by rw [hd1]; exact hP.le)
  rw [hd2] at he
  exact he.trans (le_iSup_of_le P (le_iSup_of_le hPC le_rfl))

theorem minimaxTail_antitone_threshold {Y : Type*} [MeasurableSpace Y]
    (n : ℕ) (T : ProbabilityMeasure Y → ℝ) (C : Set (ProbabilityMeasure Y))
    {s t : ℝ} (hst : s  ≤  t) : minimaxTail n T C t  ≤  minimaxTail n T C s := by
  unfold minimaxTail
  apply iInf_mono
  intro g
  apply iSup_mono
  intro P
  apply iSup_mono
  intro _
  exact measure_mono fun _ h=>hst.trans h
end RoughRegime.Model

namespace RoughRegime.GeneralTesting
set_option backward.isDefEq.respectTransparency false

/-- The full statistical reduction uses the actual common placement kernel,
true fuzzy-prior marginals, true ordered Poisson laws, and true iid laws. -/
theorem fuzzy_placement_fixed_minimax {W Ω Y : Type*} [MeasurableSpace W]
    [MeasurableSpace Ω] [MeasurableSpace Y] {μ : Measure Ω} [SigmaFinite μ]
    (L R : DensityLaw μ) (PL PR : Measure W)
    [IsProbabilityMeasure PL] [IsProbabilityMeasure PR]
    (K : Kernel W Ω) [IsMarkovKernel K]
    (hPL : (PL ⊗ₘ K).map Prod.snd = L.measure)
    (hPR : (PR ⊗ₘ K).map Prod.snd = R.measure)
    (J : Kernel Ω (PoissonMeasure.PointConfiguration Y)) [IsMarkovKernel J]
    (P : W → ProbabilityMeasure Y) (T : ProbabilityMeasure Y → ℝ)
    (rate : ℝ≥0) (hlaw : ∀ w,
      PoissonMeasure.referenceProcess (P w : Measure Y) rate=J ∘ₘ K w)
    (C : Set (ProbabilityMeasure Y)) (hC : ∀ w,P w∈C)
    (ht : Measurable (fun w=>T (P w)))
    (htL : MemLp (fun w=>T (P w)) 2 PL) (htR : MemLp (fun w=>T (P w)) 2 PR)
    (hH : hellingerSquared L R  ≤  1/128)
    (hsep : 0 < |(∫ w,T (P w) ∂PR)-(∫ w,T (P w) ∂PL)|)
    (hvL : variance (fun w=>T (P w)) PL  ≤  |(∫ w,T (P w) ∂PR)-(∫ w,T (P w) ∂PL)|^2/1024)
    (hvR : variance (fun w=>T (P w)) PR  ≤  |(∫ w,T (P w) ∂PR)-(∫ w,T (P w) ∂PL)|^2/1024)
    (n : ℕ) (hcount : ProbabilityTheory.poissonMeasure rate {m | m < n} ≤ (1/32 : ℝ≥0∞))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hδgap : δ ≤ |(∫ w,T (P w) ∂PR)-(∫ w,T (P w) ∂PL)|/4) :
    (3/8 : ℝ≥0∞)  ≤  Model.minimaxTail n T C δ ∧
      ENNReal.ofReal (δ/2)  ≤  Model.minimaxRMSE n T C := by
  let target := fun w=>T (P w)
  let gap := |(∫ w,target w ∂PR)-(∫ w,target w ∂PL)|
  have hs := fuzzy_minimaxTail_variance_strong L R PL PR K hPL hPR target ht htL htR
    hH hsep hvL hvR
  have hp : KernelTransfers.minimaxTail (fun w=>K w) target Set.univ (gap/4)  ≤ 
      KernelTransfers.minimaxTail (fun w=>PoissonMeasure.referenceProcess (P w : Measure Y) rate)
        target Set.univ (gap/4) := by
    exact KernelTransfers.kernel_minimax_loss J _ _ target target Set.univ Set.univ id
      (fun _ _=>Set.mem_univ _) (fun w _=>hlaw w) (fun _ _=>rfl)
      (fun a y=>if gap/4 ≤ |y-a| then 1 else 0)
  have hf := PoissonMeasure.poisson_minimax_to_fixed_tail P T C hC rate n (gap/4)
    (hs.trans hp) hcount
  have ht := hf.trans (Model.minimaxTail_antitone_threshold n T C hδgap)
  exact ⟨ht,Model.minimaxRMSE_lower_of_three_eighths n T C δ hδ ht⟩
end RoughRegime.GeneralTesting
