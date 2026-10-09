module

public import RoughRegime.KernelTransfers
public import RoughRegime.RiskBridge


@[expose] public section
/-! Every randomized real-output kernel is equivalent to a measurable estimator
using the model's independent uniform real seed. No structural assumption on
the observation measurable space is needed: the kernel output space is ℝ. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology unitInterval
namespace RoughRegime.KernelSeedBridge

def seedLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure seedLaw := by
  rw [seedLaw, ← unitInterval.measurePreserving_coe.map_eq]
  infer_instance

/-- A jointly measurable seed estimator defines a law-independent real-output kernel. -/
def seedRule {Ω : Type*} [MeasurableSpace Ω] (g : Ω × ℝ → ℝ) : Kernel Ω ℝ :=
  (Kernel.id ×ₖ Kernel.const Ω seedLaw).map g

theorem seedRule_markov {Ω : Type*} [MeasurableSpace Ω] (g : Ω × ℝ → ℝ) (hg : Measurable g) :
    IsMarkovKernel (seedRule g) := by
  exact Kernel.IsMarkovKernel.map _ hg

theorem seedRule_apply {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω × ℝ → ℝ) (hg : Measurable g) (x : Ω) :
    seedRule g x = seedLaw.map (fun u => g (x, u)) := by
  have hx : Measurable (fun u => g (x, u)) := hg.comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [seedRule, Kernel.map_apply' _ hg _ hs,
    Kernel.id_prod_apply' _ _ (hg hs), Kernel.const_apply,
    Measure.map_apply hx hs]
  rfl

/-- The output law of a seed estimator agrees with its associated kernel. -/
theorem seedRule_law {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω × ℝ → ℝ) (hg : Measurable g) (μ : Measure Ω) [SFinite μ] :
    seedRule g ∘ₘ μ = (μ.prod seedLaw).map g := by
  rw [seedRule, ← Measure.map_comp μ _ hg, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const]

/-- A real-output Markov kernel has exactly a measurable uniform-real-seed realization. -/
theorem kernel_exists_seedRule {Ω : Type*} [MeasurableSpace Ω]
    (δ : Kernel Ω ℝ) [IsMarkovKernel δ] :
    ∃ g : Ω × ℝ → ℝ, Measurable g ∧ seedRule g = δ := by
  obtain ⟨f, hf, hmap⟩ := δ.exists_measurable_map_eq_unitInterval
  let g : Ω × ℝ → ℝ := fun x => f x.1 (Set.projIcc (0 : ℝ) 1 (by norm_num) x.2)
  have hclip : Measurable (Set.projIcc (0 : ℝ) 1 (by norm_num)) :=
    continuous_projIcc.measurable
  have hp : Measurable (fun x : Ω × ℝ => (x.1, Set.projIcc (0 : ℝ) 1 (by norm_num) x.2)) :=
    measurable_fst.prodMk (hclip.comp measurable_snd)
  have hg : Measurable g := hf.comp hp
  refine ⟨g, hg, ?_⟩
  ext x : 1
  have hx : Measurable (fun u => g (x, u)) := hg.comp (measurable_const.prodMk measurable_id)
  rw [seedRule_apply g hg, seedLaw, ← unitInterval.measurePreserving_coe.map_eq,
    Measure.map_map hx measurable_subtype_coe]
  have heq : ((fun u : ℝ => g (x, u)) ∘ ((↑) : I → ℝ)) = f x := by
    ext u
    dsimp only [Function.comp_def, g]
    rw [Set.projIcc_of_mem _ u.property]
  rw [heq, hmap]

def seedMinimaxLoss {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (T : Θ → ℝ) (C : Set Θ) (loss : ℝ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ g : RoughRegime.Applications.Estimator (Ω × ℝ), ⨆ θ ∈ C,
    ∫⁻ x, loss (T θ) (g.val x) ∂((laws θ).prod seedLaw)

/-- Equality holds for every measurable nonnegative loss, uniformly over all laws. -/
theorem seedMinimaxLoss_eq_kernel {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T : Θ → ℝ) (C : Set Θ) (loss : ℝ → ℝ → ℝ≥0∞)
    (hloss : ∀ a, Measurable (loss a)) :
    seedMinimaxLoss laws T C loss = KernelTransfers.minimaxLoss laws T C loss := by
  have hsame : ∀ g : RoughRegime.Applications.Estimator (Ω × ℝ), ∀ θ,
      (∫⁻ x, loss (T θ) (g.val x) ∂((laws θ).prod seedLaw)) =
      ∫⁻ y, loss (T θ) y ∂(seedRule g.val ∘ₘ laws θ) := by
    intro g θ
    rw [seedRule_law g.val g.property]
    exact (lintegral_map (hloss _) g.property).symm
  apply le_antisymm
  · apply le_iInf
    intro δ
    have : IsMarkovKernel δ.val := δ.property
    obtain ⟨g, hg, heq⟩ := kernel_exists_seedRule δ.val
    apply (iInf_le _ ⟨g, hg⟩).trans
    apply iSup_le
    intro θ
    apply iSup_le
    intro hθ
    rw [hsame, heq]
    exact le_iSup_of_le θ (le_iSup_of_le hθ le_rfl)
  · apply le_iInf
    intro g
    have : IsMarkovKernel (seedRule g.val) := seedRule_markov g.val g.property
    apply (iInf_le _ (⟨seedRule g.val, inferInstance⟩ : KernelTransfers.RandomizedRule Ω)).trans
    apply iSup_le
    intro θ
    apply iSup_le
    intro hθ
    rw [← hsame]
    exact le_iSup_of_le θ (le_iSup_of_le hθ le_rfl)

/-- Exact equality of the seed and kernel minimax error-event probabilities. -/
theorem seed_minimaxTail_eq_kernel {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T : Θ → ℝ) (C : Set Θ) (t : ℝ) :
    Applications.minimaxTail (fun θ => (laws θ).prod seedLaw) T C t =
      KernelTransfers.minimaxTail laws T C t := by
  have hl : ∀ a : ℝ, Measurable (fun y : ℝ => if t ≤ |y - a| then (1 : ℝ≥0∞) else 0) := by
    intro a
    have hs : MeasurableSet {y : ℝ | t ≤ |y - a|} :=
      measurableSet_le measurable_const ((measurable_id.sub measurable_const).abs)
    convert (measurable_const (a := (1 : ℝ≥0∞))).indicator hs using 1
    ext y
    by_cases hy : t ≤ |y - a| <;> simp [Set.indicator, hy]
  have heq : seedMinimaxLoss laws T C (fun a y => if t ≤ |y - a| then 1 else 0) =
      Applications.minimaxTail (fun θ => (laws θ).prod seedLaw) T C t := by
    unfold seedMinimaxLoss Applications.minimaxTail
    apply iInf_congr
    intro g
    apply iSup_congr
    intro θ
    apply iSup_congr
    intro _
    have hs : MeasurableSet {x : Ω × ℝ | t ≤ |g.val x - T θ|} :=
      measurableSet_le measurable_const ((g.property.sub measurable_const).abs)
    simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using
      (lintegral_indicator_one (μ := (laws θ).prod seedLaw) hs)
  rw [← heq, seedMinimaxLoss_eq_kernel laws T C _ hl]
  rfl

/-- Exact equality of the seed and kernel minimax RMSE, including infinity. -/
theorem seed_minimaxRMSE_eq_kernel {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T : Θ → ℝ) (C : Set Θ) :
    Applications.minimaxRMSE (fun θ => (laws θ).prod seedLaw) T C =
      KernelTransfers.minimaxRMSE laws T C := by
  unfold Applications.minimaxRMSE KernelTransfers.minimaxRMSE
  congr 1
  exact seedMinimaxLoss_eq_kernel laws T C (fun a y => ENNReal.ofReal ((y - a) ^ 2))
    (fun _ => (measurable_id.sub measurable_const).pow_const 2 |>.ennreal_ofReal)

end RoughRegime.KernelSeedBridge

namespace RoughRegime.Model
open RoughRegime.KernelSeedBridge

theorem minimaxTail_eq_kernel {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) (t : ℝ) :
    minimaxTail n T C t = KernelTransfers.minimaxTail
      (fun P : ProbabilityMeasure Ω => Measure.pi (fun _ : Fin n => (P : Measure Ω))) T C t :=
  seed_minimaxTail_eq_kernel _ T C t

theorem minimaxRMSE_eq_kernel {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) :
    minimaxRMSE n T C = KernelTransfers.minimaxRMSE
      (fun P : ProbabilityMeasure Ω => Measure.pi (fun _ : Fin n => (P : Measure Ω))) T C := by
  rw [minimaxRMSE_eq_squaredRisk]
  exact seed_minimaxRMSE_eq_kernel _ T C

def kernelLaw {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (K : Kernel Ω Ξ) [IsMarkovKernel K] (P : ProbabilityMeasure Ω) : ProbabilityMeasure Ξ :=
  (K ∘ₘ (P : Measure Ω)).toProbabilityMeasure

/-- Literal Lemma 19(c) for the model's measurable uniform-seed estimators. -/
theorem kernel_reduction {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (n : ℕ) (K : Kernel Ω Ξ) [IsMarkovKernel K]
    (T0 : ProbabilityMeasure Ω → ℝ) (T1 : ProbabilityMeasure Ξ → ℝ)
    (C0 : Set (ProbabilityMeasure Ω)) (C1 : Set (ProbabilityMeasure Ξ))
    (hclass : ∀ P ∈ C0, kernelLaw K P ∈ C1)
    (htarget : ∀ P ∈ C0, T1 (kernelLaw K P) = T0 P) (t : ℝ) :
    minimaxTail n T0 C0 t ≤ minimaxTail n T1 C1 t ∧
      minimaxRMSE n T0 C0 ≤ minimaxRMSE n T1 C1 := by
  simpa only [minimaxTail_eq_kernel, minimaxRMSE_eq_kernel] using
    KernelTransfers.iid_kernel_reduction n K
      (fun P : ProbabilityMeasure Ω => (P : Measure Ω))
      (fun Q : ProbabilityMeasure Ξ => (Q : Measure Ξ)) T0 T1 C0 C1 (kernelLaw K)
      hclass (fun _ _ => rfl) htarget t

/-- Kernel transformations preserve hardness on the images of the hard classes. -/
theorem kernel_hardness {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (K : Kernel Ω Ξ) [IsMarkovKernel K]
    (T0 : ProbabilityMeasure Ω → ℝ) (T1 : ProbabilityMeasure Ξ → ℝ)
    (Cn : ℕ → Set (ProbabilityMeasure Ω))
    (htarget : ∀ n P, P ∈ Cn n → T1 (kernelLaw K P) = T0 P)
    (tn : ℕ → ℝ) (H : ℝ≥0∞)
    (hhard : H ≤ Filter.liminf (fun n => minimaxTail n T0 (Cn n) (tn n)) atTop) :
    H ≤ Filter.liminf (fun n => minimaxTail n T1 (kernelLaw K '' Cn n) (tn n)) atTop := by
  simpa only [minimaxTail_eq_kernel] using
    KernelTransfers.iid_kernel_hardness K
      (fun P : ProbabilityMeasure Ω => (P : Measure Ω))
      (fun Q : ProbabilityMeasure Ξ => (Q : Measure Ξ)) T0 T1 Cn (kernelLaw K)
      (fun _ _ _ => rfl) htarget tn H (by simpa only [minimaxTail_eq_kernel] using hhard)

end RoughRegime.Model
