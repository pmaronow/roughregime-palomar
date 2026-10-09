module

public import RoughRegime.KernelTransfers


@[expose] public section
/-! Independent, nonidentical observation kernels under actual independent
parameter priors. This is the product-mixture identity used by the pair priors. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.KernelTransfers
variable {ι W Ω : Type*} [Fintype ι] [MeasurableSpace W] [MeasurableSpace Ω]

def productKernel (K : ι → Kernel W Ω) [∀ i, IsMarkovKernel (K i)] :
    Kernel (ι → W) (ι → Ω) where
  toFun x := Measure.pi (fun i => K i (x i))
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (generateFrom_pi.symm) isPiSystem_pi
    rintro _ ⟨s, hs, rfl⟩
    simp only [Measure.pi_pi]
    apply Finset.measurable_prod
    intro i _
    exact ((K i).measurable_coe (hs i (Set.mem_univ i))).comp (measurable_pi_apply i)

@[simp] theorem productKernel_apply (K : ι → Kernel W Ω) [∀ i, IsMarkovKernel (K i)]
    (x : ι → W) : productKernel K x = Measure.pi (fun i => K i (x i)) := rfl

instance productKernel_markov (K : ι → Kernel W Ω) [∀ i, IsMarkovKernel (K i)] :
    IsMarkovKernel (productKernel K) :=
  ⟨fun x => by change IsProbabilityMeasure (Measure.pi (fun i => K i (x i))); infer_instance⟩

theorem productKernel_law (K : ι → Kernel W Ω) [∀ i, IsMarkovKernel (K i)]
    (prior : ι → Measure W) [∀ i, IsProbabilityMeasure (prior i)] :
    productKernel K ∘ₘ Measure.pi prior = Measure.pi (fun i => K i ∘ₘ prior i) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.bind_apply (.univ_pi hs) (productKernel K).aemeasurable]
  simp only [productKernel_apply, Measure.pi_pi]
  have hX : iIndepFun (fun i : ι => fun x : ι → W => K i (x i) (s i))
      (Measure.pi prior) :=
    iIndepFun_pi (fun i => ((K i).measurable_coe (hs i)).aemeasurable)
  have hmeas : ∀ i : ι, Measurable (fun x : ι → W => K i (x i) (s i)) :=
    fun i => ((K i).measurable_coe (hs i)).comp (measurable_pi_apply i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hX hmeas]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.bind_apply (hs i) (K i).aemeasurable]
  exact (measurePreserving_eval prior i).lintegral_comp ((K i).measurable_coe (hs i))

/-- The actual observation marginal under independent parameter priors is the
product of the actual single-pair observation marginals. -/
theorem productKernel_marginal (K : ι → Kernel W Ω) [∀ i, IsMarkovKernel (K i)]
    (prior : ι → Measure W) [∀ i, IsProbabilityMeasure (prior i)] :
    (Measure.pi prior ⊗ₘ productKernel K).snd =
      Measure.pi (fun i => (prior i ⊗ₘ K i).snd) := by
  simp only [Measure.snd_compProd]
  exact productKernel_law K prior

/-- Independent mixtures can be identified with proved single-pair density
mixtures, without assuming independence of the full observation marginal. -/
theorem productKernel_marginal_eq (K : ι → Kernel W Ω) [∀ i, IsMarkovKernel (K i)]
    (prior : ι → Measure W) [∀ i, IsProbabilityMeasure (prior i)]
    (mixture : ι → Measure Ω)
    (hmix : ∀ i, (prior i ⊗ₘ K i).snd = mixture i) :
    (Measure.pi prior ⊗ₘ productKernel K).snd = Measure.pi mixture := by
  rw [productKernel_marginal]
  congr 1
  exact funext hmix

end RoughRegime.KernelTransfers
