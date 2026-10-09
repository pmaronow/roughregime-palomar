module

public import RoughRegime.Applications


@[expose] public section
/-!
Lemma 19(c) for randomized real-output estimators represented by Markov kernels.
This convention permits arbitrary observation measurable spaces. Equivalence with
`Model`'s single uniform-seed convention is proved in `KernelSeedBridge.lean`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
namespace RoughRegime.KernelTransfers

/-- Independent applications of a fixed observation kernel to a finite sample. -/
def iidKernel {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (n : ℕ) (K : Kernel Ω Ξ) [IsMarkovKernel K] : Kernel (Fin n → Ω) (Fin n → Ξ) where
  toFun x := Measure.pi (fun i => K (x i))
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (generateFrom_pi.symm) isPiSystem_pi
    rintro _ ⟨s, hs, rfl⟩
    simp only [Measure.pi_pi]
    apply Finset.measurable_prod
    intro i _
    exact (K.measurable_coe (hs i (Set.mem_univ i))).comp (measurable_pi_apply i)

@[simp] lemma iidKernel_apply {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (n : ℕ) (K : Kernel Ω Ξ) [IsMarkovKernel K] (x : Fin n → Ω) :
    iidKernel n K x = Measure.pi (fun i => K (x i)) := rfl

instance {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (n : ℕ) (K : Kernel Ω Ξ) [IsMarkovKernel K] : IsMarkovKernel (iidKernel n K) :=
  ⟨fun x => by change IsProbabilityMeasure (Measure.pi (fun i => K (x i))); infer_instance⟩

/-- The output sample has exactly the product law `(KP)^n`. -/
theorem iidKernel_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (n : ℕ) (K : Kernel Ω Ξ) [IsMarkovKernel K]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    (iidKernel n K) ∘ₘ Measure.pi (fun _ : Fin n => P) =
      Measure.pi (fun _ : Fin n => K ∘ₘ P) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.bind_apply (.univ_pi hs) (iidKernel n K).aemeasurable]
  simp only [iidKernel_apply, Measure.pi_pi]
  have hX : iIndepFun (fun i : Fin n => fun x : Fin n → Ω => K (x i) (s i))
      (Measure.pi (fun _ : Fin n => P)) :=
    iIndepFun_pi (fun i => (K.measurable_coe (hs i)).aemeasurable)
  have hmeas : ∀ i : Fin n, Measurable (fun x : Fin n → Ω => K (x i) (s i)) :=
    fun i => (K.measurable_coe (hs i)).comp (measurable_pi_apply i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hX hmeas]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.bind_apply (hs i) K.aemeasurable]
  exact (measurePreserving_eval (fun _ : Fin n => P) i).lintegral_comp
    (K.measurable_coe (hs i))

abbrev RandomizedRule (Ω : Type*) [MeasurableSpace Ω] :=
  {δ : Kernel Ω ℝ // IsMarkovKernel δ}

instance {Ω : Type*} [MeasurableSpace Ω] : Nonempty (RandomizedRule Ω) :=
  ⟨⟨Kernel.deterministic (fun _ => 0) measurable_const, inferInstance⟩⟩

/-- The minimax loss over all randomized real-output rules. -/
def minimaxLoss {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (T : Θ → ℝ) (C : Set Θ) (loss : ℝ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ δ : RandomizedRule Ω, ⨆ θ ∈ C, ∫⁻ y, loss (T θ) y ∂(δ.val ∘ₘ laws θ)

def minimaxTail {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (T : Θ → ℝ) (C : Set Θ) (t : ℝ) : ℝ≥0∞ :=
  minimaxLoss laws T C (fun a y => if t ≤ |y - a| then 1 else 0)

def minimaxMSE {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (T : Θ → ℝ) (C : Set Θ) : ℝ≥0∞ :=
  minimaxLoss laws T C (fun a y => ENNReal.ofReal ((y - a) ^ 2))

def minimaxRMSE {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (T : Θ → ℝ) (C : Set Θ) : ℝ≥0∞ :=
  (minimaxMSE laws T C) ^ (1 / 2 : ℝ)

/-- The tail loss is the actual error-event probability, including its boundary. -/
theorem minimaxTail_eq_probability {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (T : Θ → ℝ) (C : Set Θ) (t : ℝ) :
    minimaxTail laws T C t =
      ⨅ δ : RandomizedRule Ω, ⨆ θ ∈ C, (δ.val ∘ₘ laws θ) {y | t ≤ |y - T θ|} := by
  unfold minimaxTail minimaxLoss
  apply iInf_congr
  intro δ
  apply iSup_congr
  intro θ
  apply iSup_congr
  intro _
  have hs : MeasurableSet {y : ℝ | t ≤ |y - T θ|} :=
    measurableSet_le measurable_const ((measurable_id.sub measurable_const).abs)
  simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using
    (lintegral_indicator_one (μ := δ.val ∘ₘ laws θ) hs)

/-- Extended square roots commute with the risk infimum and supremum. -/
theorem minimaxRMSE_eq_inf_sup {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (T : Θ → ℝ) (C : Set Θ) :
    minimaxRMSE laws T C = ⨅ δ : RandomizedRule Ω, ⨆ θ ∈ C,
      (∫⁻ y, ENNReal.ofReal ((y - T θ) ^ 2) ∂(δ.val ∘ₘ laws θ)) ^ (1 / 2 : ℝ) := by
  unfold minimaxRMSE minimaxMSE minimaxLoss
  change RoughRegime.Applications.halfPowerOrderIso _ = _
  rw [RoughRegime.Applications.halfPowerOrderIso.map_iInf]
  apply iInf_congr
  intro δ
  rw [RoughRegime.Applications.halfPowerOrderIso.map_iSup]
  apply iSup_congr
  intro θ
  rw [RoughRegime.Applications.halfPowerOrderIso.map_iSup]
  rfl

/-- Composing an output rule with a fixed kernel preserves its full output law. -/
theorem transformedRule_output {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (K : Kernel Ω Ξ) (δ : Kernel Ξ ℝ) (P : Measure Ω) :
    (δ ∘ₖ K) ∘ₘ P = δ ∘ₘ (K ∘ₘ P) := Measure.comp_assoc.symm

/-- A law-independent observation kernel transfers every nonnegative loss. -/
theorem kernel_minimax_loss {Ω Ξ Θ Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (K : Kernel Ω Ξ) [IsMarkovKernel K]
    (P : Θ → Measure Ω) (Q : Λ → Measure Ξ)
    (T0 : Θ → ℝ) (T1 : Λ → ℝ) (C0 : Set Θ) (C1 : Set Λ) (φ : Θ → Λ)
    (hclass : ∀ θ ∈ C0, φ θ ∈ C1)
    (hlaw : ∀ θ ∈ C0, Q (φ θ) = K ∘ₘ P θ)
    (htarget : ∀ θ ∈ C0, T1 (φ θ) = T0 θ) (loss : ℝ → ℝ → ℝ≥0∞) :
    minimaxLoss P T0 C0 loss ≤ minimaxLoss Q T1 C1 loss := by
  apply le_iInf
  intro δ
  have : IsMarkovKernel δ.val := δ.property
  let δ0 : RandomizedRule Ω := ⟨δ.val ∘ₖ K, inferInstance⟩
  apply (iInf_le _ δ0).trans
  apply iSup_le
  intro θ
  apply iSup_le
  intro hθ
  change (∫⁻ y, loss (T0 θ) y ∂((δ.val ∘ₖ K) ∘ₘ P θ)) ≤ _
  rw [transformedRule_output, ← hlaw θ hθ, ← htarget θ hθ]
  exact le_iSup_of_le (φ θ) (le_iSup_of_le (hclass θ hθ) le_rfl)

/-- Lemma 19(c): both probability and RMSE bounds for actual independent kernel outputs. -/
theorem iid_kernel_reduction {Ω Ξ Θ Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (n : ℕ) (K : Kernel Ω Ξ) [IsMarkovKernel K]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (Q : Λ → Measure Ξ) [∀ ξ, IsProbabilityMeasure (Q ξ)]
    (T0 : Θ → ℝ) (T1 : Λ → ℝ) (C0 : Set Θ) (C1 : Set Λ) (φ : Θ → Λ)
    (hclass : ∀ θ ∈ C0, φ θ ∈ C1)
    (hlaw : ∀ θ ∈ C0, Q (φ θ) = K ∘ₘ P θ)
    (htarget : ∀ θ ∈ C0, T1 (φ θ) = T0 θ) (t : ℝ) :
    minimaxTail (fun θ => Measure.pi (fun _ : Fin n => P θ)) T0 C0 t ≤
        minimaxTail (fun ξ => Measure.pi (fun _ : Fin n => Q ξ)) T1 C1 t ∧
    minimaxRMSE (fun θ => Measure.pi (fun _ : Fin n => P θ)) T0 C0 ≤
        minimaxRMSE (fun ξ => Measure.pi (fun _ : Fin n => Q ξ)) T1 C1 := by
  have hlaw' : ∀ θ ∈ C0,
      Measure.pi (fun _ : Fin n => Q (φ θ)) =
        iidKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P θ) := by
    intro θ hθ
    rw [iidKernel_law, hlaw θ hθ]
  constructor
  · exact kernel_minimax_loss (iidKernel n K) _ _ T0 T1 C0 C1 φ hclass hlaw'
      htarget (fun a y => if t ≤ |y - a| then 1 else 0)
  · apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact kernel_minimax_loss (iidKernel n K) _ _ T0 T1 C0 C1 φ hclass hlaw'
      htarget (fun a y => ENNReal.ofReal ((y - a) ^ 2))

/-- The final hardness assertion of Lemma 19(c), on the image of each hard class. -/
theorem iid_kernel_hardness {Ω Ξ Θ Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (K : Kernel Ω Ξ) [IsMarkovKernel K]
    (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (Q : Λ → Measure Ξ) [∀ ξ, IsProbabilityMeasure (Q ξ)]
    (T0 : Θ → ℝ) (T1 : Λ → ℝ) (Cn : ℕ → Set Θ) (φ : Θ → Λ)
    (hlaw : ∀ n θ, θ ∈ Cn n → Q (φ θ) = K ∘ₘ P θ)
    (htarget : ∀ n θ, θ ∈ Cn n → T1 (φ θ) = T0 θ)
    (tn : ℕ → ℝ) (H : ℝ≥0∞)
    (hhard : H ≤ Filter.liminf (fun n =>
      minimaxTail (fun θ => Measure.pi (fun _ : Fin n => P θ)) T0 (Cn n) (tn n)) atTop) :
    H ≤ Filter.liminf (fun n =>
      minimaxTail (fun ξ => Measure.pi (fun _ : Fin n => Q ξ)) T1 (φ '' Cn n) (tn n)) atTop := by
  apply hhard.trans
  have hineq : ∀ᶠ n in atTop,
      minimaxTail (fun θ => Measure.pi (fun _ : Fin n => P θ)) T0 (Cn n) (tn n) ≤
      minimaxTail (fun ξ => Measure.pi (fun _ : Fin n => Q ξ)) T1 (φ '' Cn n) (tn n) :=
    Filter.Eventually.of_forall (fun n =>
      (iid_kernel_reduction n K P Q T0 T1 (Cn n) (φ '' Cn n) φ
        (fun θ hθ => Set.mem_image_of_mem φ hθ) (hlaw n) (htarget n) (tn n)).1)
  exact Filter.liminf_le_liminf hineq

end RoughRegime.KernelTransfers
