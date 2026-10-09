module

public import RoughRegime.OutsideAugmentation


@[expose] public section
/-! Actual finite independent pair processes, fixed spatial placements and
an independent fixed outside process reconstruct a normalized global marked
Poisson observation through one parameter-independent Markov kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {ι W X Y : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] [MeasurableSpace Y]

 def placementComponent (outside : ProbabilityMeasure Y) (P : ι→ProbabilityMeasure X)
    (f : ι→X→Y) (_hf : ∀ i,Measurable (f i)) : Option ι→ProbabilityMeasure Y
  | none=>outside
  | some i=>ProbabilityMeasure.map (P i) (f i)
 def placementObservation (w : Option ι→ℝ≥0) (hw : ∑ i,w i=1)
    (outside : ProbabilityMeasure Y) (P : ι→ProbabilityMeasure X)
    (f : ι→X→Y) (hf : ∀ i,Measurable (f i)) : ProbabilityMeasure Y :=
  ⟨PoissonSuperposition.markMixture w (fun i=>(placementComponent outside P f hf i:Measure Y)),
    PoissonSuperposition.markMixture_probability w _ hw⟩
 def placementPairProcess (w : Option ι→ℝ≥0) (P : ι→ProbabilityMeasure X) (rate : ℝ≥0) :
    Measure (ι→PointConfiguration X) :=
  Measure.pi (fun i=>referenceProcess (P i:Measure X) (rate*w (some i)))
 instance placementPairProcess_probability (w : Option ι→ℝ≥0) (P : ι→ProbabilityMeasure X) (rate : ℝ≥0) :
    IsProbabilityMeasure (placementPairProcess w P rate) := by unfold placementPairProcess;infer_instance
 def placementKernel (w : Option ι→ℝ≥0) (outside : ProbabilityMeasure Y)
    (f : ι→X→Y) (hf : ∀ i,Measurable (f i)) (rate : ℝ≥0) :
    Kernel (ι→PointConfiguration X) (PointConfiguration Y) :=
  PoissonSuperposition.superpositionKernel ∘ₖ
    (outsideAugmentationKernel (referenceProcess (outside:Measure Y) (rate*w none)) ∘ₖ
      Kernel.deterministic (componentPointMap f) (measurable_componentPointMap f hf))
 instance placementKernel_markov (w : Option ι→ℝ≥0) (outside : ProbabilityMeasure Y)
    (f : ι→X→Y) (hf : ∀ i,Measurable (f i)) (rate : ℝ≥0) :
    IsMarkovKernel (placementKernel w outside f hf rate) := by unfold placementKernel;infer_instance

 theorem placementKernel_law (w : Option ι→ℝ≥0) (hw : ∑ i,w i=1)
    (outside : ProbabilityMeasure Y) (P : ι→ProbabilityMeasure X)
    (f : ι→X→Y) (hf : ∀ i,Measurable (f i)) (rate : ℝ≥0) (hr : 0<rate) :
    placementKernel w outside f hf rate ∘ₘ placementPairProcess w P rate=
      referenceProcess (placementObservation w hw outside P f hf:Measure Y) rate := by
  unfold placementKernel
  rw [← Measure.comp_assoc,← Measure.comp_assoc,Measure.deterministic_comp_eq_map]
  rw [placementPairProcess,referenceProcess_product_map _ _ _ hf]
  let Q:=placementComponent outside P f hf
  have he : Measure.pi (fun i=>referenceProcess ((P i:Measure X).map (f i)) (rate*w (some i)))=
      Measure.pi (fun i=>referenceProcess (Q (some i):Measure Y) (rate*w (some i))) := by
    rfl
  rw [he]
  change PoissonSuperposition.superpositionKernel ∘ₘ
    (outsideAugmentationKernel (referenceProcess (Q none:Measure Y) (rate*w none)) ∘ₘ
      Measure.pi (fun i=>referenceProcess (Q (some i):Measure Y) (rate*w (some i))))=_
  rw [outsideAugmentationKernel_law (fun i=>referenceProcess (Q i:Measure Y) (rate*w i))]
  have hsum : ∑ i,rate*w i=rate:=by rw [← Finset.mul_sum,hw,mul_one]
  rw [PoissonSuperposition.superpositionKernel_comp _ _ (hsum.symm ▸ hr),hsum]
  have hweights : PoissonSuperposition.rateWeights (fun i=>rate*w i)=w := by
    funext i;unfold PoissonSuperposition.rateWeights
    rw [hsum,mul_div_cancel_left₀ _ hr.ne']
  rw [hweights];rfl

 omit [DecidableEq ι] in
 theorem placementObservation_integral (w : Option ι→ℝ≥0) (hw : ∑ i,w i=1)
    (outside : ProbabilityMeasure Y) (P : ι→ProbabilityMeasure X)
    (f : ι→X→Y) (hf : ∀ i,Measurable (f i)) (g : Y→ℝ) (hg : Measurable g)
    (houtside : Integrable g (outside:Measure Y))
    (hpair : ∀ i,Integrable (fun x=>g (f i x)) (P i:Measure X)) :
    (∫ y,g y ∂(placementObservation w hw outside P f hf:Measure Y))=
      (w none:ℝ)*(∫ y,g y ∂(outside:Measure Y))+
        ∑ i,(w (some i):ℝ)*(∫ x,g (f i x) ∂(P i:Measure X)) := by
  have hi : ∀ i,Integrable g (placementComponent outside P f hf i:Measure Y) := by
    intro i
    cases i with
    | none=>exact houtside
    | some i=>exact (integrable_map_measure hg.aestronglyMeasurable (hf i).aemeasurable).2 (hpair i)
  change (∫ y,g y ∂∑ i,(w i:ℝ≥0∞) • (placementComponent outside P f hf i:Measure Y))=_
  rw [integral_finsetSum_measure (fun i _=>(hi i).smul_measure (by finiteness))]
  simp only [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul,Fintype.sum_option]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact integral_map (hf i).aemeasurable hg.aestronglyMeasurable

/-- The kernel is fixed before all latent pair realizations. -/
 theorem placementKernel_all_parameters (w : Option ι→ℝ≥0) (hw : ∑ i,w i=1)
    (outside : ProbabilityMeasure Y) (P : ι→W→ProbabilityMeasure X)
    (f : ι→X→Y) (hf : ∀ i,Measurable (f i)) (rate : ℝ≥0) (hr : 0<rate) :
    ∃ K : Kernel (ι→PointConfiguration X) (PointConfiguration Y),IsMarkovKernel K ∧
      ∀ q : ι→W,K ∘ₘ placementPairProcess w (fun i=>P i (q i)) rate=
        referenceProcess (placementObservation w hw outside (fun i=>P i (q i)) f hf:Measure Y) rate :=
  ⟨placementKernel w outside f hf rate,inferInstance,fun q=>placementKernel_law w hw outside (fun i=>P i (q i)) f hf rate hr⟩

end RoughRegime.PoissonMeasure
