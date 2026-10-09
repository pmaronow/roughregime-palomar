module

public import RoughRegime.PoissonProcess


@[expose] public section
/-! Measurable spatial transformations of the actual ordered count-and-mark
Poisson configurations, retaining the count and every observation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Apply the same deterministic mark transformation to every observation. -/
def pointMap (f : X → Y) (z : PointConfiguration X) : PointConfiguration Y :=
  ⟨z.1,fun k => f (z.2 k)⟩

theorem measurable_pointMap (f : X → Y) (hf : Measurable f) :
    Measurable (pointMap f) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun xs : Fin n → X => (⟨n,fun k => f (xs k)⟩ : PointConfiguration Y)) ⁻¹' s)
  exact ((measurable_point_mk n).comp
    (Measurable.of_eval (fun k => hf.comp (measurable_pi_apply k)))) hs

/-- Deterministically mapping each mark gives the Poisson process of the
mapped mark law, with exactly the original intensity. -/
theorem referenceProcess_map (P : Measure X) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (f : X → Y) (hf : Measurable f) :
    (referenceProcess P rate).map (pointMap f) = referenceProcess (P.map f) rate := by
  rw [referenceProcess,referenceProcess,
    Measure.map_sum (measurable_pointMap f hf).aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul _ (measurable_pointMap f hf).aemeasurable,
    Measure.map_map (measurable_pointMap f hf) (measurable_point_mk n)]
  have hpi : (Measure.pi (fun _ : Fin n => P)).map (fun xs k => f (xs k)) =
      Measure.pi (fun _ : Fin n => P.map f) :=
    Measure.pi_map_pi (fun _ => hf.aemeasurable)
  have hm : Measurable (fun xs : Fin n → X => fun k : Fin n => f (xs k)) :=
    Measurable.of_eval (fun k => hf.comp (measurable_pi_apply k))
  rw [← hpi,Measure.map_map (measurable_point_mk n) hm]
  rfl

/-- Map each component's marks through its own fixed spatial transform. -/
def componentPointMap {ι : Type*} (f : ι → X → Y)
    (z : ι → PointConfiguration X) : ι → PointConfiguration Y :=
  fun i => pointMap (f i) (z i)

theorem measurable_componentPointMap {ι : Type*} (f : ι → X → Y)
    (hf : ∀ i, Measurable (f i)) : Measurable (componentPointMap f) :=
  Measurable.of_eval (fun i => (measurable_pointMap (f i) (hf i)).comp (measurable_pi_apply i))

/-- The actual independent component process law is preserved under its
fixed componentwise spatial transformations. -/
theorem referenceProcess_product_map {ι : Type*} [Fintype ι]
    (P : ι → Measure X) [∀ i, IsProbabilityMeasure (P i)] (rate : ι → ℝ≥0)
    (f : ι → X → Y) (hf : ∀ i, Measurable (f i)) :
    (Measure.pi (fun i => referenceProcess (P i) (rate i))).map (componentPointMap f) =
      Measure.pi (fun i => referenceProcess ((P i).map (f i)) (rate i)) := by
  unfold componentPointMap
  rw [Measure.pi_map_pi
    (fun i => (measurable_pointMap (f i) (hf i)).aemeasurable)]
  congr 1
  funext i
  exact referenceProcess_map (P i) (rate i) (f i) (hf i)

end RoughRegime.PoissonMeasure
