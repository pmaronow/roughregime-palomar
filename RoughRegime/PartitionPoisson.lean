module

public import RoughRegime.PoissonSuperposition
public import Mathlib.Probability.ConditionalProbability


@[expose] public section
/-! Genuine conditional component mark laws and finite-partition Poisson
superposition, including components of zero probability. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators NNReal ENNReal
namespace RoughRegime.PartitionPoisson
set_option backward.isDefEq.respectTransparency false
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]

def componentMass (P : ProbabilityMeasure X) (s : Set X) : ℝ≥0 :=
  ((P : Measure X) s).toNNReal

theorem componentMass_coe (P : ProbabilityMeasure X) (s : Set X) :
    (componentMass P s : ℝ≥0∞) = (P : Measure X) s :=
  ENNReal.coe_toNNReal (measure_ne_top _ _)

def componentLaw (P : ProbabilityMeasure X) (s : Set X) : ProbabilityMeasure X := by
  classical
  exact if h : (P : Measure X) s = 0 then P else
    ⟨ProbabilityTheory.cond (P : Measure X) s, cond_isProbabilityMeasure h⟩

theorem componentMass_smul_componentLaw (P : ProbabilityMeasure X) (s : Set X) :
    (componentMass P s : ℝ≥0∞) • (componentLaw P s : Measure X) = (P : Measure X).restrict s := by
  classical
  change (componentMass P s : ℝ≥0∞) • (componentLaw P s : Measure X) = _
  rw [componentMass_coe]
  by_cases h : (P : Measure X) s = 0
  · simp only [componentLaw, dite_eq_left h, h, zero_smul, Measure.restrict_eq_zero.mpr h]
  · simp only [componentLaw, dite_eq_right h, ProbabilityMeasure.coe_mk, ProbabilityTheory.cond, smul_smul]
    rw [ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

theorem partition_restriction_sum (P : ProbabilityMeasure X) (s : ι → Set X)
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : (⋃ i, s i) = univ) :
    (∑ i, (P : Measure X).restrict (s i)) = (P : Measure X) := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd hm, hc, Measure.restrict_univ]

theorem componentMass_sum (P : ProbabilityMeasure X) (s : ι → Set X)
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : (⋃ i, s i) = univ) : (∑ i, componentMass P (s i)) = 1 := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_finset_sum, ENNReal.coe_one]
  simp_rw [componentMass_coe]
  have h := congrArg (fun μ : Measure X => μ univ) (partition_restriction_sum P s hm hd hc)
  simpa only [Measure.finsetSum_apply, MeasurableSet.univ, Measure.restrict_apply_univ,
    measure_univ] using h

theorem component_markMixture (P : ProbabilityMeasure X) (s : ι → Set X)
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : (⋃ i, s i) = univ) :
    PoissonSuperposition.markMixture (fun i => componentMass P (s i))
      (fun i => (componentLaw P (s i) : Measure X)) = (P : Measure X) := by
  unfold PoissonSuperposition.markMixture
  simp_rw [componentMass_smul_componentLaw]
  exact partition_restriction_sum P s hm hd hc

theorem partition_superposition (P : ProbabilityMeasure X) (s : ι → Set X)
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hc : (⋃ i, s i) = univ) (rate : ℝ≥0) (hr : 0 < rate) :
    PoissonSuperposition.superpositionKernel ∘ₘ
      Measure.pi (fun i => PoissonMeasure.referenceProcess
        (componentLaw P (s i) : Measure X) (rate * componentMass P (s i))) =
      PoissonMeasure.referenceProcess (P : Measure X) rate := by
  classical
  have hs : (∑ i, rate * componentMass P (s i)) = rate := by
    rw [← Finset.mul_sum, componentMass_sum P s hm hd hc, mul_one]
  rw [PoissonSuperposition.superpositionKernel_comp _ _ (hs.symm ▸ hr), hs]
  have hw : PoissonSuperposition.rateWeights (fun i => rate * componentMass P (s i)) =
      fun i => componentMass P (s i) := by
    funext i
    unfold PoissonSuperposition.rateWeights
    rw [hs, mul_div_cancel_left₀ _ hr.ne']
  rw [hw, component_markMixture P s hm hd hc]

end RoughRegime.PartitionPoisson
