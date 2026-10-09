module

public import RoughRegime.SignPrior
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd


@[expose] public section
/-! Genuine joint probability measures for the uniform angle and its conditional
paired signs. The identities connect normalized interval integration to these laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace RoughRegime.LatticeFourier

def angleUniform : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi))

instance angleUniform_probability : IsProbabilityMeasure angleUniform := by
  constructor
  simp only [angleUniform, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top

/-- Every scalar expectation under the actual uniform-angle probability law. -/
theorem integral_angleUniform (f : ℝ → ℝ) :
    (∫ θ, f θ ∂angleUniform) = (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) / (2 * Real.pi) := by
  rw [angleUniform, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  ring

/-- The conditional paired-sign laws form an actual measurable Markov kernel. -/
def angularSignKernel (M : ℕ) (positive : Bool) : Kernel ℝ (Bool × Bool) where
  toFun θ := (angularSignLaw M θ positive).toMeasure
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp_rw [PMF.toMeasure_apply _ hs, tsum_fintype]
    apply Finset.measurable_sum
    intro st _
    by_cases hst : st ∈ s
    · simp only [Set.indicator_of_mem hst, angularSignLaw, signLaw_apply,
        RoughRegime.Lower.signWeight]
      fun_prop
    · simp only [Set.indicator_of_notMem hst]
      exact measurable_const

@[simp] theorem angularSignKernel_apply (M : ℕ) (positive : Bool) (θ : ℝ) :
    angularSignKernel M positive θ = (angularSignLaw M θ positive).toMeasure := rfl

instance angularSignKernel_markov (M : ℕ) (positive : Bool) :
    IsMarkovKernel (angularSignKernel M positive) := ⟨fun θ => by
      change IsProbabilityMeasure (angularSignLaw M θ positive).toMeasure
      infer_instance⟩

/-- The paper's actual angular-sign prior, with no conditioning assumed. -/
def angleSignLaw (M : ℕ) (positive : Bool) : Measure (ℝ × (Bool × Bool)) :=
  angleUniform.compProd (angularSignKernel M positive)

instance angleSignLaw_probability (M : ℕ) (positive : Bool) :
    IsProbabilityMeasure (angleSignLaw M positive) := by
  unfold angleSignLaw
  infer_instance

/-- The joint prior expectation is precisely the source's normalized angular average. -/
theorem integral_angleSignLaw (M : ℕ) (positive : Bool)
    (f : ℝ × (Bool × Bool) → ℝ) (hf : Integrable f (angleSignLaw M positive)) :
    (∫ ts, f ts ∂angleSignLaw M positive) =
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ st, f (θ, st) ∂(angularSignLaw M θ positive).toMeasure) / (2 * Real.pi) := by
  rw [angleSignLaw, Measure.integral_compProd hf, integral_angleUniform]
  rfl

end RoughRegime.LatticeFourier
