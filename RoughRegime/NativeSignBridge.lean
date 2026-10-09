module

public import RoughRegime.PoissonPhase
public import RoughRegime.AngularLaw


@[expose] public section
/-! Exact expectation bridges from the paper's Markov-kernel conditional sign
laws to the likelihood-density priors used in the marked-Poisson bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 theorem angleUniform_eq_native : LatticePriors.angleUniform = LatticeFourier.angleUniform := by
  unfold LatticePriors.angleUniform LatticeFourier.angleUniform
  rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi)]

 theorem signLaw_power_mean (c v : ℝ) (hc : |c| ≤ 1) (ku kv : ℕ) :
    (∫ st, Lower.sign st.1 ^ ku * Lower.sign st.2 ^ kv * v
      ∂(LatticeFourier.signLaw c hc).toMeasure) = Lower.signMoment c ku kv * v := by
  rw [PMF.integral_eq_sum]
  simp only [LatticeFourier.signLaw_apply,
    ENNReal.toReal_ofReal (Lower.signWeight_nonneg hc _ _), smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [Lower.signMoment, Lower.signWeight, Lower.sign]
  ring

variable {H : Type*} [MeasurableSpace H] (ν : Measure H) [IsProbabilityMeasure ν]

 theorem native_signed_integral (M ku kv : ℕ) (positive : Bool)
    (f : H × ℝ → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ p, |f p| ≤ B) :
    (∫ q : H × (ℝ × (Bool × Bool)), Lower.sign q.2.2.1 ^ ku *
      Lower.sign q.2.2.2 ^ kv * f (q.1, q.2.1)
      ∂ν.prod (LatticeFourier.angleSignLaw M positive)) =
    ∫ p, Lower.signMoment ((if positive then 1 else -1) * Real.cos ((M : ℝ) * p.2)) ku kv * f p
      ∂ν.prod LatticePriors.angleUniform := by
  let g := fun q : H × (ℝ × (Bool × Bool)) => Lower.sign q.2.2.1 ^ ku *
    Lower.sign q.2.2.2 ^ kv * f (q.1, q.2.1)
  have hs : Measurable Lower.sign := Measurable.of_discrete
  have hg : Measurable g := by fun_prop
  have hgb : ∀ q, |g q| ≤ B := by
    intro q
    dsimp [g]
    rw [abs_mul, abs_mul, sign_power_abs, sign_power_abs, one_mul, one_mul]
    exact hfb _
  have hi : Integrable g (ν.prod (LatticeFourier.angleSignLaw M positive)) :=
    bounded_integrable _ _ hg B hgb
  change (∫ q, g q ∂ν.prod (LatticeFourier.angleSignLaw M positive)) = _
  rw [integral_prod g hi]
  have hinner (h : H) : (∫ q, g (h, q) ∂LatticeFourier.angleSignLaw M positive) =
      ∫ θ, Lower.signMoment ((if positive then 1 else -1) * Real.cos ((M : ℝ) * θ)) ku kv * f (h, θ)
        ∂LatticePriors.angleUniform := by
    have hgi : Integrable (fun q => g (h, q)) (LatticeFourier.angleSignLaw M positive) :=
      bounded_integrable _ _ (hg.comp (measurable_const.prodMk measurable_id)) B (fun q => hgb (h, q))
    rw [LatticeFourier.angleSignLaw, Measure.integral_compProd hgi]
    rw [angleUniform_eq_native]
    apply integral_congr_ae
    filter_upwards with θ
    change (∫ st, Lower.sign st.1 ^ ku * Lower.sign st.2 ^ kv * f (h, θ)
      ∂(LatticeFourier.angularSignLaw M θ positive).toMeasure) = _
    unfold LatticeFourier.angularSignLaw
    exact signLaw_power_mean _ _ _ ku kv
  simp_rw [hinner]
  have hright : Integrable (fun p : H × ℝ =>
      Lower.signMoment ((if positive then 1 else -1) * Real.cos ((M : ℝ) * p.2)) ku kv * f p)
      (ν.prod LatticePriors.angleUniform) := by
    cases positive
    · have hi' := (phaseDensity_signed_integrable ν M ku kv (-1) (by norm_num) f hf B hB hfb).integral_prod_left
      simpa only [uniformSigns_signed_density, Bool.false_eq_true, ite_false] using hi'
    · have hi' := (phaseDensity_signed_integrable ν M ku kv 1 (by norm_num) f hf B hB hfb).integral_prod_left
      simpa only [uniformSigns_signed_density, ite_true] using hi'
  rw [integral_prod _ hright]

 theorem native_signed_eq_phasePrior (M ku kv : ℕ) (positive : Bool)
    (f : H × ℝ → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ p, |f p| ≤ B) :
    (∫ q : H × (ℝ × (Bool × Bool)), Lower.sign q.2.2.1 ^ ku *
      Lower.sign q.2.2.2 ^ kv * f (q.1, q.2.1)
      ∂ν.prod (LatticeFourier.angleSignLaw M positive)) =
    ∫ q : PhaseParameter H, Lower.sign q.2.1 ^ ku * Lower.sign q.2.2 ^ kv * f q.1
      ∂(phasePrior ν M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure := by
  rw [native_signed_integral ν M ku kv positive f hf B hB hfb,
    phasePrior_signed_integral ν M ku kv _ _ f hf B hB hfb]


/-- Equation (5.3) for the actual conditional-sign Markov kernel from A5. -/
 theorem native_signed_difference (M ku kv : ℕ)
    (f : H × ℝ → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ p, |f p| ≤ B) :
    (∫ q : H × (ℝ × (Bool × Bool)), Lower.sign q.2.2.1 ^ ku *
      Lower.sign q.2.2.2 ^ kv * f (q.1, q.2.1)
      ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
    (∫ q : H × (ℝ × (Bool × Bool)), Lower.sign q.2.2.1 ^ ku *
      Lower.sign q.2.2.2 ^ kv * f (q.1, q.2.1)
      ∂ν.prod (LatticeFourier.angleSignLaw M false)) =
    if Odd ku ∧ Odd kv then
      2 * ∫ p, Real.cos ((M : ℝ) * p.2) * f p ∂ν.prod LatticePriors.angleUniform else 0 := by
  rw [native_signed_eq_phasePrior ν M ku kv true f hf B hB hfb,
    native_signed_eq_phasePrior ν M ku kv false f hf B hB hfb]
  exact phasePrior_signed_difference ν M ku kv f hf B hB hfb

end RoughRegime.PoissonMeasure
