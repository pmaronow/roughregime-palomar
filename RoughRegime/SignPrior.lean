module

public import RoughRegime.Lower
public import RoughRegime.AngularReciprocal


@[expose] public section
/-! The actual paired sign probability laws in the lattice construction. -/
noncomputable section
open MeasureTheory
open RoughRegime.Lower
open scoped ENNReal

namespace RoughRegime.LatticeFourier

/-- The signs have exactly the source masses (1+sigma*tau*c)/4. -/
def signLaw (c : ℝ) (hc : |c| ≤ 1) : PMF (Bool × Bool) :=
  ⟨fun st => ENNReal.ofReal (signWeight c st.1 st.2),
    ENNReal.summable.hasSum_iff.2 (by
      rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
        (fun st _ => signWeight_nonneg hc st.1 st.2)]
      have hs : (∑ st : Bool × Bool, signWeight c st.1 st.2) = 1 := by
        rw [Fintype.sum_prod_type]
        exact signWeight_sum c
      rw [hs, ENNReal.ofReal_one])⟩

@[simp] theorem signLaw_apply (c : ℝ) (hc : |c| ≤ 1) (st : Bool × Bool) :
    signLaw c hc st = ENNReal.ofReal (signWeight c st.1 st.2) := rfl

/-- Exact conditional product-sign mean, also after multiplying any scalar target. -/
theorem signLaw_product_mean (c v : ℝ) (hc : |c| ≤ 1) :
    (∫ st, sign st.1 * sign st.2 * v ∂(signLaw c hc).toMeasure) = c * v := by
  rw [PMF.integral_eq_sum]
  simp only [signLaw_apply, ENNReal.toReal_ofReal (signWeight_nonneg hc _ _), smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [signWeight, sign]
  ring

/-- Difference of the two genuine sign-law expectations is exactly2cv. -/
theorem signLaw_difference (c v : ℝ) (hc : |c| ≤ 1) :
    (∫ st, sign st.1 * sign st.2 * v ∂(signLaw c hc).toMeasure) -
      (∫ st, sign st.1 * sign st.2 * v
        ∂(signLaw (-c) (by simpa only [abs_neg] using hc)).toMeasure) = 2 * c * v := by
  rw [signLaw_product_mean, signLaw_product_mean]
  ring

/-- The source angular sign law is defined at every angle. -/
def angularSignLaw (M : ℕ) (θ : ℝ) (positive : Bool) : PMF (Bool × Bool) :=
  signLaw ((if positive then 1 else -1) * Real.cos ((M : ℝ) * θ)) (by
    cases positive <;> simpa using Real.abs_cos_le_one ((M : ℝ) * θ))

/-- Both sign priors combined with the actual angular reciprocal coefficient. -/
theorem angular_sign_reciprocal_difference (lo hi φ v : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (M b : ℕ) (hM : 0 < M) (heven : Even M) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      ((∫ st, sign st.1 * sign st.2 * v /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + φ + (b : ℝ) * Real.pi)) ∂(angularSignLaw M θ true).toMeasure) -
        (∫ st, sign st.1 * sign st.2 * v /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + φ + (b : ℝ) * Real.pi)) ∂(angularSignLaw M θ false).toMeasure))) /
      (2 * Real.pi) =
        2 * v * RoughRegime.Upper.intervalRho lo hi ^ M * Real.cos ((M : ℝ) * φ) /
          RoughRegime.Upper.intervalGeometricMean lo hi := by
  have he (θ : ℝ) :
      ((∫ st, sign st.1 * sign st.2 * v /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + φ + (b : ℝ) * Real.pi)) ∂(angularSignLaw M θ true).toMeasure) -
        (∫ st, sign st.1 * sign st.2 * v /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + φ + (b : ℝ) * Real.pi)) ∂(angularSignLaw M θ false).toMeasure)) =
        2 * v * (Real.cos ((M : ℝ) * θ) /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + φ + (b : ℝ) * Real.pi))) := by
    have hv : (fun st : Bool × Bool => sign st.1 * sign st.2 * v /
        (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
          Real.cos (θ + φ + (b : ℝ) * Real.pi))) =
        (fun st => sign st.1 * sign st.2 * (v /
          (RoughRegime.Upper.intervalCenter lo hi + RoughRegime.Upper.intervalHalfWidth lo hi *
            Real.cos (θ + φ + (b : ℝ) * Real.pi)))) := by funext st; ring
    rw [hv]
    simp only [angularSignLaw, Bool.false_eq_true, ite_false, ite_true, neg_one_mul, one_mul,
      signLaw_product_mean]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have h := angular_reciprocal_coefficient_even_offset lo hi φ hlo hlt M b hM heven
  calc
    _ = 2 * v * ((∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((M : ℝ) * θ) / (RoughRegime.Upper.intervalCenter lo hi +
        RoughRegime.Upper.intervalHalfWidth lo hi * Real.cos (θ + φ + (b : ℝ) * Real.pi))) /
          (2 * Real.pi)) := by ring
    _ = _ := by rw [h]; ring

end RoughRegime.LatticeFourier
