module

public import RoughRegime.UpperDegreeRules


@[expose] public section
/-! Numerical risk envelopes resulting from the paper's degree rules. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.UpperRates

lemma sqrt_rpow (L s : ℝ) (hL : 0 ≤ L) : Real.sqrt L ^ s = L ^ (s / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL]
  congr 1
  ring

lemma sqrt_nat_pow (L : ℝ) (ν : ℕ) (hL : 0 ≤ L) : Real.sqrt L ^ ν = L ^ ((ν : ℝ) / 2) := by
  rw [← Real.rpow_natCast, sqrt_rpow L ν hL]

lemma window_constant_degree_envelope (θ CX Xbar L : ℝ)
    (hθ : 0 < θ) (hCX : 0 ≤ CX) (hL : 1 ≤ L) (hX : Xbar ≤ CX * Real.sqrt L) :
    2 + Real.sqrt (Real.pi * Xbar / θ) / Real.log 2 ≤
      (2 + Real.sqrt (Real.pi * CX / θ) / Real.log 2) * L ^ (1 / 4 : ℝ) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hquarter : 1 ≤ L ^ (1 / 4 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hroot : Real.sqrt (Real.pi * Xbar / θ) ≤ Real.sqrt (Real.pi * CX / θ) * L ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ Real.sqrt (Real.pi * (CX * Real.sqrt L) / θ) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX Real.pi_pos.le) hθ.le)
      _ = Real.sqrt (Real.pi * CX / θ) * L ^ (1 / 4 : ℝ) := by
        have heq : Real.pi * (CX * Real.sqrt L) / θ = (Real.pi * CX / θ) * Real.sqrt L := by ring
        rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (Real.sqrt L), sqrt_rpow L (1 / 2) (by linarith)]
        norm_num
  have hdiv := div_le_div_of_nonneg_right hroot hlog.le
  calc
    _ ≤ 2 + Real.sqrt (Real.pi * CX / θ) * L ^ (1 / 4 : ℝ) / Real.log 2 := add_le_add le_rfl hdiv
    _ ≤ 2 * L ^ (1 / 4 : ℝ) + Real.sqrt (Real.pi * CX / θ) * L ^ (1 / 4 : ℝ) / Real.log 2 := by linarith
    _ = _ := by ring

lemma degree_envelope_powers (Cv CR Rbar L θ : ℝ) (ν : ℕ)
    (hCv : 0 ≤ Cv) (hCR : 0 ≤ CR) (hR : 0 ≤ Rbar) (hL : 0 ≤ L) (hθ : 0 ≤ θ)
    (henv : Rbar ≤ CR * Real.sqrt L) :
    (Cv * Rbar) ^ θ * Rbar ^ ν ≤
      (Cv * CR) ^ θ * CR ^ ν * L ^ (θ / 2 + (ν : ℝ) / 2) := by
  have hθpow : (Cv * Rbar) ^ θ ≤ (Cv * CR) ^ θ * L ^ (θ / 2) := by
    calc
      _ ≤ (Cv * (CR * Real.sqrt L)) ^ θ :=
        Real.rpow_le_rpow (mul_nonneg hCv hR) (mul_le_mul_of_nonneg_left henv hCv) hθ
      _ = _ := by rw [← mul_assoc, Real.mul_rpow (by positivity) (Real.sqrt_nonneg L), sqrt_rpow L θ hL]
  have hνpow : Rbar ^ ν ≤ CR ^ ν * L ^ ((ν : ℝ) / 2) := by
    calc
      _ ≤ (CR * Real.sqrt L) ^ ν := pow_le_pow_left₀ hR henv _
      _ = _ := by rw [mul_pow, sqrt_nat_pow L ν hL]
  calc
    _ ≤ ((Cv * CR) ^ θ * L ^ (θ / 2)) * (CR ^ ν * L ^ ((ν : ℝ) / 2)) :=
      mul_le_mul hθpow hνpow (by positivity) (by positivity)
    _ = _ := by
      by_cases hL0 : L = 0
      · subst L
        rw [Real.rpow_add_of_nonneg (by norm_num) (by positivity) (by positivity)]
        ring
      · rw [Real.rpow_add (lt_of_le_of_ne hL (Ne.symm hL0))]
        ring

/-- The explicit constant multiplying the subcritical upper-bound scale. -/
def cappedBiasConstant (Cv CR CX θ τ : ℝ) (ν : ℕ) : ℝ :=
  (Cv * CR) ^ θ * CR ^ ν * Real.exp (τ * (ν + 3)) *
    (2 + Real.sqrt (Real.pi * CX / θ) / Real.log 2) * Real.exp (8 * θ * τ)

/-- The actual variance-rule bias sum has the source logarithmic power
`θ/2 + ν/2 + 1/4`. Its input envelopes are degree and window-radius bounds. -/
theorem cappedDegree_subcritical_bound (S : Finset ℝ)
    (n Cv CR CX Rbar Xbar θ τ L : ℝ) (ν : ℕ)
    (hn : 0 < n) (hCv : 0 < Cv) (hCR : 0 ≤ CR) (hCX : 0 ≤ CX) (hRbar : 0 < Rbar)
    (hXbar : 0 < Xbar) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hL : 1 ≤ L)
    (hRenv : Rbar ≤ CR * Real.sqrt L) (hXenv : Xbar ≤ CX * Real.sqrt L)
    (hB : 0 < (1 - 2 * θ) * L - 2 * RoughRegime.Rates.kappa θ τ * Real.sqrt L)
    (hS : ∀ x ∈ S, 0 < x ∧ x ≤ Xbar)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.log 2 ≤ |x - y|)
    (hlarge : ∀ x ∈ S, (ν : ℝ) + 3 ≤
      ((1 - 2 * θ) * L - 2 * RoughRegime.Rates.kappa θ τ * Real.sqrt L) / x)
    (hdegree : ∀ x ∈ S,
      (RoughRegime.UpperDegreeRules.cappedDegree
        ((1 - 2 * θ) * L - 2 * RoughRegime.Rates.kappa θ τ * Real.sqrt L) x ν : ℝ) + 1 ≤ Rbar) :
    (∑ x ∈ S, RoughRegime.UpperDegreeRules.approximationWeight
      (n * Real.exp x / (Cv * Rbar)) θ τ ν
      (RoughRegime.UpperDegreeRules.cappedDegree
        ((1 - 2 * θ) * L - 2 * RoughRegime.Rates.kappa θ τ * Real.sqrt L) x ν)) ≤
      cappedBiasConstant Cv CR CX θ τ ν * n ^ (-θ) *
        L ^ (θ / 2 + (ν : ℝ) / 2 + 1 / 4) *
          Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt L) := by
  let B := (1 - 2 * θ) * L - 2 * RoughRegime.Rates.kappa θ τ * Real.sqrt L
  let W := 2 + Real.sqrt (Real.pi * Xbar / θ) / Real.log 2
  let W0 := 2 + Real.sqrt (Real.pi * CX / θ) / Real.log 2
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hW0 : 0 ≤ W0 := by dsimp [W0]; positivity
  have hraw := RoughRegime.UpperDegreeRules.cappedDegree_window_sum_bound S n (Cv * Rbar) Rbar θ τ B Xbar ν
    hn (mul_pos hCv hRbar) hRbar.le hθ hτ hB hXbar hS hsep hlarge hdegree
  have hpowers := degree_envelope_powers Cv CR Rbar L θ ν hCv.le hCR hRbar.le (by linarith) hθ.le hRenv
  have hwindows := window_constant_degree_envelope θ CX Xbar L hθ hCX hL hXenv
  have hexp := RoughRegime.UpperDegreeRules.window_exponential_correction θ τ (1 - 2 * θ) L
    hθ hτ (by linarith) (by linarith) hB.le
  have hκ : 2 * Real.sqrt (θ * (1 - 2 * θ) * τ) = RoughRegime.Rates.kappa θ τ := rfl
  rw [hκ] at hexp
  change Real.exp (-2 * Real.sqrt (θ * τ * B)) ≤
    Real.exp (8 * θ * τ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt L) at hexp
  calc
    _ ≤ n ^ (-θ) * ((Cv * Rbar) ^ θ * Rbar ^ ν) * Real.exp (τ * (ν + 3)) *
        W * Real.exp (-2 * Real.sqrt (θ * τ * B)) := by simpa only [B, W, mul_assoc] using hraw
    _ ≤ n ^ (-θ) * ((Cv * CR) ^ θ * CR ^ ν * L ^ (θ / 2 + (ν : ℝ) / 2)) *
        Real.exp (τ * (ν + 3)) * (W0 * L ^ (1 / 4 : ℝ)) *
        (Real.exp (8 * θ * τ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt L)) := by
      apply mul_le_mul _ hexp (by positivity) (by positivity)
      apply mul_le_mul _ hwindows hW (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpowers (by positivity)
    _ = _ := by
      unfold cappedBiasConstant
      dsimp [W0]
      simp only [Real.rpow_add (by linarith : 0 < L)]
      ring

end RoughRegime.UpperRates
