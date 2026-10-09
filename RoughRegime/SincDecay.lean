module

public import RoughRegime.Lattice
public import Mathlib


@[expose] public section
noncomputable section
open MeasureTheory Filter Asymptotics

namespace RoughRegime.LatticeFourier

/-- The scaled even sinc power used in the gated lattice density. -/
def scaledSincPower (Q : ℕ) (η : ℝ) (x : ℝ) : ℂ :=
  ((Real.sinc (x / η) ^ (2 * Q) : ℝ) : ℂ)

theorem scaledSincPower_continuous (Q : ℕ) (η : ℝ) :
    Continuous (scaledSincPower Q η) := by
  unfold scaledSincPower
  fun_prop

theorem scaledSincPower_norm (Q : ℕ) (η x : ℝ) :
    ‖scaledSincPower Q η x‖ = RoughRegime.Lattice.gate Q η x := by
  rw [scaledSincPower, Complex.norm_real, Real.norm_eq_abs]
  change |RoughRegime.Lattice.gate Q η x| = RoughRegime.Lattice.gate Q η x
  exact abs_of_nonneg (RoughRegime.Lattice.gate_nonneg Q η x)

/-- A globally integrable quadratic envelope, including the origin. -/
theorem scaledSincPower_norm_le (Q : ℕ) (η x : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    ‖scaledSincPower Q η x‖ ≤ (1 + η ^ 2) * (1 + x ^ 2)⁻¹ := by
  have hpow := RoughRegime.Lattice.gate_weighted_power Q 2 (by omega) η x hη
  have hgate := RoughRegime.Lattice.gate_le_one Q η x
  rw [sq_abs] at hpow
  rw [scaledSincPower_norm]
  apply (le_div_iff₀ (show 0 < 1 + x ^ 2 by positivity)).2
  nlinarith

theorem scaledSincPower_integrable (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    Integrable (scaledSincPower Q η) := by
  apply (integrable_inv_one_add_sq.const_mul (1 + η ^ 2)).mono'
    (scaledSincPower_continuous Q η).aestronglyMeasurable
  filter_upwards [] with x
  exact scaledSincPower_norm_le Q η x hQ hη

/-- Quadratic decay at infinity; the constant is exactly the square of the scale. -/
theorem scaledSincPower_isBigO (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    IsBigO (cocompact ℝ) (scaledSincPower Q η) (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  apply IsBigO.of_bound (η ^ 2)
  have he : ∀ᶠ x : ℝ in cocompact ℝ, x ≠ 0 := by
    simpa using (isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact
  filter_upwards [he] with x hx
  rw [Real.rpow_neg (abs_nonneg x), Real.rpow_two,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),
    scaledSincPower_norm]
  apply (le_div_iff₀ (show 0 < |x| ^ 2 by positivity)).2
  exact RoughRegime.Lattice.gate_weighted_power Q 2 (by omega) η x hη

/-- The corresponding real sinc power is integrable. -/
theorem scaledSincPower_real_integrable (Q : ℕ) (η : ℝ)
    (hQ : 1 ≤ Q) (hη : 0 < η) :
    Integrable (fun x : ℝ => Real.sinc (x / η) ^ (2 * Q)) := by
  have h := (scaledSincPower_integrable Q η hQ hη).re
  change Integrable (fun x => (scaledSincPower Q η x).re) at h
  simpa only [scaledSincPower, Complex.ofReal_re] using h

/-- The paper's normalizing constant exists as an integrable real integral. -/
theorem sinc_even_power_integrable (Q : ℕ) (hQ : 1 ≤ Q) :
    Integrable (fun x : ℝ => Real.sinc x ^ (2 * Q)) := by
  simpa using scaledSincPower_real_integrable Q 1 hQ (by norm_num)

/-- The normalizing constant c_Q is strictly positive. -/
theorem integral_sinc_even_power_pos (Q : ℕ) (hQ : 1 ≤ Q) :
    0 < ∫ x : ℝ, Real.sinc x ^ (2 * Q) := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := (0 : ℝ))
    (by fun_prop) (sinc_even_power_integrable Q hQ)
  · intro x
    simpa [RoughRegime.Lattice.gate] using RoughRegime.Lattice.gate_nonneg Q 1 x
  · simp

/-- The second-moment integrand has a globally integrable quadratic envelope. -/
theorem sinc_second_moment_norm_le (Q : ℕ) (η x : ℝ)
    (hQ : 2 ≤ Q) (hη : 0 < η) :
    ‖x ^ 2 * Real.sinc (x / η) ^ (2 * Q)‖ ≤
      (η ^ 2 + η ^ 4) * (1 + x ^ 2)⁻¹ := by
  have h2 := RoughRegime.Lattice.gate_weighted_power Q 2 (by omega) η x hη
  have h4 := RoughRegime.Lattice.gate_weighted_power Q 4 (by omega) η x hη
  have habs4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_mul, sq_abs]
  rw [sq_abs] at h2
  rw [habs4] at h4
  rw [Real.norm_eq_abs]
  change |x ^ 2 * RoughRegime.Lattice.gate Q η x| ≤ _
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg x)
    (RoughRegime.Lattice.gate_nonneg Q η x))]
  apply (le_div_iff₀ (show 0 < 1 + x ^ 2 by positivity)).2
  change RoughRegime.Lattice.gate Q η x * x ^ 2 ≤ η ^ 2 at h2
  change RoughRegime.Lattice.gate Q η x * x ^ 4 ≤ η ^ 4 at h4
  nlinarith

/-- Finite second moment of the scaled density, for Q >= 2. -/
theorem scaledSincPower_second_moment_integrable (Q : ℕ) (η : ℝ)
    (hQ : 2 ≤ Q) (hη : 0 < η) :
    Integrable (fun x : ℝ => x ^ 2 * Real.sinc (x / η) ^ (2 * Q)) := by
  apply (integrable_inv_one_add_sq.const_mul (η ^ 2 + η ^ 4)).mono'
    (by fun_prop)
  filter_upwards [] with x
  exact sinc_second_moment_norm_le Q η x hQ hη

/-- Finite second moment of the paper's unscaled sinc density. -/
theorem sinc_even_power_second_moment_integrable (Q : ℕ) (hQ : 2 ≤ Q) :
    Integrable (fun x : ℝ => x ^ 2 * Real.sinc x ^ (2 * Q)) := by
  simpa using scaledSincPower_second_moment_integrable Q 1 hQ (by norm_num)

/-- Multiplying by any bounded factor preserves integrability. -/
theorem scaledSincPower_mul_integrable (Q : ℕ) (η : ℝ)
    (hQ : 1 ≤ Q) (hη : 0 < η) (g : ℝ → ℂ)
    (hg : AEStronglyMeasurable g volume) (hb : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun x => scaledSincPower Q η x * g x) :=
  (scaledSincPower_integrable Q η hQ hη).mul_bdd hg (ae_of_all _ hb)

/-- Multiplying by a norm-bounded gate preserves any stated asymptotic bound. -/
theorem isBigO_mul_bounded {α : Type*} (l : Filter α) (f g : α → ℂ) (r : α → ℝ)
    (hf : IsBigO l f r) (hg : ∀ x, ‖g x‖ ≤ 1) :
    IsBigO l (fun x => f x * g x) r := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp hf
  apply IsBigO.of_bound C
  filter_upwards [hC] with x hx
  calc
    ‖f x * g x‖ = ‖f x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _)
    _ = ‖f x‖ := mul_one _
    _ ≤ C * ‖r x‖ := hx

/-- Quadratic decay also holds after multiplication by arbitrary bounded gates. -/
theorem scaledSincPower_mul_isBigO (Q : ℕ) (η : ℝ)
    (hQ : 1 ≤ Q) (hη : 0 < η) (g : ℝ → ℂ) (hb : ∀ x, ‖g x‖ ≤ 1) :
    IsBigO (cocompact ℝ) (fun x => scaledSincPower Q η x * g x)
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) :=
  isBigO_mul_bounded _ _ _ _ (scaledSincPower_isBigO Q η hQ hη) hb

/-- The weighted gate estimate holds for every real exponent in the full
    stated interval, including nonintegral exponents. -/
theorem gate_weighted_rpow (Q : ℕ) (r scale x : ℝ)
    (hr0 : 0 ≤ r) (hrQ : r ≤ (2 * Q : ℕ)) (hscale : 0 < scale) :
    RoughRegime.Lattice.gate Q scale x * |x| ^ r ≤ scale ^ r := by
  by_cases hx : |x| ≤ scale
  · calc
      RoughRegime.Lattice.gate Q scale x * |x| ^ r ≤ 1 * |x| ^ r :=
        mul_le_mul_of_nonneg_right (RoughRegime.Lattice.gate_le_one Q scale x)
          (Real.rpow_nonneg (abs_nonneg x) r)
      _ = |x| ^ r := one_mul _
      _ ≤ scale ^ r := Real.rpow_le_rpow (abs_nonneg x) hx hr0
  · have hsx : scale ≤ |x| := (lt_of_not_ge hx).le
    have hxpos : 0 < |x| := hscale.trans_le hsx
    have hp (y : ℝ) (hy : 0 < y) :
        y ^ (2 * Q) * y ^ (r - (2 * Q : ℕ)) = y ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hy]
      congr 1
      ring
    calc
      RoughRegime.Lattice.gate Q scale x * |x| ^ r =
          (RoughRegime.Lattice.gate Q scale x * |x| ^ (2 * Q)) *
            |x| ^ (r - (2 * Q : ℕ)) := by rw [mul_assoc, hp |x| hxpos]
      _ ≤ scale ^ (2 * Q) * |x| ^ (r - (2 * Q : ℕ)) :=
        mul_le_mul_of_nonneg_right
          (RoughRegime.Lattice.gate_weighted_power Q (2 * Q) le_rfl scale x hscale)
          (Real.rpow_nonneg (abs_nonneg x) _)
      _ ≤ scale ^ (2 * Q) * scale ^ (r - (2 * Q : ℕ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hscale hsx (sub_nonpos.mpr hrQ))
          (pow_nonneg hscale.le _)
      _ = scale ^ r := hp scale hscale

end RoughRegime.LatticeFourier
