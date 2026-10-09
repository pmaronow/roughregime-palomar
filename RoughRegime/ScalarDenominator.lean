module

public import RoughRegime.Upper


@[expose] public section
/-! The reciprocal Chebyshev kernel has no scalar denominator zeros in its disk. -/

noncomputable section
open Complex

namespace RoughRegime.ComplexKernel

theorem scalarDenominator_ne_zero (ρ : ℝ) (z : ℂ) (t : ℝ)
    (hρ : 0 < ρ) (ht : t ∈ Set.Icc (-1) 1) (hz : ρ * ‖z‖ < 1) :
    1 + 2 * (ρ : ℂ) * z * (t : ℂ) + (ρ : ℂ) ^ 2 * z ^ 2 ≠ 0 := by
  let θ := Real.arccos t
  let E : ℂ := Complex.exp ((θ : ℂ) * I)
  let F : ℂ := Complex.exp ((-θ : ℂ) * I)
  have hcos : Real.cos θ = t := Real.cos_arccos ht.1 ht.2
  have hEF : E * F = 1 := by
    dsimp [E, F]
    rw [← Complex.exp_add]
    have he : (θ : ℂ) * I + (-θ : ℂ) * I = 0 := by push_cast; ring
    rw [he, Complex.exp_zero]
  have hsum : E + F = 2 * (t : ℂ) := by
    rw [← hcos, Complex.ofReal_cos, Complex.cos]
    dsimp [E, F]
    ring
  have hEnorm : ‖(ρ : ℂ) * z * E‖ < 1 := by
    simpa [E, norm_mul, abs_of_pos hρ] using hz
  have hFnorm : ‖(ρ : ℂ) * z * F‖ < 1 := by
    dsimp [F]
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hz
  have ha : 1 + (ρ : ℂ) * z * E ≠ 0 := by
    intro he
    have he' : (ρ : ℂ) * z * E = -1 := by linear_combination he
    simpa [he'] using hEnorm
  have hb : 1 + (ρ : ℂ) * z * F ≠ 0 := by
    intro he
    have he' : (ρ : ℂ) * z * F = -1 := by linear_combination he
    simpa [he'] using hFnorm
  have hfactor : 1 + 2 * (ρ : ℂ) * z * (t : ℂ) + (ρ : ℂ) ^ 2 * z ^ 2 =
      (1 + (ρ : ℂ) * z * E) * (1 + (ρ : ℂ) * z * F) := by
    calc
      _ = 1 + (ρ : ℂ) * z * (E + F) + (ρ : ℂ) ^ 2 * z ^ 2 * (E * F) := by
        rw [hsum, hEF]
        ring
      _ = _ := by ring
  rw [hfactor]
  exact mul_ne_zero ha hb

end RoughRegime.ComplexKernel
