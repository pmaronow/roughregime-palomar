module

public import RoughRegime.LatticeConstruction


@[expose] public section
/-! Actual multivariate derivative bounds for the source's smooth digit selectors. -/
noncomputable section
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors

/-- The scalar selector estimate controls every Euclidean Frechet derivative;
 the constant depends only on derivative order and the fixed smooth step. -/
theorem coordinateSoftDigit_derivative_bound (U : SmoothStep) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ), 0 < γ → γ ≤ 1 / 4 →
      ∀ {d : ℕ} (a : ℕ) (q : Fin d) (x : Model.Covariate d),
      ‖iteratedFDeriv ℝ N (coordinateSoftDigit U γ a q) x‖ ≤ C * ((2 : ℝ) ^ a / γ) ^ N := by
  obtain ⟨C, hC, hbound⟩ := softDigit_derivative_bound U N
  refine ⟨C, hC, ?_⟩
  intro γ hγ hγ1 d a q x
  let P : Model.Covariate d →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin d => ℝ) q
  let L : Model.Covariate d →L[ℝ] ℝ := (2 : ℝ) ^ a • P
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound (by norm_num)
    intro y
    simpa only [P, PiLp.proj_apply, one_mul] using PiLp.norm_apply_le y q
  have hL : ‖L‖ ≤ (2 : ℝ) ^ a := by
    dsimp [L]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left hP (by positivity)).trans_eq (by ring)
  have hsmooth := softDigit_smooth U γ hγ hγ1
  change ‖iteratedFDeriv ℝ N ((softDigit U γ) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hsmooth x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ N (softDigit U γ) (L x)‖ * ∏ _i : Fin N, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = |iteratedDeriv N (softDigit U γ) (L x)| * ‖L‖ ^ N := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      simp
    _ ≤ (C * γ ^ (-(N : ℤ))) * ((2 : ℝ) ^ a) ^ N :=
      mul_le_mul (hbound γ hγ hγ1 (L x)) (pow_le_pow_left₀ (norm_nonneg _) hL N)
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by
      rw [zpow_neg, zpow_natCast, div_pow]
      ring

end RoughRegime.LatticePriors
