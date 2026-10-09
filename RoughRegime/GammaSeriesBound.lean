module

public import RoughRegime.PoissonSeriesBounds
public import RoughRegime.GammaBounds


@[expose] public section
/-! The genuine Gamma tail is bounded by its factorial-exponential majorant. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.PoissonMeasure

theorem gamma_series_bound (Γ : ℕ → ℝ) (hΓ : ∀ j, 0 ≤ Γ j)
    (D q z : ℝ) (hD : 0 ≤ D) (hq : 0 ≤ q) (hz : 0 ≤ z) (M : ℕ)
    (hb : ∀ i, Γ (i + M) ≤ D * q ^ i) :
    Summable (fun j => if M ≤ j then z ^ j / j.factorial * Γ j else 0) ∧
      (∑' j, if M ≤ j then z ^ j / j.factorial * Γ j else 0) ≤
        D * (z ^ M / M.factorial) * Real.exp (z * q) := by
  let f := fun j => if M ≤ j then z ^ j / j.factorial * Γ j else 0
  have hfn (j : ℕ) : 0 ≤ f j := by
    have hj := hΓ j
    dsimp [f]
    split_ifs <;> positivity
  have hbound (i : ℕ) : f (i + M) ≤ (D * (z ^ M / M.factorial)) * ((z * q) ^ i / i.factorial) := by
    dsimp [f]
    rw [ite_eq_left (by omega)]
    calc
      _ ≤ z ^ (i + M) / (i + M).factorial * (D * q ^ i) :=
        mul_le_mul_of_nonneg_left (hb i) (by positivity)
      _ ≤ z ^ (i + M) / ((M.factorial : ℝ) * i.factorial) * (D * q ^ i) := by
        gcongr
        exact ScalarExponentialTail.factorial_supermultiplicative M i
      _ = _ := by rw [pow_add, mul_pow]; ring
  have hs := (Real.summable_pow_div_factorial (z * q)).mul_left (D * (z ^ M / M.factorial))
  have hshift : Summable (fun i => f (i + M)) :=
    Summable.of_nonneg_of_le (fun i => hfn _) hbound hs
  have hf : Summable f := (summable_nat_add_iff M).mp hshift
  refine ⟨hf, ?_⟩
  rw [PoissonSeriesBounds.tsum_supported_shift f M hf (by
    intro j hj
    dsimp [f]
    rw [ite_eq_right (by omega)])]
  exact (hshift.tsum_le_tsum hbound hs).trans_eq (by
    rw [tsum_mul_left, ScalarExponentialTail.exp_series_sum])

 theorem gammaSpatialFactor_shift (R : ℝ) (hR : 0 < R) (M i : ℕ) :
    RoughRegime.LatticePriors.gammaSpatialFactor R M (i + M) =
      R ^ (1 - (M : ℝ)) * (R ^ Real.sqrt M) ^ i := by
  unfold RoughRegime.LatticePriors.gammaSpatialFactor
  rw [Nat.cast_add]
  have he : 1 - (M : ℝ) + (((i : ℝ) + M) - M) * Real.sqrt M =
      (1 - (M : ℝ)) + Real.sqrt M * (i : ℝ) := by ring
  rw [he, Real.rpow_add hR, Real.rpow_mul hR.le, Real.rpow_natCast]

 theorem spatial_gamma_series_bound (Γ : ℕ → ℝ) (hΓ : ∀ j, 0 ≤ Γ j)
    (CΓ D CE R z : ℝ) (hC : 0 ≤ CΓ) (hD : 0 ≤ D) (hR : 0 < R) (hz : 0 ≤ z) (M : ℕ)
    (hb : ∀ j, M ≤ j → Γ j ≤ CΓ ^ (j + 1) * D * Real.exp (CE * M) *
      RoughRegime.LatticePriors.gammaSpatialFactor R M j) :
    Summable (fun j => if M ≤ j then z ^ j / j.factorial * Γ j else 0) ∧
      (∑' j, if M ≤ j then z ^ j / j.factorial * Γ j else 0) ≤
        CΓ * D * Real.exp (CE * M) * R ^ (1 - (M : ℝ)) *
          ((CΓ * z) ^ M / M.factorial) * Real.exp (CΓ * z * R ^ Real.sqrt M) := by
  have hh := gamma_series_bound Γ hΓ
    (CΓ ^ (M + 1) * D * Real.exp (CE * M) * R ^ (1 - (M : ℝ)))
    (CΓ * R ^ Real.sqrt M) z (by positivity) (by positivity) hz M (by
      intro i
      have hi := hb (i + M) (by omega)
      rw [gammaSpatialFactor_shift R hR M i] at hi
      convert hi using 1
      rw [mul_pow, show i + M + 1 = i + (M + 1) by omega, pow_add]
      ring)
  have hexp : z * (CΓ * R ^ Real.sqrt M) = CΓ * z * R ^ Real.sqrt M := by ring
  rw [hexp] at hh
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  rw [pow_add, mul_pow]
  ring

end RoughRegime.PoissonMeasure
