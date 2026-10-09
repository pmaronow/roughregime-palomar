module

public import RoughRegime.ModelSwap


@[expose] public section
/-! Fixed model constants and exact physical-to-resolution bias normalization. -/
noncomputable section
namespace RoughRegime.Model

theorem Parameters.theta_pos (A : Parameters) : 0 < A.theta := by
  exact div_pos (add_pos A.hα A.hβ)
    (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one A.hd))

theorem Parameters.nu_ge_two (A : Parameters) : 2 ≤ A.nu := by
  have ha : 0 < (A.d + holderOrder A.α).choose A.d := Nat.choose_pos (Nat.le_add_right _ _)
  have hb : 0 < (A.d + holderOrder A.β).choose A.d := Nat.choose_pos (Nat.le_add_right _ _)
  unfold Parameters.nu
  omega

theorem Parameters.tau_pos (A : Parameters) : 0 < RoughRegime.Rates.tau A.gminus A.gplus :=
  RoughRegime.Rates.tau_pos A.gminus A.gplus A.hgminus A.hgplus

theorem dyadic_product_scale_eq_resolution (A : Parameters) (j : ℕ) :
    ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ (A.α + A.β) = ((2 : ℝ) ^ j) ^ (-A.theta) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  unfold Parameters.theta
  ring

theorem uniform_projection_telescope_resolution_bias (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : MeasureTheory.ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (J : ℕ),
      |W.productTarget - (W.levelProjectionTarget (holderOrder A.β) 0 +
        ∑ j ∈ Finset.range J, W.levelProjectionIncrement j)| ≤ C * ((2 : ℝ) ^ J) ^ (-A.theta) := by
  obtain ⟨C, hC, hb⟩ := uniform_projection_telescope_bias.{u} A hαβ
  refine ⟨C, hC, ?_⟩
  intro Z _ F P W J
  simpa only [dyadic_product_scale_eq_resolution] using hb Z F P W J

end RoughRegime.Model
