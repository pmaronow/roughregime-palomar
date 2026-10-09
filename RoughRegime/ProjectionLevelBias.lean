module

public import RoughRegime.ProjectionBias


@[expose] public section
/-! Uniform bias of the actual dyadic projection target. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RoughRegime.Model
universe u
variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}

theorem ModelWitness.product_integrable (W : ModelWitness A F P) :
    Integrable (fun x => W.a x * W.b x * W.designDensity x) (cubeVolume A.d) := by
  apply Integrable.of_bound ((W.measurableA.mul W.measurableB).mul W.designDensity_measurable).aestronglyMeasurable
    (A.H * A.H * A.gplus)
  filter_upwards [W.densityBounds, ae_restrict_mem (measurableSet_cube A.d)] with x hg hx
  change A.gminus ≤ W.designDensity x ∧ W.designDensity x ≤ A.gplus at hg
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (A.hgminus.le.trans hg.1)]
  exact mul_le_mul (mul_le_mul (holderNorm_bounds_values W.a A.α A.H A.hH.le W.smoothA x hx)
    (holderNorm_bounds_values W.b A.β A.H A.hH.le W.smoothB x hx)
    (abs_nonneg _) A.hH.le) hg.2 (A.hgminus.le.trans hg.1) (mul_nonneg A.hH.le A.hH.le)

theorem ModelWitness.productTarget_decomposition (W : ModelWitness A F P) (j : ℕ) :
    W.productTarget = ∑ c : DyadicCell A.d j, (1 / (2 : ℝ) ^ j) * W.cellProductTarget c := by
  rw [ModelWitness.productTarget, dyadic_integral_decomposition (lt_of_lt_of_le Nat.zero_lt_one A.hd)
    _ W.product_integrable]
  apply Finset.sum_congr rfl
  intro c _
  rw [W.cellProductTarget_integral]

theorem uniform_level_projection_bias (A : Parameters) (k : ℕ)
    (hak : holderOrder A.α ≤ k) (hbk : holderOrder A.β ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (j : ℕ),
      |W.productTarget - W.levelProjectionTarget k j| ≤
        C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ (A.α + A.β) := by
  obtain ⟨C, hC, hb⟩ := uniform_cell_projection_bias.{u} A k hak hbk
  refine ⟨C, hC, ?_⟩
  intro Z _ F P W j
  calc
    _ = |∑ c : DyadicCell A.d j, (1 / (2 : ℝ) ^ j) *
        (W.cellProductTarget c - W.cellProjectionTarget k c)| := by
      rw [W.productTarget_decomposition j, ModelWitness.levelProjectionTarget,
        ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c : DyadicCell A.d j, |(1 / (2 : ℝ) ^ j) *
        (W.cellProductTarget c - W.cellProjectionTarget k c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : DyadicCell A.d j, (1 / (2 : ℝ) ^ j) *
        (C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ (A.α + A.β)) := by
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 ^ j)]
      exact mul_le_mul_of_nonneg_left (hb Z F P W j c) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ,
        dyadicCell_card A.d j (lt_of_lt_of_le Nat.zero_lt_one A.hd),
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

end RoughRegime.Model
