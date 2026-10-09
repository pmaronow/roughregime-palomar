module

public import RoughRegime.ProjectionLevelBias
public import RoughRegime.ModelLocalApproximation
public import RoughRegime.DesignChildBlocks


@[expose] public section
/-! The actual weighted dyadic projection telescope used by the estimator. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
namespace RoughRegime.Model
universe u
variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}

theorem ModelWitness.localProjectionIncrement_children (W : ModelWitness A F P)
    {j : ℕ} (c : DyadicCell A.d j) :
    W.localProjectionIncrement c = (1 / 2 : ℝ) * ∑ b : Bool,
      W.cellProjectionTarget (holderOrder A.β)
        (dyadicChildCell (lt_of_lt_of_le Nat.zero_lt_one A.hd) c b) -
      W.cellProjectionTarget (holderOrder A.β) c := by
  unfold ModelWitness.localProjectionIncrement ModelWitness.cellResponseA ModelWitness.cellResponseB
  rw [W.finite_projection_child_energy (holderOrder A.β) c W.a W.b
    (W.holder_memLp_cell c W.a W.measurableA A.α W.smoothA)
    (W.holder_memLp_cell c W.b W.measurableB A.β W.smoothB)
    (fun b => W.holder_memLp_cell _ W.a W.measurableA A.α W.smoothA)
    (fun b => W.holder_memLp_cell _ W.b W.measurableB A.β W.smoothB)]
  rfl

def ModelWitness.levelProjectionIncrement (W : ModelWitness A F P) (j : ℕ) : ℝ :=
  ∑ c : DyadicCell A.d j, (1 / (2 : ℝ) ^ j) * W.localProjectionIncrement c

theorem ModelWitness.levelProjectionIncrement_eq (W : ModelWitness A F P) (j : ℕ) :
    W.levelProjectionIncrement j = W.levelProjectionTarget (holderOrder A.β) (j + 1) -
      W.levelProjectionTarget (holderOrder A.β) j := by
  unfold ModelWitness.levelProjectionIncrement ModelWitness.levelProjectionTarget
  rw [sum_dyadic_children (lt_of_lt_of_le Nat.zero_lt_one A.hd), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [W.localProjectionIncrement_children, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [pow_succ]
  ring

theorem ModelWitness.projection_telescope (W : ModelWitness A F P) (J : ℕ) :
    W.levelProjectionTarget (holderOrder A.β) J =
      W.levelProjectionTarget (holderOrder A.β) 0 +
        ∑ j ∈ Finset.range J, W.levelProjectionIncrement j := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, W.levelProjectionIncrement_eq]
    linarith

theorem uniform_projection_telescope_bias (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P) (J : ℕ),
      |W.productTarget - (W.levelProjectionTarget (holderOrder A.β) 0 +
        ∑ j ∈ Finset.range J, W.levelProjectionIncrement j)| ≤
        C * ((2 : ℝ) ^ (-(J : ℝ) / A.d)) ^ (A.α + A.β) := by
  obtain ⟨C, hC, hb⟩ := uniform_level_projection_bias.{u} A (holderOrder A.β)
    (holderOrder_monotone hαβ) le_rfl
  refine ⟨C, hC, ?_⟩
  intro Z _ F P W J
  rw [← W.projection_telescope J]
  exact hb Z F P W J

end RoughRegime.Model
