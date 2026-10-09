module

public import RoughRegime.DesignWeightedChildren
public import RoughRegime.DyadicIntegral


@[expose] public section
/-! Actual model projection energies and their product Hölder bias. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RoughRegime.Model
variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}

theorem projection_residual_le_approximation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (f q : E) (hq : q ∈ K) : ‖f - K.starProjection f‖ ≤ 2 * ‖f - q‖ := by
  have he : f - K.starProjection f = (f - q) - K.starProjection (f - q) := by
    rw [map_sub, K.starProjection_eq_self_iff.mpr hq]
    abel
  rw [he]
  calc
    _ ≤ ‖f - q‖ + ‖K.starProjection (f - q)‖ := norm_sub_le _ _
    _ ≤ ‖f - q‖ + ‖f - q‖ := add_le_add le_rfl (K.norm_starProjection_apply_le (f - q))
    _ = _ := by ring

def ModelWitness.cellALp (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    Lp ℝ 2 (W.cellDesignMeasure c) := (W.holder_memLp_cell c W.a W.measurableA A.α W.smoothA).toLp W.a

def ModelWitness.cellBLp (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    Lp ℝ 2 (W.cellDesignMeasure c) := (W.holder_memLp_cell c W.b W.measurableB A.β W.smoothB).toLp W.b

def ModelWitness.cellProductTarget (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) : ℝ :=
  inner ℝ (W.cellALp c) (W.cellBLp c)

def ModelWitness.cellProjectionTarget (W : ModelWitness A F P) {j : ℕ} (k : ℕ)
    (c : DyadicCell A.d j) : ℝ :=
  inner ℝ ((HilbertGram.basisSpan (W.weightedParentBasis k c)).starProjection (W.cellALp c))
    ((HilbertGram.basisSpan (W.weightedParentBasis k c)).starProjection (W.cellBLp c))

def ModelWitness.levelProjectionTarget (W : ModelWitness A F P) (k j : ℕ) : ℝ :=
  ∑ c : DyadicCell A.d j, (1 / (2 : ℝ) ^ j) * W.cellProjectionTarget k c

def ModelWitness.productTarget (W : ModelWitness A F P) : ℝ :=
  ∫ x, W.a x * W.b x * W.designDensity x ∂cubeVolume A.d

theorem ModelWitness.cellProductTarget_integral (W : ModelWitness A F P) {j : ℕ}
    (c : DyadicCell A.d j) :
    W.cellProductTarget c = ∫ x, W.a x * W.b x * W.designDensity x
      ∂rectangleVolume (dyadicOrigin c) (dyadicSides c) := by
  have h : W.cellProductTarget c = ∫ x, W.a x * W.b x ∂W.cellDesignMeasure c := by
    rw [ModelWitness.cellProductTarget, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(W.holder_memLp_cell c W.a W.measurableA A.α W.smoothA).coeFn_toLp,
      (W.holder_memLp_cell c W.b W.measurableB A.β W.smoothB).coeFn_toLp] with x ha hb
    simpa [ModelWitness.cellALp, ModelWitness.cellBLp, ha, hb, mul_comm]
  rw [h, ModelWitness.cellDesignMeasure, weightedDesignMeasure_integral _ _ W.designDensity_measurable
    ((W.dyadic_density_bounds c).mono (fun _ hx => A.hgminus.le.trans hx.1))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem ModelWitness.weightedParentBasis_linearIndependent (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) : LinearIndependent ℝ (W.weightedParentBasis k c) := by
  obtain ⟨L, hL, he⟩ := dyadic_parent_matrix (lt_of_lt_of_le Nat.zero_lt_one A.hd) c (le_refl k)
  rw [← W.weighted_parent_expansion c L he]
  exact HilbertGram.parentBasis_linearIndependent _ (W.weightedChildBasis_linearIndependent k c) L hL

theorem ModelWitness.cellProjectionTarget_energy (W : ModelWitness A F P) {j : ℕ}
    (k : ℕ) (c : DyadicCell A.d j) :
    W.cellProjectionTarget k c = HilbertGram.moments (W.weightedParentBasis k c) (W.cellALp c) ⬝ᵥ
      (Matrix.gram ℝ (W.weightedParentBasis k c))⁻¹.mulVec
        (HilbertGram.moments (W.weightedParentBasis k c) (W.cellBLp c)) :=
  HilbertGram.child_projection_inner _ (W.weightedParentBasis_linearIndependent k c) _ _

end RoughRegime.Model
