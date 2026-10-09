module

public import RoughRegime.ModelLocalApproximation
public import RoughRegime.Foundation


@[expose] public section
/-! The genuine local dyadic increment is small uniformly over all models. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RoughRegime.Model
universe u
open RoughRegime.HilbertGram

 theorem nested_increment_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K ≤ L) (f g ta tb : E) (hta : ta ∈ K) (htb : tb ∈ K) :
    ‖⟪L.starProjection f, L.starProjection g⟫ - ⟪K.starProjection f, K.starProjection g⟫‖ ≤
      4 * ‖f - ta‖ * ‖g - tb‖ := by
  have hb (v t : E) (ht : t ∈ K) :
      ‖L.starProjection v - K.starProjection v‖ ≤ 2 * ‖v - t‖ := by
    have he : L.starProjection v - K.starProjection v =
        L.starProjection (v - t) - K.starProjection (v - t) := by
      rw [map_sub, map_sub, L.starProjection_eq_self_iff.mpr (hKL ht), K.starProjection_eq_self_iff.mpr ht]
      abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (L.norm_starProjection_apply_le _)
      (K.norm_starProjection_apply_le _)).trans_eq (by ring))
  rw [RoughRegime.Foundation.nested_projection_increment K L hKL f g, Real.norm_eq_abs]
  calc
    _ ≤ ‖L.starProjection f - K.starProjection f‖ * ‖L.starProjection g - K.starProjection g‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (2 * ‖f - ta‖) * (2 * ‖g - tb‖) := mul_le_mul (hb f ta hta) (hb g tb htb)
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

 theorem uniform_model_increment_size (A : Parameters) (hαβ : A.α ≤ A.β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j : ℕ) (c : DyadicCell A.d j),
      ‖W.localProjectionIncrement c‖ ≤ C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ (A.α + A.β) := by
  obtain ⟨Ha, hHa, ha⟩ := uniform_model_cell_approximation.{u} A A.α
  obtain ⟨Hb, hHb, hb⟩ := uniform_model_cell_approximation.{u} A A.β
  refine ⟨4 * Ha * Hb, by positivity, ?_⟩
  intro Z _ F P W j c
  obtain ⟨hqa, hda, hea⟩ := ha Z F P W j c W.a W.measurableA W.smoothA
  obtain ⟨hqb, hdb, heb⟩ := hb Z F P W j c W.b W.measurableB W.smoothB
  let K := basisSpan (W.weightedParentBasis (holderOrder A.β) c)
  let L := basisSpan (W.weightedChildBasis (holderOrder A.β) c)
  have hma : hqa.toLp _ ∈ K := W.weighted_parent_span_mono c (holderOrder_monotone hαβ)
    (W.weighted_polynomial_parent_member c _ hda hqa)
  have hmb : hqb.toLp _ ∈ K := W.weighted_polynomial_parent_member c _ hdb hqb
  have hKL : K ≤ L := by
    change basisSpan _ ≤ basisSpan _
    rw [← W.referenceParentMatrix_expansion c (holderOrder A.β) (holderOrder A.β) le_rfl]
    exact parentBasis_span_le _ _
  have hn := nested_increment_norm_le K L hKL (W.cellResponseA c) (W.cellResponseB c)
    (hqa.toLp _) (hqb.toLp _) hma hmb
  calc
    _ ≤ 4 * ‖W.cellResponseA c - hqa.toLp _‖ * ‖W.cellResponseB c - hqb.toLp _‖ := hn
    _ ≤ 4 * (Ha * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.α) *
        (Hb * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ A.β) := by
      gcongr
      · exact hea
      · exact heb
    _ = _ := by rw [Real.rpow_add (dyadicScale_pos A j)]; ring

end RoughRegime.Model
