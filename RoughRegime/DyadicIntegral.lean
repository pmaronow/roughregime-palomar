module

public import RoughRegime.DyadicChildren


@[expose] public section
/-! Exact integral decomposition over the actual normalized dyadic cells. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem dyadicCell_integral_normalization {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j)
    (f : Covariate d → ℝ) :
    (1 / (2 : ℝ) ^ j) * (∫ x, f x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c)) =
      ∫ x in dyadicPartitionCell c, f x ∂cubeVolume d := by
  rw [dyadicRectangle_normalizedVolume hd c, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ j), smul_eq_mul]
  field_simp

theorem dyadic_integral_decomposition {d j : ℕ} (hd : 0 < d) (f : Covariate d → ℝ)
    (hf : Integrable f (cubeVolume d)) :
    (∫ x, f x ∂cubeVolume d) =
      ∑ c : DyadicCell d j, (1 / (2 : ℝ) ^ j) *
        (∫ x, f x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c)) := by
  have hsum := integral_iUnion_fintype (μ := volume) (f := f)
    (fun c : DyadicCell d j => dyadicPartitionCell_measurable c)
    (dyadicPartitionCell_pairwiseDisjoint d j)
    (fun c => (show IntegrableOn f (cube d) volume from hf).mono_set (fun x hx => hx.1))
  rw [dyadicPartitionCell_cover] at hsum
  calc
    _ = ∑ c : DyadicCell d j, ∫ x in dyadicPartitionCell c, f x ∂volume := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [dyadicCell_integral_normalization hd c, cubeVolume,
        Measure.restrict_restrict (dyadicPartitionCell_measurable c),
        inter_eq_left.mpr (fun _ hx => hx.1)]

theorem dyadic_children_union {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    dyadicRectangle (dyadicChildCell hd c false) ∪ dyadicRectangle (dyadicChildCell hd c true) =
      dyadicRectangle c := by
  have hsurj : Function.Surjective (rectangleEmbed (dyadicOrigin c) (dyadicSides c)) := fun y =>
    ⟨rectangleCoords (dyadicOrigin c) (dyadicSides c) y,
      rectangleEmbed_coords _ _ (fun i => (dyadicSides_pos c i).ne') y⟩
  apply Set.preimage_injective.mpr hsurj
  rw [preimage_union, dyadicChild_preimage, dyadicChild_preimage,
    splitRectangle_union, dyadicRectangle_eq_rectangle,
    rectangleEmbed_preimage _ _ (dyadicSides_pos c)]

theorem dyadicChildCell_false_ne_true {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    dyadicChildCell hd c false ≠ dyadicChildCell hd c true := by
  intro he
  have hh := congrArg (fun e : DyadicCell d (j + 1) => (e (dyadicSplitAxis d j hd)).val) he
  simp [dyadicChildCell, dyadicSplitAxis, Bool.toNat] at hh

theorem dyadic_children_aeDisjoint {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    AEDisjoint volume (dyadicRectangle (dyadicChildCell hd c false))
      (dyadicRectangle (dyadicChildCell hd c true)) := by
  have h := (dyadicPartitionCell_pairwiseDisjoint d (j + 1)
    (dyadicChildCell_false_ne_true hd c)).aedisjoint (μ := volume)
  exact h.congr (dyadicRectangle_ae_eq_partition _) (dyadicRectangle_ae_eq_partition _)

theorem dyadic_children_integral {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j)
    (f : Covariate d → ℝ) (hf : Integrable f (cubeVolume d)) :
    (∫ x, f x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c)) =
      (1 / 2 : ℝ) * ∑ b : Bool, (∫ x, f x ∂rectangleVolume
        (dyadicOrigin (dyadicChildCell hd c b)) (dyadicSides (dyadicChildCell hd c b))) := by
  have hnorm (j : ℕ) (c : DyadicCell d j) :
      (∫ x, f x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c)) =
        (2 : ℝ) ^ j * ∫ x in dyadicRectangle c, f x ∂volume := by
    rw [rectangleVolume, dyadicSides_prod hd c, one_div_div, div_one,
      ← dyadicRectangle_eq_rectangle, integral_smul_measure]
    simp [ENNReal.toReal_ofReal, smul_eq_mul]
  have hi := integral_union_ae (f := f) (dyadic_children_aeDisjoint hd c)
    (dyadicRectangle_measurable _).nullMeasurableSet
    ((show IntegrableOn f (cube d) volume from hf).mono_set (dyadicRectangle_subset_cube _))
    ((show IntegrableOn f (cube d) volume from hf).mono_set (dyadicRectangle_subset_cube _))
  rw [dyadic_children_union hd c] at hi
  simp only [Fintype.sum_bool, hnorm, pow_succ]
  rw [hi]
  ring

end RoughRegime.Model
