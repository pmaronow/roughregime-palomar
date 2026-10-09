module

public import RoughRegime.DyadicSelection


@[expose] public section
/-! The actual partition cells differ from closed rectangles only on null faces. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem rectangle_volume {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) :
    volume (rectangle o s) = ∏ i, ENNReal.ofReal (s i) := by
  have he : rectangle o s = WithLp.ofLp ⁻¹' Icc (fun i => o i) (fun i => o i + s i) := by
    ext x
    simp only [rectangle, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp

def dyadicUpperFace {d j : ℕ} (c : DyadicCell d j) (i : Fin d) : Set (Covariate d) :=
  {x | x ∈ dyadicRectangle c ∧ x i = ((c i : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j i}

theorem dyadicUpperFace_volume_zero {d j : ℕ} (c : DyadicCell d j) (i : Fin d) :
    volume (dyadicUpperFace c i) = 0 := by
  classical
  let o : Covariate d := WithLp.toLp 2 (fun k => if k = i then
    ((c k : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j k else (c k : ℝ) / (2 : ℝ) ^ axisDepth d j k)
  let s : Fin d → ℝ := fun k => if k = i then 0 else 1 / (2 : ℝ) ^ axisDepth d j k
  have hsub : dyadicUpperFace c i ⊆ rectangle o s := by
    intro x hx k
    by_cases hk : k = i
    · subst k
      simp only [mem_Icc, o, s,
        ite_eq_left rfl, add_zero]
      rw [hx.2]
      exact ⟨le_rfl, le_rfl⟩
    · have hh := hx.1 k
      simpa only [o, s, WithLp.ofLp_toLp, ite_eq_right hk, add_div] using hh
  apply measure_mono_null hsub
  rw [rectangle_volume]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [s])

theorem dyadicRectangle_bad_subset_faces {d j : ℕ} (c : DyadicCell d j) :
    dyadicRectangle c \ dyadicPartitionCell c ⊆ ⋃ i : Fin d, dyadicUpperFace c i := by
  intro x hx
  by_contra hfaces
  have he : dyadicSelection d j x = c := by
    funext i
    apply intervalIndex_eq_of_halfopen
    have hne : x i ≠ ((c i : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j i := by
      intro hi
      exact hfaces (mem_iUnion.mpr ⟨i, hx.1, hi⟩)
    have hh := hx.1 i
    have hu := lt_of_le_of_ne hh.2 hne
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (show x i ∈ Ico
      ((c i : ℝ) / (2 : ℝ) ^ axisDepth d j i)
      (((c i : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j i) from ⟨hh.1, hu⟩)
  apply hx.2
  exact ⟨dyadicRectangle_subset_cube c hx.1, he⟩

theorem dyadicRectangle_ae_eq_partition {d j : ℕ} (c : DyadicCell d j) :
    dyadicRectangle c =ᵐ[volume] dyadicPartitionCell c := by
  have hz : volume (dyadicRectangle c \ dyadicPartitionCell c) = 0 :=
    measure_mono_null (dyadicRectangle_bad_subset_faces c)
      (measure_iUnion_null (dyadicUpperFace_volume_zero c))
  have hae : ∀ᵐ x ∂(volume : Measure (Covariate d)), x ∉
      dyadicRectangle c \ dyadicPartitionCell c := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hz
  filter_upwards [hae] with x hx
  apply propext
  constructor
  · intro hr
    by_contra hp
    exact hx ⟨hr, hp⟩
  · exact fun hp => dyadicPartitionCell_subset_rectangle c hp

theorem dyadicPartitionCell_volume {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    volume (dyadicPartitionCell c) = ENNReal.ofReal (1 / (2 : ℝ) ^ j) := by
  rw [← measure_congr (dyadicRectangle_ae_eq_partition c)]
  exact dyadicRectangle_volume hd c

theorem dyadicPartitionCell_cubeVolume {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    cubeVolume d (dyadicPartitionCell c) = ENNReal.ofReal (1 / (2 : ℝ) ^ j) := by
  rw [cubeVolume, Measure.restrict_apply (dyadicPartitionCell_measurable c),
    inter_eq_left.mpr (fun _ hx => hx.1)]
  exact dyadicPartitionCell_volume hd c

end RoughRegime.Model
