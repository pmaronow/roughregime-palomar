module

public import RoughRegime.RectangleTransport


@[expose] public section
/-! A genuine measurable partition selector for the cyclic dyadic rectangles. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

def intervalIndex (N : ℕ) (hN : 0 < N) (x : ℝ) : Fin N :=
  ⟨min (Nat.floor ((N : ℝ) * x)) (N - 1),
    (min_le_right _ _).trans_lt (Nat.sub_lt hN (by norm_num))⟩

theorem intervalIndex_measurable (N : ℕ) (hN : 0 < N) :
    Measurable (intervalIndex N hN) := by
  have hf : Measurable (fun x : ℝ => min (Nat.floor ((N : ℝ) * x)) (N - 1)) :=
    (Nat.measurable_floor.comp (measurable_const.mul measurable_id)).min measurable_const
  apply measurable_to_countable
  intro c
  convert (measurableSet_singleton (intervalIndex N hN c).val).preimage hf using 1
  ext x
  simp [intervalIndex, Fin.ext_iff]

theorem intervalIndex_bounds (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    x ∈ Icc ((intervalIndex N hN x : ℝ) / N) (((intervalIndex N hN x : ℝ) + 1) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod : 0 ≤ (N : ℝ) * x := mul_nonneg hNr.le hx.1
  have hlo := Nat.floor_le hprod
  have hmin : ((min (Nat.floor ((N : ℝ) * x)) (N - 1) : ℕ) : ℝ) ≤ Nat.floor ((N : ℝ) * x) := by
    exact_mod_cast min_le_left (Nat.floor ((N : ℝ) * x)) (N - 1)
  constructor
  · apply (div_le_iff₀ hNr).mpr
    change ((min (Nat.floor ((N : ℝ) * x)) (N - 1) : ℕ) : ℝ) ≤ x * N
    nlinarith
  · apply (le_div_iff₀ hNr).mpr
    change x * N ≤ ((min (Nat.floor ((N : ℝ) * x)) (N - 1) : ℕ) : ℝ) + 1
    by_cases hh : Nat.floor ((N : ℝ) * x) ≤ N - 1
    · rw [min_eq_left hh]
      have hu := Nat.lt_floor_add_one ((N : ℝ) * x)
      nlinarith
    · rw [min_eq_right (Nat.le_of_not_ge hh)]
      have he : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast Nat.sub_add_cancel hN
      rw [he]
      nlinarith [hx.2]

theorem intervalIndex_eq_of_halfopen (N : ℕ) (hN : 0 < N) (c : Fin N) (x : ℝ)
    (hx : x ∈ Ico ((c : ℝ) / N) (((c : ℝ) + 1) / N)) : intervalIndex N hN x = c := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : (c : ℝ) ≤ (N : ℝ) * x := by
    have h := (div_le_iff₀ hNr).mp hx.1
    nlinarith
  have hhi : (N : ℝ) * x < (c : ℝ) + 1 := by
    have h := (lt_div_iff₀ hNr).mp hx.2
    nlinarith
  have hf : Nat.floor ((N : ℝ) * x) = c.val :=
    (Nat.floor_eq_iff ((Nat.cast_nonneg c.val).trans hlo)).mpr ⟨hlo, hhi⟩
  apply Fin.ext
  simp only [intervalIndex, hf]
  exact min_eq_left (by omega)

def dyadicSelection (d j : ℕ) (x : Covariate d) : DyadicCell d j :=
  fun i => intervalIndex (2 ^ axisDepth d j i) (by positivity) (x i)

theorem dyadicSelection_measurable (d j : ℕ) : Measurable (dyadicSelection d j) := by
  apply measurable_pi_iff.mpr
  intro i
  have hi : Measurable (fun x : Covariate d => x i) :=
    ((EuclideanSpace.proj i).continuous : Continuous (fun x : Covariate d => x i)).measurable
  exact (intervalIndex_measurable _ (by positivity)).comp hi

theorem dyadicSelection_rectangle (d j : ℕ) (x : Covariate d) (hx : x ∈ cube d) :
    x ∈ dyadicRectangle (dyadicSelection d j x) := by
  intro i
  simpa only [dyadicSelection, Nat.cast_pow, Nat.cast_ofNat] using
    intervalIndex_bounds (2 ^ axisDepth d j i) (by positivity) (x i) (hx i)

def dyadicPartitionCell {d j : ℕ} (c : DyadicCell d j) : Set (Covariate d) :=
  cube d ∩ (dyadicSelection d j ⁻¹' {c})

theorem dyadicPartitionCell_measurable {d j : ℕ} (c : DyadicCell d j) :
    MeasurableSet (dyadicPartitionCell c) :=
  (measurableSet_cube d).inter ((measurableSet_singleton c).preimage (dyadicSelection_measurable d j))

theorem dyadicPartitionCell_subset_rectangle {d j : ℕ} (c : DyadicCell d j) :
    dyadicPartitionCell c ⊆ dyadicRectangle c := by
  intro x hx
  have he : dyadicSelection d j x = c := hx.2
  rw [← he]
  exact dyadicSelection_rectangle d j x hx.1

theorem dyadicPartitionCell_pairwiseDisjoint (d j : ℕ) :
    Pairwise (fun c e : DyadicCell d j => Disjoint (dyadicPartitionCell c) (dyadicPartitionCell e)) := by
  intro c e hce
  apply Set.disjoint_left.mpr
  intro x hc he
  apply hce
  exact hc.2.symm.trans he.2

theorem dyadicPartitionCell_cover (d j : ℕ) :
    (⋃ c : DyadicCell d j, dyadicPartitionCell c) = cube d := by
  ext x
  simp only [mem_iUnion, dyadicPartitionCell, mem_inter_iff, mem_preimage, mem_singleton_iff]
  exact ⟨fun ⟨c, hc, _⟩ => hc, fun hx => ⟨dyadicSelection d j x, hx, rfl⟩⟩

end RoughRegime.Model
