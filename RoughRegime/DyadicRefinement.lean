module

public import RoughRegime.DyadicPartition


@[expose] public section
/-! Exact cyclic refinement of the source resolution grid. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

theorem axisDepth_succ (d j : ℕ) (hd : 0 < d) (i : Fin d) :
    axisDepth d (j + 1) i = axisDepth d j i + if i.val = j % d then 1 else 0 := by
  have hr : j % d < d := Nat.mod_lt j hd
  have hj : j = d * (j / d) + j % d := (Nat.div_add_mod j d).symm
  by_cases h : j % d + 1 < d
  · have hj1 : j + 1 = d * (j / d) + (j % d + 1) := by omega
    have hq : (j + 1) / d = j / d := by
      rw [hj1, Nat.mul_add_div hd, Nat.div_eq_of_lt h]
      omega
    have hm : (j + 1) % d = j % d + 1 := by
      rw [hj1]
      simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt h]
    simp only [axisDepth, hq, hm]
    split_ifs <;> omega
  · have hrd : j % d + 1 = d := by omega
    have hj1 : j + 1 = d * (j / d + 1) := by nlinarith
    have hq : (j + 1) / d = j / d + 1 := by rw [hj1, Nat.mul_div_right _ hd]
    have hm : (j + 1) % d = 0 := by rw [hj1, Nat.mul_mod_right]
    have hii : i.val ≤ j % d := Nat.le_of_lt_succ (i.isLt.trans_eq hrd.symm)
    by_cases hi : i.val < j % d
    · simp [axisDepth, hq, hm, hi, ne_of_lt hi]
    · have hie : i.val = j % d := le_antisymm hii (Nat.le_of_not_gt hi)
      simp [axisDepth, hq, hm, hie]

theorem axisDepth_monotone (d : ℕ) (hd : 0 < d) (i : Fin d) :
    Monotone (fun j => axisDepth d j i) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [axisDepth_succ d j hd i]
  exact Nat.le_add_right _ _

theorem intervalIndex_double (N : ℕ) (hN : 0 < N) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (intervalIndex (2 * N) (by omega) x).val / 2 = (intervalIndex N hN x).val := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hx1 : x = 1
  · subst x
    simp only [intervalIndex, mul_one, Nat.floor_natCast,
      min_eq_right (Nat.sub_le N 1), min_eq_right (Nat.sub_le (2 * N) 1)]
    omega
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hprod : 0 ≤ (N : ℝ) * x := mul_nonneg hNr.le hx.1
    have hlt : Nat.floor ((N : ℝ) * x) < N :=
      (Nat.floor_lt hprod).mpr (by nlinarith)
    have hprod2 : 0 ≤ (2 * N : ℕ) * (x : ℝ) := mul_nonneg (Nat.cast_nonneg _) hx.1
    have hlt2 : Nat.floor (((2 * N : ℕ) : ℝ) * x) < 2 * N :=
      (Nat.floor_lt hprod2).mpr (by push_cast; nlinarith)
    simp only [intervalIndex, min_eq_left (by omega : Nat.floor ((N : ℝ) * x) ≤ N - 1),
      min_eq_left (by omega : Nat.floor (((2 * N : ℕ) : ℝ) * x) ≤ 2 * N - 1)]
    have he : (((2 * N : ℕ) : ℝ) * x) = ((N : ℝ) * x) * (2 : ℕ) := by push_cast; ring
    rw [he, Nat.mul_cast_floor_div_cancel (by norm_num : (2 : ℕ) ≠ 0)]

def dyadicParentCell {d j : ℕ} (hd : 0 < d) (c : DyadicCell d (j + 1)) : DyadicCell d j :=
  fun i => ⟨(c i).val / 2 ^ (if i.val = j % d then 1 else 0), by
    have hpow : 2 ^ axisDepth d (j + 1) i =
        2 ^ axisDepth d j i * 2 ^ (if i.val = j % d then 1 else 0) := by
      rw [axisDepth_succ d j hd i, pow_add]
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [hpow] using (c i).isLt⟩

theorem dyadicParentCell_selection (d j : ℕ) (hd : 0 < d) (x : Covariate d)
    (hx : x ∈ cube d) :
    dyadicParentCell hd (dyadicSelection d (j + 1) x) = dyadicSelection d j x := by
  funext i
  apply Fin.ext
  change (intervalIndex (2 ^ axisDepth d (j + 1) i) _ (x i)).val /
      2 ^ (if i.val = j % d then 1 else 0) = (intervalIndex (2 ^ axisDepth d j i) _ (x i)).val
  simp only [intervalIndex]
  by_cases hi : i.val = j % d
  · simp only [axisDepth_succ d j hd i, ite_eq_left hi, pow_succ, pow_zero, one_mul]
    simpa only [intervalIndex, mul_comm] using
      intervalIndex_double (2 ^ axisDepth d j i) (by positivity) (x i) (hx i)
  · simp only [axisDepth_succ d j hd i, ite_eq_right hi, add_zero, pow_zero, Nat.div_one]

theorem dyadicPartitionCell_refinement {d j : ℕ} (hd : 0 < d) (c : DyadicCell d (j + 1)) :
    dyadicPartitionCell c ⊆ dyadicPartitionCell (dyadicParentCell hd c) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have he := dyadicParentCell_selection d j hd x hx.1
  have hs : dyadicSelection d (j + 1) x = c := hx.2
  rw [hs] at he
  exact he.symm

end RoughRegime.Model
