module

public import Mathlib


@[expose] public section
/-! Exact measure bounds for transition collars of dyadic digits. The estimates
come from actual Lebesgue interval lengths and finite unions, not a supplied
collar-volume hypothesis. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RoughRegime.DyadicDigits

/-- A collar of width gamma in the scaled coordinate around every integer. -/
def integerCollar (N : ℕ) (γ : ℝ) : Set ℝ :=
  {y | y ∈ Icc (0 : ℝ) 1 ∧ ∃ z : ℤ, |(N : ℝ) * y - z| < γ}

private def cellCollarCover (N : ℕ) (γ : ℝ) (k : ℕ) : Set ℝ :=
  Icc ((k : ℝ) / N) (((k : ℝ) + γ) / N) ∪
    Icc (((k : ℝ) + 1 - γ) / N) (((k : ℝ) + 1) / N)

private theorem collar_cover (N : ℕ) (γ : ℝ) (hN : 0 < N) :
    integerCollar N γ ⊆
      (⋃ k ∈ Finset.range N, cellCollarCover N γ k) ∪ {1} := by
  intro y hy
  rcases hy with ⟨hy, z, hz⟩
  by_cases hy1 : y = 1
  · exact Or.inr hy1
  left
  let j : ℤ := Int.floor ((N : ℝ) * y)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (mul_nonneg hNr.le hy.1)
  have hjq : (j : ℝ) ≤ (N : ℝ) * y := Int.floor_le _
  have hqj : (N : ℝ) * y < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hylt : y < 1 := lt_of_le_of_ne hy.2 hy1
  have hjN : j < (N : ℤ) := by
    have hh : (j : ℝ) < (N : ℝ) := lt_of_le_of_lt hjq (by nlinarith)
    exact_mod_cast hh
  let k := j.toNat
  have hkN : k < N := (Int.toNat_lt hj0).mpr hjN
  have hkj : (k : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hj0
  apply mem_iUnion.2
  refine ⟨k, mem_iUnion.2 ⟨Finset.mem_range.mpr hkN, ?_⟩⟩
  simp only [cellCollarCover, mem_union, mem_Icc]
  rcases le_or_gt z j with hlow | hhigh
  · left
    have hzr : (z : ℝ) ≤ k := by rw [hkj]; exact_mod_cast hlow
    have hz' := (abs_lt.mp hz).2
    constructor
    · apply (div_le_iff₀ hNr).mpr
      rw [hkj]
      simpa only [mul_comm] using hjq
    · apply (le_div_iff₀ hNr).mpr
      nlinarith
  · right
    have hzj : j + 1 ≤ z := by omega
    have hzr : (k : ℝ) + 1 ≤ z := by rw [hkj]; exact_mod_cast hzj
    have hz' := (abs_lt.mp hz).1
    constructor
    · apply (div_le_iff₀ hNr).mpr
      nlinarith
    · apply (le_div_iff₀ hNr).mpr
      rw [hkj]
      simpa only [mul_comm] using hqj.le

private theorem cellCollarCover_volume_le (N : ℕ) (γ : ℝ) (k : ℕ)
    (hγ : 0 ≤ γ) :
    volume (cellCollarCover N γ k) ≤ ENNReal.ofReal (2 * γ / N) := by
  have hgn : 0 ≤ γ / (N : ℝ) := div_nonneg hγ (Nat.cast_nonneg _)
  calc
    volume (cellCollarCover N γ k) ≤
        volume (Icc ((k : ℝ) / N) (((k : ℝ) + γ) / N)) +
        volume (Icc (((k : ℝ) + 1 - γ) / N) (((k : ℝ) + 1) / N)) :=
      measure_union_le _ _
    _ = ENNReal.ofReal (γ / (N : ℝ)) + ENNReal.ofReal (γ / (N : ℝ)) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      congr 1 <;> congr 1 <;> ring
    _ = ENNReal.ofReal (2 * γ / N) := by
      rw [← ENNReal.ofReal_add hgn hgn]
      congr 1
      ring

/-- Per-level collar loss is at most 2 gamma, independently of the frequency.
This stronger statement does not need the smoothing restriction gamma≤1/4. -/
theorem integerCollar_volume_le (N : ℕ) (γ : ℝ) (hN : 0 < N) (hγ : 0 ≤ γ) :
    volume (integerCollar N γ) ≤ ENNReal.ofReal (2 * γ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    volume (integerCollar N γ) ≤
        volume ((⋃ k ∈ Finset.range N, cellCollarCover N γ k) ∪ {1}) :=
      measure_mono (collar_cover N γ hN)
    _ ≤ volume (⋃ k ∈ Finset.range N, cellCollarCover N γ k) + volume {1} :=
      measure_union_le _ _
    _ = volume (⋃ k ∈ Finset.range N, cellCollarCover N γ k) := by simp
    _ ≤ ∑ k ∈ Finset.range N, volume (cellCollarCover N γ k) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, ENNReal.ofReal (2 * γ / (N : ℝ)) :=
      Finset.sum_le_sum (fun k _ => cellCollarCover_volume_le N γ k hγ)
    _ = ENNReal.ofReal (2 * γ) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      field_simp

/-- The source's collar bound for the a-th binary digit. -/
theorem dyadicCollar_volume_le (a : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    volume (integerCollar (2 ^ a) γ) ≤ ENNReal.ofReal (2 * γ) :=
  integerCollar_volume_le _ _ (pow_pos (by norm_num) _) hγ

/-- Finite unions across levels have the source's sum of collar widths. -/
theorem dyadicCollars_volume_le (S : Finset ℕ) (γ : ℕ → ℝ)
    (hγ : ∀ a ∈ S, 0 ≤ γ a) :
    volume (⋃ a ∈ S, integerCollar (2 ^ a) (γ a)) ≤
      ENNReal.ofReal (2 * ∑ a ∈ S, γ a) := by
  calc
    _ ≤ ∑ a ∈ S, volume (integerCollar (2 ^ a) (γ a)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ S, ENNReal.ofReal (2 * γ a) :=
      Finset.sum_le_sum (fun a ha => dyadicCollar_volume_le a (γ a) (hγ a ha))
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a ha => mul_nonneg (by norm_num) (hγ a ha)),
        Finset.mul_sum]

end RoughRegime.DyadicDigits
