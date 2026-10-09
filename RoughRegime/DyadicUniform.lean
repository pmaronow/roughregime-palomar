module

public import RoughRegime.DyadicCollars


@[expose] public section
/-! Actual uniform dyadic cell probabilities and nesting of binary digits. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RoughRegime.DyadicDigits

def scaledFloor (a : ℕ) (y : ℝ) : ℤ := Int.floor ((2 : ℝ) ^ a * y)

def digit (a : ℕ) (y : ℝ) : ℤ := scaledFloor a y % 2

/-- The full fiber of a scaled floor function is the corresponding cell. -/
theorem scaled_floor_fiber (N : ℕ) (hN : 0 < N) (k : ℤ) :
    {y : ℝ | Int.floor ((N : ℝ) * y) = k} =
      Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  ext y
  simp only [mem_ofPred_eq, Int.floor_eq_iff, mem_Ico]
  constructor
  · intro hy
    constructor
    · exact (div_le_iff₀ hNr).mpr (by simpa only [mul_comm] using hy.1)
    · exact (lt_div_iff₀ hNr).mpr (by simpa only [mul_comm] using hy.2)
  · intro hy
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hNr).mp hy.1
    · simpa only [mul_comm] using (lt_div_iff₀ hNr).mp hy.2

/-- Every interior cell has exactly mass 1/N under the unit uniform law. -/
theorem scaled_floor_cell_probability (N : ℕ) (hN : 0 < N) (k : ℤ)
    (hk0 : 0 ≤ k) (hkN : k < (N : ℤ)) :
    (volume.restrict (Icc (0 : ℝ) 1))
      {y : ℝ | Int.floor ((N : ℝ) * y) = k} = ENNReal.ofReal (1 / (N : ℝ)) := by
  rw [scaled_floor_fiber N hN k, Measure.restrict_apply measurableSet_Ico]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hkr : 0 ≤ (k : ℝ) := by exact_mod_cast hk0
  have hk1r : (k : ℝ) + 1 ≤ N := by
    have hk1 : k + 1 ≤ (N : ℤ) := by omega
    exact_mod_cast hk1
  have hsub : Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N) ⊆ Icc (0 : ℝ) 1 := by
    intro y hy
    constructor
    · exact (div_nonneg hkr hNr.le).trans hy.1
    · have hh : ((k : ℝ) + 1) / N ≤ 1 := (div_le_one hNr).mpr hk1r
      exact hy.2.le.trans hh
  rw [inter_eq_left.mpr hsub, Real.volume_Ico]
  congr 1
  ring

/-- The J-bit dyadic cell index is exactly uniform on 0,...,2^J-1. -/
theorem dyadic_cell_probability (J : ℕ) (k : ℤ)
    (hk0 : 0 ≤ k) (hkJ : k < (2 : ℤ) ^ J) :
    (volume.restrict (Icc (0 : ℝ) 1)) {y : ℝ | scaledFloor J y = k} =
      ENNReal.ofReal ((2 : ℝ) ^ (-(J : ℤ))) := by
  have hp : 0 < (2 : ℕ) ^ J := pow_pos (by norm_num) _
  have hkN : k < ((2 ^ J : ℕ) : ℤ) := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hkJ
  have h := scaled_floor_cell_probability (2 ^ J) hp k hk0 hkN
  simpa only [scaledFloor, Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast, one_div] using h

/-- Coarser cell indices are the exact integer quotients of finer indices. -/
theorem scaledFloor_nesting (a J : ℕ) (haJ : a ≤ J) (y : ℝ) :
    scaledFloor a y = scaledFloor J y / (2 : ℤ) ^ (J - a) := by
  have hpow : (2 : ℝ) ^ J = (2 : ℝ) ^ a * (2 : ℝ) ^ (J - a) := by
    rw [← pow_add, Nat.add_sub_of_le haJ]
  have hn : ((2 ^ (J - a) : ℕ) : ℝ) ≠ 0 := by positivity
  have harg : (2 : ℝ) ^ a * y = ((2 : ℝ) ^ J * y) / ((2 ^ (J - a) : ℕ) : ℝ) := by
    apply (eq_div_iff hn).mpr
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [hpow]
    ring
  unfold scaledFloor
  rw [harg, Int.floor_div_natCast]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- Each binary digit is a definite bit of the fine cell index. -/
theorem digit_nesting (a J : ℕ) (haJ : a ≤ J) (y : ℝ) :
    digit a y = (scaledFloor J y / (2 : ℤ) ^ (J - a)) % 2 := by
  unfold digit
  rw [scaledFloor_nesting a J haJ y]

/-- The finite cell's J binary bits, in order from least to most significant. -/
def cellBits (J : ℕ) (k : Fin (2 ^ J)) : Fin J → Bool :=
  fun i => k.val.testBit i.val

/-- The complete J-bit string identifies its cell, with no omitted strings. -/
theorem cellBits_bijective (J : ℕ) : Function.Bijective (cellBits J) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro k l hkl
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < J
    · exact congrFun hkl ⟨i, hi⟩
    · have hp : 2 ^ J ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hi)
      rw [Nat.testBit_eq_false_of_lt (k.isLt.trans_le hp),
        Nat.testBit_eq_false_of_lt (l.isLt.trans_le hp)]
  · simp

/-- Bits of the fine-cell index. On the unit interval these are the source
binary digits in reverse level order, as follows from `digit_nesting`. -/
def pointBits (J : ℕ) (y : ℝ) : Fin J → Bool :=
  fun i => (scaledFloor J y).toNat.testBit i.val

theorem scaledFloor_bounds (J : ℕ) (y : ℝ) (hy : y ∈ Ico (0 : ℝ) 1) :
    0 ≤ scaledFloor J y ∧ scaledFloor J y < (2 : ℤ) ^ J := by
  have hp : 0 < (2 : ℝ) ^ J := by positivity
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg hp.le hy.1)
  · apply Int.floor_lt.mpr
    push_cast
    nlinarith [hy.2]

/-- Exact probability of every complete binary string under Lebesgue's unit
uniform law; equivalently, all J digits are independent fair binary digits. -/
theorem pointBits_probability (J : ℕ) (b : Fin J → Bool) :
    (volume.restrict (Icc (0 : ℝ) 1)) {y : ℝ | pointBits J y = b} =
      ENNReal.ofReal ((2 : ℝ) ^ (-(J : ℤ))) := by
  obtain ⟨k, hk⟩ := (cellBits_bijective J).surjective b
  have hset : {y : ℝ | pointBits J y = b} ∩ Ico (0 : ℝ) 1 =
      {y : ℝ | scaledFloor J y = (k.val : ℤ)} ∩ Ico (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨hyb, hy⟩
      have hb := scaledFloor_bounds J y hy
      let ky : Fin (2 ^ J) := ⟨(scaledFloor J y).toNat,
        (Int.toNat_lt hb.1).mpr (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hb.2)⟩
      have hky : cellBits J ky = cellBits J k := by
        exact hyb.trans hk.symm
      have he := (cellBits_bijective J).injective hky
      have hn : (scaledFloor J y).toNat = k.val := congrArg Fin.val he
      have hf : scaledFloor J y = (k.val : ℤ) := by
        rw [← Int.toNat_of_nonneg hb.1, hn]
      exact ⟨hf, hy⟩
    · rintro ⟨hyf, hy⟩
      refine ⟨?_, hy⟩
      change pointBits J y = b
      unfold pointBits
      rw [hyf, Int.toNat_natCast]
      exact hk
  rw [← restrict_Ico_eq_restrict_Icc, Measure.restrict_apply' measurableSet_Ico,
    hset, ← Measure.restrict_apply' measurableSet_Ico, restrict_Ico_eq_restrict_Icc]
  apply dyadic_cell_probability J k.val
  · positivity
  · exact_mod_cast k.isLt

/-- Identification with the original levels 1,...,J (in reverse order). -/
theorem pointBits_eq_digit (J : ℕ) (y : ℝ) (hy : y ∈ Ico (0 : ℝ) 1) (i : Fin J) :
    pointBits J y i = decide (digit (J - i.val) y = 1) := by
  have hfloor : ((scaledFloor J y).toNat : ℤ) = scaledFloor J y :=
    Int.toNat_of_nonneg (scaledFloor_bounds J y hy).1
  unfold pointBits digit
  rw [Nat.testBit_eq_decide_div_mod_eq,
    scaledFloor_nesting (J - i.val) J (Nat.sub_le _ _) y]
  have hsub : J - (J - i.val) = i.val := by omega
  rw [hsub, ← hfloor]
  have hcast : (((scaledFloor J y).toNat / 2 ^ i.val % 2 : ℕ) : ℤ) =
      ((scaledFloor J y).toNat : ℤ) / (2 : ℤ) ^ i.val % 2 := by
    norm_cast
  rw [← hcast]
  norm_cast

theorem digit_zero_or_one (a : ℕ) (y : ℝ) : digit a y = 0 ∨ digit a y = 1 := by
  unfold digit
  have h0 := Int.emod_nonneg (scaledFloor a y) (by norm_num : (2 : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos (scaledFloor a y) (by norm_num : (0 : ℤ) < 2)
  omega

/-- Exact probability of each string of the paper's original binary digits.
The indexing is level J-i, so every level 1,...,J occurs exactly once. -/
theorem digits_probability (J : ℕ) (b : Fin J → Bool) :
    (volume.restrict (Icc (0 : ℝ) 1))
      {y : ℝ | (fun i : Fin J => decide (digit (J - i.val) y = 1)) = b} =
      ENNReal.ofReal ((2 : ℝ) ^ (-(J : ℤ))) := by
  have he : {y : ℝ | (fun i : Fin J => decide (digit (J - i.val) y = 1)) = b} ∩
      Ico (0 : ℝ) 1 = {y : ℝ | pointBits J y = b} ∩ Ico (0 : ℝ) 1 := by
    ext y
    by_cases hy : y ∈ Ico (0 : ℝ) 1
    · have hf : (fun i : Fin J => decide (digit (J - i.val) y = 1)) = pointBits J y := by
        funext i
        exact (pointBits_eq_digit J y hy i).symm
      simp only [mem_inter_iff, mem_ofPred_eq, hf]
    · simp only [mem_inter_iff, mem_ofPred_eq, hy, and_false]
  rw [← restrict_Ico_eq_restrict_Icc, Measure.restrict_apply' measurableSet_Ico,
    he, ← Measure.restrict_apply' measurableSet_Ico, restrict_Ico_eq_restrict_Icc]
  exact pointBits_probability J b

theorem pointBits_measurable (J : ℕ) : Measurable (pointBits J) := by
  exact (measurable_of_countable (fun z : ℤ => fun i : Fin J => z.toNat.testBit i.val)).comp
    ((measurable_const.mul measurable_id).floor)

end RoughRegime.DyadicDigits
