module

public import RoughRegime.DyadicTransport


@[expose] public section
/-! The transported halves are exactly the two actual cyclic dyadic children. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

def dyadicChildCell {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) : DyadicCell d (j + 1) :=
  fun i => ⟨if i.val = j % d then 2 * (c i).val + b.toNat else (c i).val, by
    have hc := (c i).isLt
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    rw [axisDepth_succ d j hd i]
    by_cases hi : i.val = j % d
    · simp only [ite_eq_left hi, pow_succ]
      omega
    · simpa only [ite_eq_right hi, add_zero] using hc⟩

theorem dyadicParentCell_child {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) :
    dyadicParentCell hd (dyadicChildCell hd c b) = c := by
  funext i
  apply Fin.ext
  simp only [dyadicParentCell, dyadicChildCell]
  by_cases hi : i.val = j % d
  · simp only [ite_eq_left hi, pow_one]
    have hb : b.toNat < 2 := by cases b <;> decide
    omega
  · simp [hi]

theorem dyadicChild_preimage {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) :
    rectangleEmbed (dyadicOrigin c) (dyadicSides c) ⁻¹' dyadicRectangle (dyadicChildCell hd c b) =
      splitRectangle (dyadicSplitAxis d j hd) b := by
  classical
  ext x
  simp only [mem_preimage, dyadicRectangle, splitRectangle, rectangle, mem_ofPred_eq]
  apply forall_congr'
  intro i
  have hN : (0 : ℝ) < (2 : ℝ) ^ axisDepth d j i := by positivity
  have he : rectangleEmbed (dyadicOrigin c) (dyadicSides c) x i =
      ((c i : ℝ) + x i) / (2 : ℝ) ^ axisDepth d j i := by
    simp [rectangleEmbed, dyadicOrigin, dyadicSides]
    ring
  rw [he]
  have hie : i = dyadicSplitAxis d j hd ↔ i.val = j % d := Fin.ext_iff
  by_cases hi : i.val = j % d
  · have hir := hie.mpr hi
    simp only [dyadicChildCell, ite_eq_left hi, axisDepth_succ d j hd i, pow_succ,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, splitOrigin, splitSides,
      WithLp.ofLp_toLp, ite_eq_left hir, mem_Icc]
    constructor
    · intro hx
      have h1 := (div_le_div_iff₀ (by positivity : (0 : ℝ) < _ * 2) hN).mp hx.1
      have h2 := (div_le_div_iff₀ hN (by positivity : (0 : ℝ) < _ * 2)).mp hx.2
      constructor <;> nlinarith
    · intro hx
      constructor
      · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < _ * 2) hN).mpr
        nlinarith [hx.1]
      · apply (div_le_div_iff₀ hN (by positivity : (0 : ℝ) < _ * 2)).mpr
        nlinarith [hx.2]
  · have hir : i ≠ dyadicSplitAxis d j hd := fun h => hi (hie.mp h)
    simp only [dyadicChildCell, ite_eq_right hi, axisDepth_succ d j hd i, add_zero,
      splitOrigin, splitSides, WithLp.ofLp_toLp, ite_eq_right hir, zero_add, mem_Icc]
    rw [div_le_div_iff₀ hN hN, div_le_div_iff₀ hN hN]
    constructor <;> intro hx <;> constructor <;> nlinarith [hx.1, hx.2]

end RoughRegime.Model
