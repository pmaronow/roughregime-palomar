module

public import RoughRegime.DyadicChildren


@[expose] public section
/-! Actual coordinate identity for the nested affine child transports. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Model

theorem rectangleCoords_comp {d : ℕ} (o p : Covariate d) (s t : Fin d → ℝ)
    (hs : ∀ i, s i ≠ 0) (x : Covariate d) :
    rectangleCoords p t (rectangleCoords o s x) =
      rectangleCoords (rectangleEmbed o s p) (fun i => s i * t i) x := by
  ext i
  simp only [rectangleCoords, rectangleEmbed, rectangleScale_apply, PiLp.sub_apply,
    PiLp.add_apply, mul_inv_rev]
  calc
    _ = (t i)⁻¹ * (s i)⁻¹ * (x i - o i - s i * p i) := by
      field_simp [hs i]
    _ = _ := by ring

theorem dyadicChildSides {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) :
    dyadicSides (dyadicChildCell hd c b) =
      fun i => dyadicSides c i * splitSides (dyadicSplitAxis d j hd) i := by
  funext i
  have hie : i = dyadicSplitAxis d j hd ↔ i.val = j % d := Fin.ext_iff
  by_cases hi : i.val = j % d
  · simp only [dyadicSides, axisDepth_succ d j hd i, ite_eq_left hi, splitSides,
      ite_eq_left (hie.mpr hi), pow_succ]
    ring
  · simp only [dyadicSides, axisDepth_succ d j hd i, ite_eq_right hi, add_zero, splitSides,
      ite_eq_right (mt hie.mp hi), mul_one]

theorem dyadicChildOrigin {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) :
    dyadicOrigin (dyadicChildCell hd c b) =
      rectangleEmbed (dyadicOrigin c) (dyadicSides c) (splitOrigin (dyadicSplitAxis d j hd) b) := by
  ext i
  have hie : i = dyadicSplitAxis d j hd ↔ i.val = j % d := Fin.ext_iff
  by_cases hi : i.val = j % d
  · simp only [dyadicOrigin, dyadicChildCell, axisDepth_succ d j hd i, ite_eq_left hi, splitOrigin,
      ite_eq_left (hie.mpr hi), rectangleEmbed, dyadicSides, pow_succ, PiLp.add_apply,
      rectangleScale_apply, WithLp.ofLp_toLp, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · simp only [dyadicOrigin, dyadicChildCell, axisDepth_succ d j hd i, ite_eq_right hi, add_zero, splitOrigin,
      ite_eq_right (mt hie.mp hi), rectangleEmbed, dyadicSides, PiLp.add_apply,
      rectangleScale_apply, WithLp.ofLp_toLp, mul_zero, add_zero]

theorem dyadicChildCoords {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) (x : Covariate d) :
    rectangleCoords (splitOrigin (dyadicSplitAxis d j hd) b) (splitSides (dyadicSplitAxis d j hd))
      (rectangleCoords (dyadicOrigin c) (dyadicSides c) x) =
      rectangleCoords (dyadicOrigin (dyadicChildCell hd c b)) (dyadicSides (dyadicChildCell hd c b)) x := by
  rw [dyadicChildOrigin, dyadicChildSides]
  exact rectangleCoords_comp _ _ _ _ (fun i => (dyadicSides_pos c i).ne') x

theorem dyadicChildCoords_mem {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) (b : Bool) (x : Covariate d) :
    rectangleCoords (dyadicOrigin c) (dyadicSides c) x ∈ splitRectangle (dyadicSplitAxis d j hd) b ↔
      x ∈ dyadicRectangle (dyadicChildCell hd c b) := by
  rw [← dyadicChild_preimage hd c b]
  simp only [mem_preimage, rectangleEmbed_coords _ _ (fun i => (dyadicSides_pos c i).ne')]

theorem dyadicChildBasisFunction_child {d j : ℕ} (hd : 0 < d) (k : ℕ) (c : DyadicCell d j)
    (b : Bool) (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) (x : Covariate d) :
    dyadicChildBasisFunction hd k c (b, i) x =
      (dyadicRectangle (dyadicChildCell hd c b)).indicator (fun x => Real.sqrt 2 *
        polynomialEvaluation (basisPolynomial d k i)
          (rectangleCoords (dyadicOrigin (dyadicChildCell hd c b))
            (dyadicSides (dyadicChildCell hd c b)) x)) x := by
  by_cases hx : x ∈ dyadicRectangle (dyadicChildCell hd c b)
  · have hr := (dyadicChildCoords_mem hd c b x).mpr hx
    simp only [dyadicChildBasisFunction, splitBasisFunction, indicator_of_mem hr, indicator_of_mem hx]
    rw [dyadicChildCoords]
  · have hr := mt (dyadicChildCoords_mem hd c b x).mp hx
    simp [dyadicChildBasisFunction, splitBasisFunction, hx, hr]

end RoughRegime.Model
