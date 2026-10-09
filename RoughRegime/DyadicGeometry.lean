module

public import RoughRegime.PolynomialLp


@[expose] public section
/-! Actual cyclic dyadic rectangles and the source cardinality and volume. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

def axisDepth (d j : ℕ) (i : Fin d) : ℕ := j / d + if i.val < j % d then 1 else 0

abbrev DyadicCell (d j : ℕ) := (i : Fin d) → Fin (2 ^ axisDepth d j i)

lemma sum_axis_indicator (d r : ℕ) :
    (∑ i : Fin d, if i.val < r then 1 else 0) = min r d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    by_cases h : r ≤ d
    · simp [Nat.min_eq_left h, Nat.min_eq_left (h.trans (Nat.le_succ _)), Nat.not_lt.mpr h]
    · have hd : d < r := Nat.lt_of_not_ge h
      simp [hd, Nat.min_eq_right hd.le]

theorem axisDepth_sum (d j : ℕ) (hd : 0 < d) : (∑ i : Fin d, axisDepth d j i) = j := by
  unfold axisDepth
  rw [Finset.sum_add_distrib, sum_axis_indicator]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.min_eq_left (Nat.mod_lt j hd).le]
  exact Nat.div_add_mod j d

theorem dyadicCell_card (d j : ℕ) (hd : 0 < d) : Fintype.card (DyadicCell d j) = 2 ^ j := by
  simp only [DyadicCell, Fintype.card_pi, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, axisDepth_sum d j hd]

def dyadicRectangle {d j : ℕ} (c : DyadicCell d j) : Set (Covariate d) :=
  {x | ∀ i, x i ∈ Icc ((c i : ℝ) / (2 : ℝ) ^ axisDepth d j i)
    (((c i : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j i)}

theorem dyadicRectangle_measurable {d j : ℕ} (c : DyadicCell d j) :
    MeasurableSet (dyadicRectangle c) := by
  have he : dyadicRectangle c = WithLp.ofLp ⁻¹' Icc
      (fun i => (c i : ℝ) / (2 : ℝ) ^ axisDepth d j i)
      (fun i => ((c i : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j i) := by
    ext x
    simp only [dyadicRectangle, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem dyadicRectangle_subset_cube {d j : ℕ} (c : DyadicCell d j) :
    dyadicRectangle c ⊆ cube d := by
  intro x hx i
  have hN : (0 : ℝ) < (2 : ℝ) ^ axisDepth d j i := by positivity
  have hci : (c i : ℝ) + 1 ≤ (2 : ℝ) ^ axisDepth d j i := by
    exact_mod_cast (c i).isLt
  exact ⟨(div_nonneg (Nat.cast_nonneg _) hN.le).trans (hx i).1,
    (hx i).2.trans ((div_le_one hN).mpr hci)⟩

theorem dyadicRectangle_volume {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    volume (dyadicRectangle c) = ENNReal.ofReal (1 / (2 : ℝ) ^ j) := by
  have he : dyadicRectangle c = WithLp.ofLp ⁻¹' Icc
      (fun i => (c i : ℝ) / (2 : ℝ) ^ axisDepth d j i)
      (fun i => ((c i : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j i) := by
    ext x
    simp only [dyadicRectangle, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  have hdiff (i : Fin d) : ((c i : ℝ) + 1) / (2 : ℝ) ^ axisDepth d j i -
      (c i : ℝ) / (2 : ℝ) ^ axisDepth d j i = 1 / (2 : ℝ) ^ axisDepth d j i := by ring
  simp only [hdiff]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity), Finset.prod_div_distrib,
    Finset.prod_const_one, Finset.prod_pow_eq_pow_sum, axisDepth_sum d j hd]

theorem dyadicRectangle_cubeVolume {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j) :
    cubeVolume d (dyadicRectangle c) = ENNReal.ofReal (1 / (2 : ℝ) ^ j) := by
  rw [cubeVolume, Measure.restrict_apply (dyadicRectangle_measurable c),
    inter_eq_left.mpr (dyadicRectangle_subset_cube c)]
  exact dyadicRectangle_volume hd c

theorem axisDepth_lower (d j : ℕ) (i : Fin d) : j / d ≤ axisDepth d j i := by
  unfold axisDepth
  split_ifs <;> omega

theorem axisDepth_upper (d j : ℕ) (i : Fin d) : axisDepth d j i ≤ j / d + 1 := by
  unfold axisDepth
  split_ifs <;> omega

theorem dyadicRectangle_coordinate_distance {d j : ℕ} (c : DyadicCell d j)
    (x y : Covariate d) (hx : x ∈ dyadicRectangle c) (hy : y ∈ dyadicRectangle c)
    (i : Fin d) : |x i - y i| ≤ 1 / (2 : ℝ) ^ axisDepth d j i := by
  have hxi := hx i
  have hyi := hy i
  simp only [add_div] at hxi hyi
  apply abs_le.mpr
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

theorem dyadicRectangle_diameter_floor {d j : ℕ} (c : DyadicCell d j)
    (x y : Covariate d) (hx : x ∈ dyadicRectangle c) (hy : y ∈ dyadicRectangle c) :
    ‖x - y‖ ≤ Real.sqrt d / (2 : ℝ) ^ (j / d) := by
  let S : ℝ := 1 / (2 : ℝ) ^ (j / d)
  have hS : 0 ≤ S := by positivity
  have hb (i : Fin d) : ‖(x - y) i‖ ≤ S := by
    change |x i - y i| ≤ S
    apply (dyadicRectangle_coordinate_distance c x y hx hy i).trans
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (axisDepth_lower d j i))
  have hs : ‖x - y‖ ^ 2 ≤ (d : ℝ) * S ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ : Fin d, S ^ 2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hb i) 2)
      _ = _ := by simp
  have hsqrt : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
  have hs2 : ‖x - y‖ ^ 2 ≤ (Real.sqrt d * S) ^ 2 := by rw [mul_pow, hsqrt]; exact hs
  have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hS)).mp hs2
  simpa only [S, div_eq_mul_inv, one_mul] using h

theorem dyadic_side_floor_le (d j : ℕ) (hd : 0 < d) :
    1 / (2 : ℝ) ^ (j / d) ≤ 2 * (2 : ℝ) ^ (-(j : ℝ) / d) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : ((j % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt j hd
  have he : (d : ℝ) * (j / d : ℕ) + ((j % d : ℕ) : ℝ) = j := by
    exact_mod_cast Nat.div_add_mod j d
  have hq : (j : ℝ) / d ≤ (j / d : ℕ) + 1 := by
    apply (div_le_iff₀ hdr).mpr
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by simp only [neg_div]; linarith only [hq] :
      -((j / d : ℕ) : ℝ) ≤ 1 + (-(j : ℝ) / d))
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast] at hp
  simpa only [one_div] using hp

theorem dyadicRectangle_diameter {d j : ℕ} (hd : 0 < d) (c : DyadicCell d j)
    (x y : Covariate d) (hx : x ∈ dyadicRectangle c) (hy : y ∈ dyadicRectangle c) :
    ‖x - y‖ ≤ 2 * Real.sqrt d * (2 : ℝ) ^ (-(j : ℝ) / d) := by
  apply (dyadicRectangle_diameter_floor c x y hx hy).trans
  have h := mul_le_mul_of_nonneg_left (dyadic_side_floor_le d j hd) (Real.sqrt_nonneg d)
  convert h using 1 <;> ring

end RoughRegime.Model
