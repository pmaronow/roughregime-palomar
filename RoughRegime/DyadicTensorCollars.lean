module

public import RoughRegime.DyadicTensor


@[expose] public section
/-! Actual cube measure of all level/coordinate digit collars. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RoughRegime.DyadicDigits

def bareCollar (a : ℕ) (γ : ℝ) : Set ℝ :=
  {y | ∃ z : ℤ, |(2 : ℝ) ^ a * y - z| < γ}

theorem bareCollar_measurable (a : ℕ) (γ : ℝ) : MeasurableSet (bareCollar a γ) := by
  unfold bareCollar
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro z
  exact measurableSet_lt ((measurable_const.mul measurable_id).sub measurable_const).abs measurable_const

theorem bareCollar_probability_le (a : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    unitUniform (bareCollar a γ) ≤ ENNReal.ofReal (2 * γ) := by
  unfold unitUniform
  rw [Measure.restrict_apply' measurableSet_Icc]
  have he : bareCollar a γ ∩ Icc (0 : ℝ) 1 = integerCollar (2 ^ a) γ := by
    ext y
    simp only [bareCollar, integerCollar, mem_inter_iff, mem_ofPred_eq,
      Nat.cast_pow, Nat.cast_ofNat]
    exact and_comm
  rw [he]
  exact dyadicCollar_volume_le a γ hγ

/-- A point is bad if any scaled coordinate lies in its transition collar. -/
def cubeCollar {ι : Type*} (d : ℕ) (a : ι → ℕ) (q : ι → Fin d) (γ : ι → ℝ) :
    Set (Fin d → ℝ) := {x | ∃ i, x (q i) ∈ bareCollar (a i) (γ i)}

theorem cubeCollar_measurable {ι : Type*} [Fintype ι]
    (d : ℕ) (a : ι → ℕ) (q : ι → Fin d) (γ : ι → ℝ) :
    MeasurableSet (cubeCollar d a q γ) := by
  unfold cubeCollar
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  exact (bareCollar_measurable (a i) (γ i)).preimage (measurable_pi_apply (q i))

/-- The actual d-dimensional collar measure has the exact source constant2. -/
theorem cubeCollar_probability_le {ι : Type*} [Fintype ι]
    (d : ℕ) (a : ι → ℕ) (q : ι → Fin d) (γ : ι → ℝ) (hγ : ∀ i, 0 ≤ γ i) :
    cubeUniform d (cubeCollar d a q γ) ≤ ENNReal.ofReal (2 * ∑ i, γ i) := by
  classical
  have he : cubeCollar d a q γ =
      ⋃ i ∈ (Finset.univ : Finset ι), (fun x : Fin d → ℝ => x (q i)) ⁻¹' bareCollar (a i) (γ i) := by
    ext x
    simp [cubeCollar]
  have hi (i : ι) : cubeUniform d ((fun x : Fin d → ℝ => x (q i)) ⁻¹' bareCollar (a i) (γ i)) ≤
      ENNReal.ofReal (2 * γ i) := by
    have hm := measurePreserving_eval (fun _ : Fin d => unitUniform) (q i)
    rw [← Measure.map_apply (measurable_pi_apply (q i)) (bareCollar_measurable (a i) (γ i))]
    change (Measure.map (Function.eval (q i)) (Measure.pi (fun _ : Fin d => unitUniform)))
      (bareCollar (a i) (γ i)) ≤ _
    rw [hm.map_eq]
    exact bareCollar_probability_le (a i) (γ i) (hγ i)
  rw [he]
  calc
    _ ≤ ∑ i, cubeUniform d ((fun x : Fin d → ℝ => x (q i)) ⁻¹' bareCollar (a i) (γ i)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (2 * γ i) := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by norm_num) (hγ i)),
        Finset.mul_sum]

/-- Quantitative finite inverse-square bound used for level widths and gate deficits. -/
theorem inverse_square_sum_le_two (J : ℕ) :
    (∑ b ∈ Finset.range J, (1 : ℝ) / ((b : ℝ) + 1) ^ 2) ≤ 2 := by
  have hs (J : ℕ) :
      (∑ b ∈ Finset.range (J + 1), (1 : ℝ) / ((b : ℝ) + 1) ^ 2) ≤
        2 - 1 / ((J : ℝ) + 1) := by
    induction J with
    | zero => norm_num
    | succ J ih =>
      rw [Finset.sum_range_succ]
      have hp : 0 < (J : ℝ) + 1 := by positivity
      have hq : 0 < (J : ℝ) + 2 := by positivity
      have hstep : 1 / ((J : ℝ) + 2) ^ 2 ≤
          1 / ((J : ℝ) + 1) - 1 / ((J : ℝ) + 2) := by
        apply (le_sub_iff_add_le).mpr
        field_simp
        nlinarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
      have he : (J : ℝ) + 1 + 1 = (J : ℝ) + 2 := by ring
      simp only [Nat.cast_add, Nat.cast_one, he] at *
      linarith
  cases J with
  | zero => simp
  | succ J =>
    have h := hs J
    have hp : 0 ≤ 1 / ((J : ℝ) + 1) := by positivity
    linarith

theorem cubeCollar_measureReal_le {ι : Type*} [Fintype ι]
    (d : ℕ) (a : ι → ℕ) (q : ι → Fin d) (γ : ι → ℝ) (hγ : ∀ i, 0 ≤ γ i) :
    (cubeUniform d).real (cubeCollar d a q γ) ≤ 2 * ∑ i, γ i := by
  have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
    (cubeCollar_probability_le d a q γ hγ)
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _ => hγ i)))] at h
  exact h

/-- The chosen inverse-square level widths have total at most2d gammaStar. -/
theorem levelWidth_sum_le (J d : ℕ) (γstar : ℝ) (hγ : 0 ≤ γstar) :
    (∑ i : Fin J × Fin d, γstar / ((i.1 : ℝ) + 1) ^ 2) ≤ 2 * d * γstar := by
  have he : (∑ i : Fin J × Fin d, γstar / ((i.1 : ℝ) + 1) ^ 2) =
      ((d : ℝ) * γstar) * ∑ b ∈ Finset.range J, (1 : ℝ) / ((b : ℝ) + 1) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have ht (b : Fin J) : (d : ℝ) * (γstar / ((b : ℝ) + 1) ^ 2) =
        ((d : ℝ) * γstar) * (1 / ((b : ℝ) + 1) ^ 2) := by ring
    simp_rw [ht]
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun b : ℕ => (1 : ℝ) / ((b : ℝ) + 1) ^ 2) J]
  rw [he]
  have h := mul_le_mul_of_nonneg_left (inverse_square_sum_le_two J)
    (mul_nonneg (Nat.cast_nonneg d) hγ)
  nlinarith

/-- With the source gammaStar choice, the actual collar costs at mostI/4. -/
theorem cubeCollar_level_budget_le_quarter (J d : ℕ) (hd : 0 < d)
    (a : Fin J × Fin d → ℕ) (q : Fin J × Fin d → Fin d)
    (γstar I : ℝ) (hγ : 0 ≤ γstar) (hγI : γstar ≤ I / (16 * d)) :
    (cubeUniform d).real (cubeCollar d a q
      (fun i : Fin J × Fin d => γstar / ((i.1 : ℝ) + 1) ^ 2)) ≤ I / 4 := by
  have hwidth (i : Fin J × Fin d) : 0 ≤ γstar / ((i.1 : ℝ) + 1) ^ 2 := by positivity
  have hc := cubeCollar_measureReal_le d a q _ hwidth
  have hs := levelWidth_sum_le J d γstar hγ
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  have hb := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hdr)).mp hγI
  nlinarith

end RoughRegime.DyadicDigits
