module

public import RoughRegime.UpperRates


@[expose] public section
/-! Dyadic variance sums and the uncapped degree rule. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.UpperParametric
open RoughRegime.UpperDegreeRules

lemma parentCells_positive (J : ℕ) (j : Fin (J + 1)) : 0 < (parentCells J j : ℝ) := by
  unfold parentCells
  split_ifs <;> positivity

lemma real_pow_rpow (a : ℝ) (ha : 0 ≤ a) (i : ℕ) (q : ℝ) :
    (a ^ i) ^ q = (a ^ q) ^ i := by
  rw [← Real.rpow_natCast_mul ha, mul_comm (i : ℝ), Real.rpow_mul_natCast ha]

lemma finite_geometric_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (J : ℕ) :
    (∑ i ∈ Finset.range J, q ^ i) ≤ (1 - q)⁻¹ := by
  have hs := hasSum_geometric_of_lt_one hq hq1
  simpa only [hs.tsum_eq] using hs.summable.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)

/-- The smoothness factors have a uniformly bounded dyadic sum. -/
theorem dyadic_smoothness_sum (J : ℕ) (q : ℝ) (hq : 0 < q) :
    (∑ j : Fin (J + 1), (parentCells J j : ℝ) ^ (-q)) ≤ 1 + (1 - (2 : ℝ) ^ (-q))⁻¹ := by
  have hbase : 0 < (2 : ℝ) ^ (-q) := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : (2 : ℝ) ^ (-q) < 1 := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.exp_lt_one_iff]
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith
  rw [Fin.sum_univ_succ]
  simp only [parentCells, Fin.val_zero, ite_true, ite_false, Nat.cast_one, Real.one_rpow,
    Fin.val_succ, Nat.add_one_ne_zero, Nat.add_sub_cancel,
    Nat.cast_pow, Nat.cast_ofNat, real_pow_rpow (2 : ℝ) (by norm_num)]
  rw [Fin.sum_univ_eq_sum_range]
  exact add_le_add le_rfl (finite_geometric_le _ hbase.le hbase1 J)

lemma sqrt_pow (a : ℝ) (ha : 0 ≤ a) (i : ℕ) : Real.sqrt (a ^ i) = Real.sqrt a ^ i := by
  simp_rw [Real.sqrt_eq_rpow]
  exact real_pow_rpow a ha i (1 / 2)

def sqrtResolutionConstant : ℝ := 1 + (Real.sqrt 2 - 1)⁻¹

/-- Sum of the square roots of all parent-cell counts is bounded by a constant
multiple of the square root of the terminal resolution. -/
theorem dyadic_sqrt_resolution_sum (J : ℕ) :
    (∑ j : Fin (J + 1), Real.sqrt (parentCells J j)) ≤
      sqrtResolutionConstant * Real.sqrt ((2 : ℝ) ^ J) := by
  have hr : 1 < Real.sqrt (2 : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
  have hden : 0 < Real.sqrt (2 : ℝ) - 1 := by linarith
  have hp : 1 ≤ Real.sqrt (2 : ℝ) ^ J := one_le_pow₀ hr.le
  rw [Fin.sum_univ_succ]
  simp only [parentCells, Fin.val_zero, ite_true, ite_false, Nat.cast_one, Real.sqrt_one,
    Fin.val_succ, Nat.add_one_ne_zero, Nat.add_sub_cancel,
    Nat.cast_pow, Nat.cast_ofNat, sqrt_pow (2 : ℝ) (by norm_num)]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hr.ne' J]
  unfold sqrtResolutionConstant
  have hb : (Real.sqrt 2 ^ J - 1) / (Real.sqrt 2 - 1) ≤ Real.sqrt 2 ^ J / (Real.sqrt 2 - 1) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  calc
    _ ≤ 1 + Real.sqrt 2 ^ J / (Real.sqrt 2 - 1) := add_le_add le_rfl hb
    _ ≤ Real.sqrt 2 ^ J + Real.sqrt 2 ^ J / (Real.sqrt 2 - 1) := add_le_add hp le_rfl
    _ = _ := by ring

lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hs := Real.sq_sqrt (add_nonneg ha hb)
  have ha2 := Real.sq_sqrt ha
  have hb2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The exact variance-envelope sum for uncapped levels is of parametric order
when the terminal resolution is at most a constant times `n`. -/
theorem dyadic_standard_deviation_sum_bound (J : ℕ) (Cv cK n q : ℝ)
    (hCv : 0 ≤ Cv) (hcK : 0 ≤ cK) (hn : 0 < n) (hq : 0 < q)
    (hterminal : (2 : ℝ) ^ J ≤ cK * n)
    (v : Fin (J + 1) → ℝ)
    (hv : ∀ j, v j ≤ Cv * (parentCells J j : ℝ) ^ (-2 * q) / n + 4 * Cv ^ 2 * parentCells J j / n ^ 2) :
    (∑ j : Fin (J + 1), Real.sqrt (v j)) ≤
      (Real.sqrt Cv * (1 + (1 - (2 : ℝ) ^ (-q))⁻¹) +
        2 * Cv * sqrtResolutionConstant * Real.sqrt cK) / Real.sqrt n := by
  have hnS : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hr2 : 1 < Real.sqrt (2 : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
  have hC : 0 ≤ sqrtResolutionConstant := by unfold sqrtResolutionConstant; positivity
  have hpoint (j : Fin (J + 1)) : Real.sqrt (v j) ≤
      Real.sqrt Cv / Real.sqrt n * (parentCells J j : ℝ) ^ (-q) +
        2 * Cv / n * Real.sqrt (parentCells J j) := by
    calc
      _ ≤ Real.sqrt (Cv * (parentCells J j : ℝ) ^ (-2 * q) / n + 4 * Cv ^ 2 * parentCells J j / n ^ 2) :=
        Real.sqrt_le_sqrt (hv j)
      _ ≤ Real.sqrt (Cv * (parentCells J j : ℝ) ^ (-2 * q) / n) +
        Real.sqrt (4 * Cv ^ 2 * parentCells J j / n ^ 2) := sqrt_add_le _ _ (by positivity) (by positivity)
      _ = _ := by
        have hp : (parentCells J j : ℝ) ^ (-2 * q) = ((parentCells J j : ℝ) ^ (-q)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (parentCells_positive J j).le]
          congr 1
          ring
        rw [hp, Real.sqrt_div (by positivity), Real.sqrt_mul hCv, Real.sqrt_sq_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos (parentCells_positive J j) _),
          Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
        norm_num [abs_of_nonneg hCv, abs_of_pos hn]
        ring
  have hsmooth := dyadic_smoothness_sum J q hq
  have hresolution := dyadic_sqrt_resolution_sum J
  have hroot : Real.sqrt ((2 : ℝ) ^ J) ≤ Real.sqrt cK * Real.sqrt n := by
    simpa only [Real.sqrt_mul hcK] using Real.sqrt_le_sqrt hterminal
  calc
    _ ≤ ∑ j : Fin (J + 1),
        (Real.sqrt Cv / Real.sqrt n * (parentCells J j : ℝ) ^ (-q) +
          2 * Cv / n * Real.sqrt (parentCells J j)) := Finset.sum_le_sum (fun j _ => hpoint j)
    _ = Real.sqrt Cv / Real.sqrt n * (∑ j : Fin (J + 1), (parentCells J j : ℝ) ^ (-q)) +
        2 * Cv / n * (∑ j : Fin (J + 1), Real.sqrt (parentCells J j)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.sqrt Cv / Real.sqrt n * (1 + (1 - (2 : ℝ) ^ (-q))⁻¹) +
        2 * Cv / n * (sqrtResolutionConstant * (Real.sqrt cK * Real.sqrt n)) := by
      apply add_le_add (mul_le_mul_of_nonneg_left hsmooth (by positivity))
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hresolution.trans (mul_le_mul_of_nonneg_left hroot hC)
    _ = _ := by
      have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
      field_simp
      linear_combination 2 * Cv * sqrtResolutionConstant * Real.sqrt cK * hs

def terminalLevel (cK n : ℝ) : ℕ := Nat.floor (Real.log (cK * n) / Real.log 2)

/-- The exact dyadic floor terminal resolution lies between `cK*n/2` and `cK*n`. -/
theorem terminalLevel_bounds (cK n : ℝ) (hcn : 1 ≤ cK * n) :
    cK * n / 2 < (2 : ℝ) ^ terminalLevel cK n ∧ (2 : ℝ) ^ terminalLevel cK n ≤ cK * n := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcnpos : 0 < cK * n := zero_lt_one.trans_le hcn
  have hratio : 0 ≤ Real.log (cK * n) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hcn) hlog.le
  have hlo := Nat.lt_floor_add_one (Real.log (cK * n) / Real.log 2)
  have hhi := Nat.floor_le hratio
  have hleft : Real.log (cK * n) < ((terminalLevel cK n : ℝ) + 1) * Real.log 2 := by
    exact (div_lt_iff₀ hlog).mp hlo
  have hright : (terminalLevel cK n : ℝ) * Real.log 2 ≤ Real.log (cK * n) :=
    (le_div_iff₀ hlog).mp hhi
  have hexp := Real.exp_lt_exp.mpr hleft
  have hexple := Real.exp_le_exp.mpr hright
  rw [Real.exp_log hcnpos] at hexp hexple
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexple
  have hrw : ((terminalLevel cK n : ℝ) + 1) * Real.log 2 =
      (terminalLevel cK n : ℝ) * Real.log 2 + Real.log 2 := by ring
  rw [hrw, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  exact ⟨(div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr hexp, hexple⟩

lemma parentCells_terminal_upper (J : ℕ) (j : Fin (J + 1)) :
    (parentCells J j : ℝ) ≤ 2 * (2 : ℝ) ^ J * Real.exp (-(levelDistance J j : ℝ) * Real.log 2) := by
  have hexp : Real.exp (-(levelDistance J j : ℝ) * Real.log 2) = ((2 : ℝ) ^ levelDistance J j)⁻¹ := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hexp]
  unfold parentCells levelDistance
  split_ifs with hj0
  · simp only [hj0, Nat.sub_zero, Nat.cast_one, pow_succ]
    have hpow : (2 : ℝ) ^ J ≠ 0 := by positivity
    field_simp
    exact le_rfl
  · have hJ : j.val - 1 + (J - j.val + 1) = J := by have := j.isLt; omega
    have hpow : (2 : ℝ) ^ J = (2 : ℝ) ^ (j.val - 1) * (2 : ℝ) ^ (J - j.val + 1) := by
      rw [← pow_add, hJ]
    rw [hpow]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    have hnonzero : (2 : ℝ) ^ (J - j.val + 1) ≠ 0 := by positivity
    rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hnonzero, mul_one]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (j.val - 1)]

lemma distance_exponential_bound (l : ℕ) :
    (l : ℝ) * Real.exp (-(l : ℝ) * Real.log 2) ≤ 1 := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hl : (l : ℝ) ≤ (2 : ℝ) ^ l := by exact_mod_cast (Nat.lt_two_pow_self (n := l)).le
  have hpow : 0 < (2 : ℝ) ^ l := by positivity
  simpa only [div_eq_mul_inv] using (div_le_one hpow).mpr hl

/-- Degree times resolution is bounded uniformly over the uncapped dyadic levels. -/
theorem biasDegree_resolution_bound (J : ℕ) (A : ℝ) (ν : ℕ) (hA : 0 ≤ A)
    (j : Fin (J + 1)) :
    ((biasDegree A (levelDistance J j) + ν + 2 : ℕ) : ℝ) * parentCells J j ≤
      2 * (A + ν + 3) * (2 : ℝ) ^ J := by
  let l := levelDistance J j
  have hl : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast levelDistance_positive J j
  have hpoly : ((biasDegree A l + ν + 2 : ℕ) : ℝ) ≤ (A + ν + 3) * l := by
    have hb := (biasDegree_bounds A l hA).2
    simp only [Nat.cast_add, Nat.cast_ofNat] at *
    have hν : (0 : ℝ) ≤ (ν : ℝ) := Nat.cast_nonneg _
    nlinarith
  have henv := parentCells_terminal_upper J j
  calc
    _ ≤ ((A + ν + 3) * l) * (2 * (2 : ℝ) ^ J * Real.exp (-(l : ℝ) * Real.log 2)) :=
      mul_le_mul hpoly henv (Nat.cast_nonneg _) (by positivity)
    _ = (2 * (A + ν + 3) * (2 : ℝ) ^ J) * (l * Real.exp (-(l : ℝ) * Real.log 2)) := by ring
    _ ≤ (2 * (A + ν + 3) * (2 : ℝ) ^ J) * 1 :=
      mul_le_mul_of_nonneg_left (distance_exponential_bound l) (by positivity)
    _ = _ := mul_one _

/-- With the paper's explicit terminal constant, every uncapped level satisfies
Lemma 8's small-resolution hypothesis. -/
theorem biasDegree_small_resolution (J : ℕ) (A Cv cK n : ℝ) (ν : ℕ)
    (hA : 0 ≤ A) (hCv : 0 < Cv) (hn : 0 < n) (_hcK : 0 ≤ cK)
    (hterminal : (2 : ℝ) ^ J ≤ cK * n)
    (hcKbound : cK ≤ (4 * Cv * (A + ν + 3))⁻¹) (j : Fin (J + 1)) :
    Cv * (biasDegree A (levelDistance J j) + ν + 2 : ℕ) * parentCells J j / n ≤ 1 / 2 := by
  have hfactor : 0 < 4 * Cv * (A + ν + 3) := by positivity
  have hc : cK * (4 * Cv * (A + ν + 3)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hcKbound hfactor.le
    simpa only [inv_mul_cancel₀ hfactor.ne'] using h
  have hb := biasDegree_resolution_bound J A ν hA j
  have hres : Cv * ((biasDegree A (levelDistance J j) + ν + 2 : ℕ) : ℝ) * parentCells J j ≤ n / 2 := by
    have hbCv := mul_le_mul_of_nonneg_left hb hCv.le
    have hterm := mul_le_mul_of_nonneg_left hterminal (by positivity : 0 ≤ 2 * Cv * (A + ν + 3))
    have hcN := mul_le_mul_of_nonneg_right hc hn.le
    nlinarith
  exact (div_le_iff₀ hn).mpr (by nlinarith)

/-- The full integer sample-size condition on every uncapped polynomial degree. -/
theorem biasDegree_sample_size (A cK : ℝ) (ν n : ℕ) (hA : 0 ≤ A) (hcK : 0 < cK)
    (hcK1 : cK ≤ 1) (hn : 1 ≤ (n : ℝ)) (hcn : 1 ≤ cK * n)
    (hlarge : 4 * (2 * A / Real.log 2 + A + ν + 3) ≤ Real.sqrt n)
    (j : Fin (terminalLevel cK n + 1)) :
    2 * (biasDegree A (levelDistance (terminalLevel cK n) j) + ν + 2) ≤ n := by
  let J := terminalLevel cK n
  let l := levelDistance J j
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl : (l : ℝ) ≤ (J : ℝ) + 1 := by
    have hj := j.isLt
    have hln : l ≤ J + 1 := by dsimp [l, levelDistance]; omega
    exact_mod_cast hln
  have hJ : (J : ℝ) ≤ Real.log n / Real.log 2 := by
    have hcnpos : 0 < cK * n := by positivity
    have hratio : 0 ≤ Real.log (cK * n) / Real.log 2 := div_nonneg (Real.log_nonneg hcn) hlog.le
    have hfloor : (J : ℝ) ≤ Real.log (cK * n) / Real.log 2 := Nat.floor_le hratio
    have hcnle : cK * n ≤ (n : ℝ) := by nlinarith
    exact hfloor.trans (div_le_div_of_nonneg_right (Real.log_le_log hcnpos hcnle) hlog.le)
  have hlogn : Real.log (n : ℝ) ≤ 2 * Real.sqrt n := by
    have h := Real.log_le_rpow_div hnpos.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hdegree : ((biasDegree A l + ν + 2 : ℕ) : ℝ) ≤
      (2 * A / Real.log 2) * Real.sqrt n + A + ν + 3 := by
    have hb := (biasDegree_bounds A l hA).2
    have hlj := hl.trans (add_le_add hJ le_rfl)
    have hljA := mul_le_mul_of_nonneg_left hlj hA
    have hln := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hlogn hlog.le) hA
    simp only [Nat.cast_add, Nat.cast_ofNat] at *
    simp only [div_eq_mul_inv] at hljA hln ⊢
    nlinarith
  have hν : (0 : ℝ) ≤ (ν : ℝ) := Nat.cast_nonneg _
  have hD : 0 ≤ 2 * A / Real.log 2 := by positivity
  have hsqrt : 1 ≤ Real.sqrt n := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  have hsquare : Real.sqrt n ^ 2 = n := Real.sq_sqrt hnpos.le
  have hR : (2 : ℝ) * ((biasDegree A l + ν + 2 : ℕ) : ℝ) ≤ n := by
    have hE : (A + ν + 3) ≤ (A + ν + 3) * Real.sqrt n := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hlarge (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  exact_mod_cast hR

def terminalConstant (A Cv : ℝ) (ν : ℕ) : ℝ := min 1 (4 * Cv * (A + ν + 3))⁻¹

def uncappedThreshold (A Cv : ℝ) (ν : ℕ) : ℕ :=
  Nat.ceil (max 3 (max (terminalConstant A Cv ν)⁻¹
    ((4 * (2 * A / Real.log 2 + A + ν + 3)) ^ 2)))

/-- Beyond one explicit parameter-dependent threshold, the uncapped choice
satisfies both degree and small-resolution conditions at every dyadic level. -/
theorem uncapped_tuning_valid (A Cv : ℝ) (ν n : ℕ) (hA : 0 ≤ A) (hCv : 0 < Cv)
    (hn : uncappedThreshold A Cv ν ≤ n) :
    let cK := terminalConstant A Cv ν
    let J := terminalLevel cK n
    0 < cK ∧ cK ≤ 1 ∧ cK * n / 2 < (2 : ℝ) ^ J ∧ (2 : ℝ) ^ J ≤ cK * n ∧
      ∀ j : Fin (J + 1),
        2 * (biasDegree A (levelDistance J j) + ν + 2) ≤ n ∧
        Cv * (biasDegree A (levelDistance J j) + ν + 2 : ℕ) * parentCells J j / n ≤ 1 / 2 := by
  let cK := terminalConstant A Cv ν
  have hfactor : 0 < 4 * Cv * (A + ν + 3) := by positivity
  have hcK : 0 < cK := by dsimp [cK, terminalConstant]; positivity
  have hcK1 : cK ≤ 1 := min_le_left _ _
  have hcKb : cK ≤ (4 * Cv * (A + ν + 3))⁻¹ := min_le_right _ _
  have hthreshold : max 3 (max cK⁻¹ ((4 * (2 * A / Real.log 2 + A + ν + 3)) ^ 2)) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn3 : (3 : ℝ) ≤ n := (le_max_left _ _).trans hthreshold
  have hnpos : 0 < (n : ℝ) := by linarith
  have hinv : cK⁻¹ ≤ (n : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hthreshold)
  have hcn : 1 ≤ cK * n := by
    have h := mul_le_mul_of_nonneg_left hinv hcK.le
    simpa only [mul_inv_cancel₀ hcK.ne'] using h
  have hsquare : (4 * (2 * A / Real.log 2 + A + ν + 3)) ^ 2 ≤ (n : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hthreshold)
  have hlarge : 4 * (2 * A / Real.log 2 + A + ν + 3) ≤ Real.sqrt n := by
    have hnonneg : 0 ≤ 4 * (2 * A / Real.log 2 + A + ν + 3) := by positivity
    have h := Real.sqrt_le_sqrt hsquare
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using h
  have hterminal := terminalLevel_bounds cK n hcn
  refine ⟨hcK, hcK1, hterminal.1, hterminal.2, fun j => ?_⟩
  exact ⟨biasDegree_sample_size A cK ν n hA hcK hcK1 (by linarith) hcn hlarge j,
    biasDegree_small_resolution _ A Cv cK n ν hA hCv hnpos hcK.le hterminal.2 hcKb j⟩

lemma terminal_bias_bound (cK n θ : ℝ) (hcK : 0 < cK) (hn : 0 < n) (hθ : 0 ≤ θ)
    (hcn : 1 ≤ cK * n) :
    ((2 : ℝ) ^ terminalLevel cK n) ^ (-θ) ≤ (2 / cK) ^ θ * n ^ (-θ) := by
  have hb := (terminalLevel_bounds cK n hcn).1.le
  have hbase : 0 < cK * n / 2 := by positivity
  have h := Real.rpow_le_rpow_of_nonpos hbase hb (neg_nonpos.mpr hθ)
  have heq : cK * n / 2 = n * (cK / 2) := by ring
  rw [heq, Real.mul_rpow hn.le (by positivity), Real.rpow_neg_eq_inv_rpow (cK / 2) θ, inv_div] at h
  simpa only [mul_comm] using h

lemma biasRuleConstant_nonneg (A : ℝ) (ν : ℕ) (hA : 0 ≤ A) : 0 ≤ biasRuleConstant A ν := by
  unfold biasRuleConstant
  exact mul_nonneg (pow_nonneg (by linarith) _) (tsum_nonneg fun _ => by positivity)

/-- Complete numerical uncapped risk bound. Applied to the exact estimator assembly,
it gives the basic upper rate `n^(-1/2)+n^(-θ)` for every `θ>0`. -/
theorem uncapped_total_error_bound (A Cv C0 Cproj cK n θ τ q : ℝ) (ν : ℕ)
    (hA : 0 ≤ A) (hCv : 0 ≤ Cv) (hC0 : 0 ≤ C0) (hCproj : 0 ≤ Cproj)
    (hcK : 0 < cK) (hn : 0 < n) (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hq : 0 < q)
    (hdecay : θ * Real.log 2 + 1 ≤ τ * A) (hcn : 1 ≤ cK * n)
    (v : Fin (terminalLevel cK n + 1) → ℝ)
    (hv : ∀ j, v j ≤ Cv * (parentCells (terminalLevel cK n) j : ℝ) ^ (-2 * q) / n +
      4 * Cv ^ 2 * parentCells (terminalLevel cK n) j / n ^ 2) :
    Cproj * ((2 : ℝ) ^ terminalLevel cK n) ^ (-θ) +
        C0 * (∑ j : Fin (terminalLevel cK n + 1),
          approximationWeight (parentCells (terminalLevel cK n) j) θ τ ν
            (biasDegree A (levelDistance (terminalLevel cK n) j))) +
        (∑ j : Fin (terminalLevel cK n + 1), Real.sqrt (v j)) ≤
      ((Cproj + C0 * biasRuleConstant A ν) * (2 / cK) ^ θ) * n ^ (-θ) +
        (Real.sqrt Cv * (1 + (1 - (2 : ℝ) ^ (-q))⁻¹) +
          2 * Cv * sqrtResolutionConstant * Real.sqrt cK) / Real.sqrt n := by
  have hterminal := terminalLevel_bounds cK n hcn
  have hbias := dyadic_biasDegree_sum_bound (terminalLevel cK n) θ τ A ν hθ hτ hA hdecay
  have hrate := terminal_bias_bound cK n θ hcK hn hθ hcn
  have hsd := dyadic_standard_deviation_sum_bound (terminalLevel cK n) Cv cK n q hCv hcK.le hn hq hterminal.2 v hv
  have hconst : 0 ≤ Cproj + C0 * biasRuleConstant A ν :=
    add_nonneg hCproj (mul_nonneg hC0 (biasRuleConstant_nonneg A ν hA))
  calc
    _ ≤ Cproj * ((2 : ℝ) ^ terminalLevel cK n) ^ (-θ) +
        C0 * (biasRuleConstant A ν * ((2 : ℝ) ^ terminalLevel cK n) ^ (-θ)) +
        (Real.sqrt Cv * (1 + (1 - (2 : ℝ) ^ (-q))⁻¹) +
          2 * Cv * sqrtResolutionConstant * Real.sqrt cK) / Real.sqrt n :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbias hC0)) hsd
    _ = (Cproj + C0 * biasRuleConstant A ν) * ((2 : ℝ) ^ terminalLevel cK n) ^ (-θ) +
        (Real.sqrt Cv * (1 + (1 - (2 : ℝ) ^ (-q))⁻¹) +
          2 * Cv * sqrtResolutionConstant * Real.sqrt cK) / Real.sqrt n := by ring
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      exact (mul_le_mul_of_nonneg_left hrate hconst).trans_eq (by ring)

/-- Above the threshold, the basic numerical upper bound is parametric. -/
theorem parametric_rate_comparison (n θ Cbias Csd : ℝ) (hn : 1 ≤ n)
    (hθ : 1 / 2 ≤ θ) (hbias : 0 ≤ Cbias) :
    Cbias * n ^ (-θ) + Csd / Real.sqrt n ≤ (Cbias + Csd) / Real.sqrt n := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hpow : n ^ (-θ) ≤ n ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  rw [Real.rpow_neg hnpos.le (1 / 2), ← Real.sqrt_eq_rpow] at hpow
  calc
    _ ≤ Cbias * (Real.sqrt n)⁻¹ + Csd / Real.sqrt n :=
      add_le_add (mul_le_mul_of_nonneg_left hpow hbias) le_rfl
    _ = _ := by ring

end RoughRegime.UpperParametric
