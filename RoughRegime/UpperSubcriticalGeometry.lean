module

public import RoughRegime.UpperParametric


@[expose] public section
/-! Actual terminal resolution and degree envelopes in the subcritical upper
construction. The numerical envelopes are derived from the ceil rule. -/
noncomputable section
namespace RoughRegime.UpperSubcritical
open RoughRegime.UpperDegreeRules RoughRegime.UpperParametric

def terminal (n θ τ : ℝ) : ℕ :=
  Nat.ceil ((Real.log n + RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ) / Real.log 2)

def highDegreeEnvelope (n θ τ A : ℝ) (ν : ℕ) : ℝ :=
  A * ((terminal n θ τ : ℝ) - Real.log n / Real.log 2 + 2 * Real.log (Real.log n) / Real.log 2) + ν + 3

def levelLog (J : ℕ) (Cv Rbar n : ℝ) (j : Fin (J + 1)) : ℝ :=
  Real.log ((parentCells J j : ℝ) / n) + Real.log (Cv * Rbar)

def windowEndpoint (J : ℕ) (Cv Rbar n : ℝ) : ℝ :=
  (J : ℝ) * Real.log 2 - Real.log n + Real.log (Cv * Rbar)

def levelCountConstant (θ τ : ℝ) : ℝ :=
  (1 + RoughRegime.Rates.kappa θ τ / θ) / Real.log 2 + 2

def highDegreeConstant (θ τ A : ℝ) (ν : ℕ) : ℝ :=
  A * (RoughRegime.Rates.kappa θ τ / θ + Real.log 2 + 4) / Real.log 2 + ν + 3

lemma parentCells_le_terminal (J : ℕ) (j : Fin (J + 1)) :
    (parentCells J j : ℝ) ≤ (2 : ℝ) ^ J := by
  unfold parentCells
  split_ifs
  · simpa only [Nat.cast_one] using one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := J)
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (by have := j.isLt; omega)

lemma terminal_bounds (n θ τ : ℝ) (hn : 1 ≤ Real.log n) (hθ : 0 < θ)
    (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    (Real.log n + RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ) / Real.log 2 ≤ terminal n θ τ ∧
    (terminal n θ τ : ℝ) ≤ (Real.log n + RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ) / Real.log 2 + 1 := by
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx : 0 ≤ (Real.log n + RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ) / Real.log 2 := by positivity
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one hx).le⟩

lemma terminal_bias_bound (n θ τ : ℝ) (hn : 1 ≤ Real.log n) (hnp : 0 < n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    ((2 : ℝ) ^ terminal n θ τ) ^ (-θ) ≤
      n ^ (-θ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) := by
  have hlo := (terminal_bounds n θ τ hn hθ hθhalf hτ).1
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he : Real.log n + RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ ≤
      (terminal n θ τ : ℝ) * Real.log 2 := (div_le_iff₀ hlog).mp hlo
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hnp, ← Real.exp_add, Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left he hθ.le
  have hθ0 := hθ.ne'
  field_simp at hmul ⊢
  nlinarith

lemma terminal_resolution_lower (n θ τ : ℝ) (hn : 1 ≤ Real.log n) (hnp : 0 < n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    n ≤ (2 : ℝ) ^ terminal n θ τ := by
  have hlo := (terminal_bounds n θ τ hn hθ hθhalf hτ).1
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he : Real.log n ≤ (terminal n θ τ : ℝ) * Real.log 2 := by
    have := (div_le_iff₀ hlog).mp hlo
    have hnonneg : 0 ≤ RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ := by positivity
    linarith
  have h := Real.exp_le_exp.mpr he
  simpa only [Real.exp_log hnp, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h

lemma highDegreeEnvelope_positive (n θ τ A : ℝ) (ν : ℕ) (hn : 1 ≤ Real.log n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hA : 0 ≤ A) :
    (ν : ℝ) + 3 ≤ highDegreeEnvelope n θ τ A ν := by
  have hlo := (terminal_bounds n θ τ hn hθ hθhalf hτ).1
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogL : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hn
  have hcomp : Real.log n / Real.log 2 ≤ (terminal n θ τ : ℝ) := by
    apply le_trans _ hlo
    apply div_le_div_of_nonneg_right _ hlog.le
    have hnonneg : 0 ≤ RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ := by positivity
    linarith
  unfold highDegreeEnvelope
  have hp : 0 ≤ A * ((terminal n θ τ : ℝ) - Real.log n / Real.log 2 + 2 * Real.log (Real.log n) / Real.log 2) := by
    apply mul_nonneg hA
    exact add_nonneg (sub_nonneg.mpr hcomp) (by positivity)
  linarith

lemma terminal_level_count_bound (n θ τ : ℝ) (hn : 1 ≤ Real.log n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    (terminal n θ τ : ℝ) + 1 ≤ levelCountConstant θ τ * Real.log n := by
  have hhi := (terminal_bounds n θ τ hn hθ hθhalf hτ).2
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hsqrt : Real.sqrt (Real.log n) ≤ Real.log n := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ Real.log n)
    nlinarith [Real.sqrt_nonneg (Real.log n)]
  unfold levelCountConstant
  calc
    _ ≤ (Real.log n + RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ) / Real.log 2 + 2 := by linarith
    _ ≤ (Real.log n + RoughRegime.Rates.kappa θ τ * Real.log n / θ) / Real.log 2 + 2 := by gcongr
    _ ≤ (Real.log n + RoughRegime.Rates.kappa θ τ * Real.log n / θ) / Real.log 2 + 2 * Real.log n := by linarith
    _ = _ := by ring

lemma highDegreeEnvelope_bound (n θ τ A : ℝ) (ν : ℕ) (hn : 1 ≤ Real.log n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hA : 0 ≤ A) :
    highDegreeEnvelope n θ τ A ν ≤ highDegreeConstant θ τ A ν * Real.sqrt (Real.log n) := by
  have hhi := (terminal_bounds n θ τ hn hθ hθhalf hτ).2
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hL : 0 < Real.log n := zero_lt_one.trans_le hn
  have hs : 1 ≤ Real.sqrt (Real.log n) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  have hlogL : Real.log (Real.log n) ≤ 2 * Real.sqrt (Real.log n) := by
    have h := Real.log_le_rpow_div hL.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hJ : (terminal n θ τ : ℝ) - Real.log n / Real.log 2 ≤
      RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / (θ * Real.log 2) + 1 := by
    simp only [add_div, div_div] at hhi
    linarith
  have hinside : (terminal n θ τ : ℝ) - Real.log n / Real.log 2 + 2 * Real.log (Real.log n) / Real.log 2 ≤
      ((RoughRegime.Rates.kappa θ τ / θ + Real.log 2 + 4) / Real.log 2) * Real.sqrt (Real.log n) := by
    calc
      _ ≤ RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / (θ * Real.log 2) + 1 + 4 * Real.sqrt (Real.log n) / Real.log 2 := by
        apply add_le_add hJ
        exact div_le_div_of_nonneg_right (by linarith) hlog.le
      _ ≤ RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / (θ * Real.log 2) + Real.sqrt (Real.log n) + 4 * Real.sqrt (Real.log n) / Real.log 2 := by linarith
      _ = _ := by field_simp
  unfold highDegreeEnvelope highDegreeConstant
  have hmul := mul_le_mul_of_nonneg_left hinside hA
  have hνs : (ν : ℝ) + 3 ≤ ((ν : ℝ) + 3) * Real.sqrt (Real.log n) :=
    by nlinarith [Nat.cast_nonneg (α := ℝ) ν]
  convert add_le_add hmul hνs using 1 <;> ring

lemma selectedDegree_global_bound (J : ℕ) (A B : ℝ) (x : Fin (J + 1) → ℝ) (ν : ℕ) (hA : 0 ≤ A)
    (j : Fin (J + 1)) :
    ((selectedDegree A (levelDistance J j) B (x j) ν + ν + 2 : ℕ) : ℝ) ≤ A * ((J : ℝ) + 1) + ν + 3 := by
  have hb := selectedDegree_degree_bound A (levelDistance J j) B (x j) ν hA
  have hl : (levelDistance J j : ℝ) ≤ (J : ℝ) + 1 := by
    exact_mod_cast (show levelDistance J j ≤ J + 1 by unfold levelDistance; omega)
  have hm := mul_le_mul_of_nonneg_left hl hA
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hb.trans (by linarith)

lemma levelDistance_log_parentCells (J : ℕ) (j : Fin (J + 1)) (hj : j.val ≠ 0) :
    (levelDistance J j : ℝ) * Real.log 2 = (J : ℝ) * Real.log 2 - Real.log (parentCells J j) := by
  have hsum : levelDistance J j + (j.val - 1) = J := by
    unfold levelDistance
    have := j.isLt
    omega
  have hc : (levelDistance J j : ℝ) + ((j.val - 1 : ℕ) : ℝ) = (J : ℝ) := by exact_mod_cast hsum
  simp only [parentCells, ite_eq_right hj, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  linear_combination Real.log 2 * hc

lemma selectedDegree_high_bound (n θ τ A B : ℝ) (ν : ℕ) (hA : 0 ≤ A)
    (hnp : 0 < n) (hL : 1 ≤ Real.log n) (hnlarge : (Real.log n) ^ 2 ≤ n)
    (x : Fin (terminal n θ τ + 1) → ℝ) (j : Fin (terminal n θ τ + 1))
    (hjhigh : n / (Real.log n) ^ 2 < (parentCells (terminal n θ τ) j : ℝ)) :
    ((selectedDegree A (levelDistance (terminal n θ τ) j) B (x j) ν + ν + 2 : ℕ) : ℝ) ≤
      highDegreeEnvelope n θ τ A ν := by
  have hLp : 0 < Real.log n := zero_lt_one.trans_le hL
  have hnratio : 1 ≤ n / (Real.log n) ^ 2 := (le_div_iff₀ (pow_pos hLp 2)).mpr (by simpa using hnlarge)
  have hj0 : j.val ≠ 0 := by
    intro he
    have hp : (parentCells (terminal n θ τ) j : ℝ) = 1 := by simp [parentCells, he]
    rw [hp] at hjhigh
    linarith
  have hlogK := Real.log_lt_log (div_pos hnp (pow_pos hLp 2)) hjhigh
  rw [Real.log_div hnp.ne' (pow_pos hLp 2).ne', Real.log_pow] at hlogK
  norm_num only [Nat.cast_ofNat] at hlogK
  have hid := levelDistance_log_parentCells (terminal n θ τ) j hj0
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl : (levelDistance (terminal n θ τ) j : ℝ) ≤
      (terminal n θ τ : ℝ) - Real.log n / Real.log 2 + 2 * Real.log (Real.log n) / Real.log 2 := by
    have heq : (terminal n θ τ : ℝ) - Real.log n / Real.log 2 + 2 * Real.log (Real.log n) / Real.log 2 =
        ((terminal n θ τ : ℝ) * Real.log 2 - Real.log n + 2 * Real.log (Real.log n)) / Real.log 2 := by field_simp
    rw [heq]
    apply (le_div_iff₀ hlog).mpr
    rw [hid]
    linarith
  have hdegree := selectedDegree_degree_bound A (levelDistance (terminal n θ τ) j) B (x j) ν hA
  have hmul := mul_le_mul_of_nonneg_left hl hA
  simp only [Nat.cast_add, Nat.cast_ofNat]
  unfold highDegreeEnvelope
  linarith

lemma exp_levelLog (J : ℕ) (Cv Rbar n : ℝ) (hCv : 0 < Cv) (hRbar : 0 < Rbar) (hn : 0 < n)
    (j : Fin (J + 1)) : Real.exp (levelLog J Cv Rbar n j) = Cv * Rbar * parentCells J j / n := by
  unfold levelLog
  rw [Real.exp_add, Real.exp_log (div_pos (parentCells_positive J j) hn), Real.exp_log (mul_pos hCv hRbar)]
  ring

lemma levelLog_positive_is_high (J : ℕ) (Cv Rbar n : ℝ) (hCv : 0 < Cv) (hRbar : 0 < Rbar)
    (hn : 0 < n) (hL : 0 < Real.log n) (hbound : Cv * Rbar ≤ (Real.log n) ^ 2)
    (j : Fin (J + 1)) (hx : 0 < levelLog J Cv Rbar n j) :
    n / (Real.log n) ^ 2 < (parentCells J j : ℝ) := by
  have he : 1 < Cv * Rbar * parentCells J j / n := by
    rw [← exp_levelLog J Cv Rbar n hCv hRbar hn j]
    exact Real.one_lt_exp_iff.mpr hx
  have he' := (lt_div_iff₀ hn).mp he
  have hmul := mul_le_mul_of_nonneg_right hbound (parentCells_positive J j).le
  apply (div_lt_iff₀ (pow_pos hL 2)).mpr
  nlinarith

lemma levelLog_le_endpoint (J : ℕ) (Cv Rbar n : ℝ) (hn : 0 < n) (j : Fin (J + 1)) :
    levelLog J Cv Rbar n j ≤ windowEndpoint J Cv Rbar n := by
  have hlogK := Real.log_le_log (parentCells_positive J j) (parentCells_le_terminal J j)
  rw [Real.log_pow] at hlogK
  unfold levelLog windowEndpoint
  rw [Real.log_div (parentCells_positive J j).ne' hn.ne']
  linarith

lemma levelLog_separated (J : ℕ) (Cv Rbar n : ℝ) (hn : 0 < n)
    (i j : Fin (J + 1)) (hi : i.val ≠ 0) (hj : j.val ≠ 0) (hij : i ≠ j) :
    Real.log 2 ≤ |levelLog J Cv Rbar n i - levelLog J Cv Rbar n j| := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hdiff : |((i.val - 1 : ℕ) : ℝ) - ((j.val - 1 : ℕ) : ℝ)| ≥ 1 := by
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · have hnat : i.val - 1 + 1 ≤ j.val - 1 := by omega
      have hr : ((i.val - 1 : ℕ) : ℝ) + 1 ≤ ((j.val - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hnat : j.val - 1 + 1 ≤ i.val - 1 := by omega
      have hr : ((j.val - 1 : ℕ) : ℝ) + 1 ≤ ((i.val - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [abs_of_nonneg (by linarith)]
      linarith
  unfold levelLog
  rw [Real.log_div (parentCells_positive J i).ne' hn.ne', Real.log_div (parentCells_positive J j).ne' hn.ne']
  simp only [parentCells, ite_eq_right hi, ite_eq_right hj, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have heq : (((i.val - 1 : ℕ) : ℝ) * Real.log 2 - Real.log n + Real.log (Cv * Rbar)) -
      (((j.val - 1 : ℕ) : ℝ) * Real.log 2 - Real.log n + Real.log (Cv * Rbar)) =
      (((i.val - 1 : ℕ) : ℝ) - ((j.val - 1 : ℕ) : ℝ)) * Real.log 2 := by ring
  rw [heq, abs_mul, abs_of_pos hlog]
  nlinarith

def windowConstant (θ τ Cv CR : ℝ) : ℝ :=
  RoughRegime.Rates.kappa θ τ / θ + Real.log 2 + |Real.log Cv| + |Real.log CR| + 1

lemma windowEndpoint_positive (n θ τ A Cv : ℝ) (ν : ℕ) (hn : 1 ≤ Real.log n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hA : 0 ≤ A) (hCv : 1 ≤ Cv) :
    0 < windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n := by
  have hr := highDegreeEnvelope_positive n θ τ A ν hn hθ hθhalf hτ hA
  have hR : 1 < highDegreeEnvelope n θ τ A ν := by have := Nat.cast_nonneg (α := ℝ) ν; linarith
  have hprod : 1 < Cv * highDegreeEnvelope n θ τ A ν := by nlinarith
  have hlogp := Real.log_pos hprod
  have hJ := (terminal_bounds n θ τ hn hθ hθhalf hτ).1
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hln : Real.log n ≤ (terminal n θ τ : ℝ) * Real.log 2 := by
    have hbound := (div_le_iff₀ hlog).mp hJ
    have hp : 0 ≤ RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ := by positivity
    linarith
  unfold windowEndpoint
  linarith

lemma windowEndpoint_bound (n θ τ A Cv : ℝ) (ν : ℕ) (hn : 1 ≤ Real.log n)
    (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hA : 0 ≤ A) (hCv : 0 < Cv) :
    windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n ≤
      windowConstant θ τ Cv (highDegreeConstant θ τ A ν) * Real.sqrt (Real.log n) := by
  let CR := highDegreeConstant θ τ A ν
  let Rbar := highDegreeEnvelope n θ τ A ν
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hLp : 0 < Real.log n := zero_lt_one.trans_le hn
  have hs : 1 ≤ Real.sqrt (Real.log n) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  have hRp : 0 < Rbar := by
    have hr := highDegreeEnvelope_positive n θ τ A ν hn hθ hθhalf hτ hA
    have := Nat.cast_nonneg (α := ℝ) ν
    dsimp [Rbar]
    linarith
  have hCRp : 0 < CR := by unfold CR highDegreeConstant; positivity
  have hRenv : Rbar ≤ CR * Real.sqrt (Real.log n) := highDegreeEnvelope_bound n θ τ A ν hn hθ hθhalf hτ hA
  have hlogR := Real.log_le_log hRp hRenv
  rw [Real.log_mul hCRp.ne' (Real.sqrt_pos.mpr hLp).ne', Real.log_sqrt hLp.le] at hlogR
  have hlogL : Real.log (Real.log n) ≤ 2 * Real.sqrt (Real.log n) := by
    have h := Real.log_le_rpow_div hLp.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hJ := (terminal_bounds n θ τ hn hθ hθhalf hτ).2
  have hJmul := mul_le_mul_of_nonneg_right hJ hlog.le
  have hJb : (terminal n θ τ : ℝ) * Real.log 2 - Real.log n ≤
      RoughRegime.Rates.kappa θ τ / θ * Real.sqrt (Real.log n) + Real.log 2 := by
    have heq : ((Real.log n + RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) / θ) / Real.log 2 + 1) * Real.log 2 =
        Real.log n + RoughRegime.Rates.kappa θ τ / θ * Real.sqrt (Real.log n) + Real.log 2 := by field_simp
    rw [heq] at hJmul
    linarith
  have hc := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ Real.log 2 + |Real.log Cv| + |Real.log CR| from by positivity)
  unfold windowEndpoint windowConstant
  change (terminal n θ τ : ℝ) * Real.log 2 - Real.log n + Real.log (Cv * Rbar) ≤ _
  rw [Real.log_mul hCv.ne' hRp.ne']
  dsimp [CR] at *
  nlinarith [le_abs_self (Real.log Cv), le_abs_self (Real.log (highDegreeConstant θ τ A ν))]

end RoughRegime.UpperSubcritical
