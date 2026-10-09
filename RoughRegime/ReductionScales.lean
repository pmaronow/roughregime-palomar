module

public import Mathlib
public import RoughRegime.Rates


@[expose] public section
/-! Numerical scale choices in Proposition 12, independent of the prior construction. -/
noncomputable section
open Filter

namespace RoughRegime.ReductionScales

/-- The closest even integer, choosing the upper one in a tie. -/
def nearestEven (z : ℝ) : ℕ := 2 * Nat.floor ((z + 1) / 2)

lemma nearestEven_even (z : ℝ) : Even (nearestEven z) := by
  unfold nearestEven
  exact even_two_mul _

lemma nearestEven_distance (z : ℝ) (hz : 0 ≤ z + 1) :
    |(nearestEven z : ℝ) - z| ≤ 1 := by
  have hq : 0 ≤ (z + 1) / 2 := by positivity
  have hlo := Nat.lt_floor_add_one ((z + 1) / 2)
  have hhi := Nat.floor_le hq
  unfold nearestEven
  rw [Nat.cast_mul, Nat.cast_ofNat, abs_le]
  constructor <;> linarith

lemma nearestEven_comparison (z : ℝ) (hz : 2 ≤ z) :
    1 ≤ (nearestEven z : ℝ) ∧ z / 2 ≤ nearestEven z ∧ (nearestEven z : ℝ) ≤ 3 * z / 2 := by
  have hd := nearestEven_distance z (by linarith)
  rw [abs_le] at hd
  constructor
  · linarith
  constructor <;> linarith

def idealFrequency (n θ τ : ℝ) : ℝ := Real.sqrt (θ * (1 - 2 * θ) * Real.log n / τ)

def frequency (n θ τ : ℝ) : ℕ := nearestEven (idealFrequency n θ τ)

def logResolution (n θ τ c0 : ℝ) : ℝ :=
  (1 - 2 * θ) * Real.log n / frequency n θ τ - Real.log (frequency n θ τ) + c0

/-- The smallest even integer at least `z`. -/
def evenCeiling (z : ℝ) : ℕ := 2 * Nat.ceil (z / 2)

lemma evenCeiling_even (z : ℝ) : Even (evenCeiling z) := by
  unfold evenCeiling
  exact even_two_mul _

lemma evenCeiling_bounds (z : ℝ) (hz : 0 ≤ z) :
    z ≤ (evenCeiling z : ℝ) ∧ (evenCeiling z : ℝ) < z + 2 := by
  have hlo := Nat.le_ceil (z / 2)
  have hhi := Nat.ceil_lt_add_one (div_nonneg hz (by norm_num : (0 : ℝ) ≤ 2))
  unfold evenCeiling
  rw [Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> linarith

lemma evenCeiling_minimal (z : ℝ) (k : ℕ) (hk : Even k) (hz : z ≤ (k : ℝ)) :
    evenCeiling z ≤ k := by
  obtain ⟨a, ha⟩ := hk
  have hka : k = 2 * a := by omega
  rw [hka] at hz ⊢
  unfold evenCeiling
  exact Nat.mul_le_mul_left 2 ((Nat.ceil_le).mpr (by rw [Nat.cast_mul, Nat.cast_ofNat] at hz; linarith))

def idealSideLength (n R t : ℝ) (d : ℕ) : ℝ := (n * Real.exp t / R) ^ ((d : ℝ)⁻¹)

def blockCount (n R t : ℝ) (d : ℕ) : ℕ := evenCeiling (idealSideLength n R t d) ^ d

lemma idealSideLength_positive (n R t : ℝ) (d : ℕ) (hn : 0 < n) (hR : 0 < R) :
    0 < idealSideLength n R t d := by unfold idealSideLength; positivity

lemma idealSideLength_pow (n R t : ℝ) (d : ℕ) (hn : 0 < n) (hR : 0 < R) (hd : 0 < d) :
    idealSideLength n R t d ^ d = n * Real.exp t / R := by
  unfold idealSideLength
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [inv_mul_cancel₀ hd0, Real.rpow_one]

/-- The block count is the `d`th power of an actual smallest even side length,
and its resolution ratio lies in the exact source rounding interval. -/
theorem blockCount_rounding (n R t : ℝ) (d : ℕ) (hn : 0 < n) (hR : 0 < R) (hd : 0 < d) :
    ∃ k : ℕ, Even k ∧ blockCount n R t d = k ^ d ∧
      (∀ k' : ℕ, Even k' → n * Real.exp t ≤ (k' : ℝ) ^ d * R → k ≤ k') ∧
      1 ≤ ((blockCount n R t d : ℝ) * R / n) * Real.exp (-t) ∧
      ((blockCount n R t d : ℝ) * R / n) * Real.exp (-t) ≤
        (1 + 2 / idealSideLength n R t d) ^ d := by
  let z := idealSideLength n R t d
  let k := evenCeiling z
  have hz : 0 < z := idealSideLength_positive n R t d hn hR
  have hround := evenCeiling_bounds z hz.le
  have hpower := idealSideLength_pow n R t d hn hR hd
  have hkp : z ^ d ≤ (k : ℝ) ^ d := pow_le_pow_left₀ hz.le hround.1 d
  refine ⟨k, evenCeiling_even z, rfl, ?_, ?_, ?_⟩
  · intro k' hk' hres
    have hpow : z ^ d ≤ (k' : ℝ) ^ d := by
      rw [hpower]
      exact (div_le_iff₀ hR).mpr hres
    have hside : z ≤ (k' : ℝ) := (pow_le_pow_iff_left₀ hz.le (Nat.cast_nonneg k') hd.ne').mp hpow
    exact evenCeiling_minimal z k' hk' hside
  · have hres : n * Real.exp t ≤ (k : ℝ) ^ d * R := by
      rw [hpower] at hkp
      exact (div_le_iff₀ hR).mp hkp
    simp only [blockCount, Nat.cast_pow]
    change 1 ≤ ((k : ℝ) ^ d * R / n) * Real.exp (-t)
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos t)).mpr ((le_div_iff₀ hn).mpr (by simpa only [one_mul, mul_comm] using hres))
  · have hratio : ((k : ℝ) ^ d * R / n) * Real.exp (-t) = ((k : ℝ) / z) ^ d := by
      rw [div_pow, hpower]
      rw [Real.exp_neg]
      field_simp
    simp only [blockCount, Nat.cast_pow]
    change ((k : ℝ) ^ d * R / n) * Real.exp (-t) ≤ (1 + 2 / z) ^ d
    rw [hratio]
    apply pow_le_pow_left₀ (by positivity) _ d
    have h := (div_le_div_of_nonneg_right hround.2.le hz.le)
    simpa only [add_div, div_self hz.ne', one_mul] using h

lemma idealFrequency_eq (n θ τ : ℝ) (_hn : 1 < n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    idealFrequency n θ τ = Real.sqrt (θ * (1 - 2 * θ) / τ) * Real.sqrt (Real.log n) := by
  have hΔ : 0 < 1 - 2 * θ := by linarith
  unfold idealFrequency
  have hcoef : 0 ≤ θ * (1 - 2 * θ) / τ := by positivity
  have heq : θ * (1 - 2 * θ) * Real.log n / τ = (θ * (1 - 2 * θ) / τ) * Real.log n := by ring
  rw [heq, Real.sqrt_mul hcoef]

lemma idealFrequency_sq (n θ τ : ℝ) (hn : 1 < n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    idealFrequency n θ τ ^ 2 = θ * (1 - 2 * θ) * Real.log n / τ := by
  have hΔ : 0 < 1 - 2 * θ := by linarith
  have hln : 0 < Real.log n := Real.log_pos hn
  unfold idealFrequency
  exact Real.sq_sqrt (by positivity)

lemma idealFrequency_kappa (n θ τ : ℝ) (hn : 1 < n) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    2 * τ * idealFrequency n θ τ = RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) := by
  rw [idealFrequency_eq n θ τ hn hθ hθhalf hτ]
  have hΔ : 0 < 1 - 2 * θ := by linarith
  have hcoef : 0 ≤ θ * (1 - 2 * θ) := by positivity
  have hroot : τ * Real.sqrt (θ * (1 - 2 * θ) / τ) = Real.sqrt (θ * (1 - 2 * θ) * τ) := by
    rw [Real.sqrt_div hcoef, Real.sqrt_mul hcoef]
    calc
      _ = Real.sqrt (θ * (1 - 2 * θ)) * (τ / Real.sqrt τ) := by ring
      _ = _ := by rw [Real.div_sqrt]
  unfold RoughRegime.Rates.kappa
  calc
    _ = 2 * (τ * Real.sqrt (θ * (1 - 2 * θ) / τ)) * Real.sqrt (Real.log n) := by ring
    _ = _ := by rw [hroot]

/-- Exact nearest-even phase penalty, rather than an assumed asymptotic expansion. -/
theorem frequency_phase_difference (n θ τ : ℝ) (hn : 1 < n) (hθ : 0 < θ)
    (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hlarge : 2 ≤ idealFrequency n θ τ) :
    θ * (1 - 2 * θ) * Real.log n / frequency n θ τ + τ * frequency n θ τ -
        RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) =
      τ * ((frequency n θ τ : ℝ) - idealFrequency n θ τ) ^ 2 / frequency n θ τ := by
  have hM : (frequency n θ τ : ℝ) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (nearestEven_comparison _ hlarge).1)
  have hs := idealFrequency_sq n θ τ hn hθ hθhalf hτ
  have ht : θ * (1 - 2 * θ) * Real.log n = τ * idealFrequency n θ τ ^ 2 := by
    exact ((eq_div_iff hτ.ne').mp hs).symm.trans (by ring)
  rw [← idealFrequency_kappa n θ τ hn hθ hθhalf hτ, ht]
  field_simp
  ring

/-- The frequency rounding loses at most `τ/M` in the optimized exponent. -/
theorem frequency_phase_penalty (n θ τ : ℝ) (hn : 1 < n) (hθ : 0 < θ)
    (hθhalf : θ < 1 / 2) (hτ : 0 < τ) (hlarge : 2 ≤ idealFrequency n θ τ) :
    0 ≤ θ * (1 - 2 * θ) * Real.log n / frequency n θ τ + τ * frequency n θ τ -
        RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) ∧
      θ * (1 - 2 * θ) * Real.log n / frequency n θ τ + τ * frequency n θ τ -
        RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n) ≤ τ / frequency n θ τ := by
  rw [frequency_phase_difference n θ τ hn hθ hθhalf hτ hlarge]
  have hM : 0 < (frequency n θ τ : ℝ) :=
    lt_of_lt_of_le zero_lt_one (nearestEven_comparison _ hlarge).1
  have hd := nearestEven_distance (idealFrequency n θ τ) (by linarith)
  have hsq : ((frequency n θ τ : ℝ) - idealFrequency n θ τ) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hd 2
    simpa only [sq_abs, one_pow, frequency] using h
  exact ⟨by positivity, div_le_div_of_nonneg_right
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hτ.le) hM.le⟩

/-- Log factorial estimate used in the leading hardness calculation. -/
lemma log_factorial_lower (M : ℕ) (hM : 1 ≤ M) :
    (M : ℝ) * Real.log M - M ≤ Real.log (M.factorial : ℝ) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hn : M ≠ 0 := by omega
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hm
  have hπ : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have h := Stirling.le_log_factorial_stirling hn
  linarith

theorem idealFrequency_tendsto (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => idealFrequency n θ τ) atTop atTop := by
  have hΔ : 0 < 1 - 2 * θ := by linarith
  have hcoef : 0 < Real.sqrt (θ * (1 - 2 * θ) / τ) := by positivity
  have hbase := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hcoef
  apply Filter.Tendsto.congr' _ hbase
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  exact (idealFrequency_eq n θ τ hn hθ hθhalf hτ).symm

theorem frequency_tendsto (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => (frequency n θ τ : ℝ)) atTop atTop := by
  have hi := idealFrequency_tendsto θ τ hθ hθhalf hτ
  have hlo := hi.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  apply tendsto_atTop_mono' atTop _ hlo
  filter_upwards [hi.eventually_ge_atTop 2] with n hn
  exact (nearestEven_comparison _ hn).2.1

/-- Exact rounding asymptotics for the actual nearest-even frequency. -/
theorem frequency_div_ideal_tendsto_one (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => (frequency n θ τ : ℝ) / idealFrequency n θ τ) atTop (nhds 1) := by
  have hi := idealFrequency_tendsto θ τ hθ hθhalf hτ
  have hinv := tendsto_inv_atTop_zero.comp hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hinv
  filter_upwards [hi.eventually_ge_atTop 2] with n hn
  have hpos : 0 < idealFrequency n θ τ := by linarith
  have hd := nearestEven_distance (idealFrequency n θ τ) (by linarith)
  have heq : (frequency n θ τ : ℝ) / idealFrequency n θ τ - 1 =
      ((frequency n θ τ : ℝ) - idealFrequency n θ τ) / idealFrequency n θ τ := by field_simp
  rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hpos]
  exact (div_le_div_of_nonneg_right hd hpos.le).trans_eq (by simp only [one_div, Function.comp_apply])

lemma frequency_sq_log_tendsto (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => (frequency n θ τ : ℝ) ^ 2 / Real.log n) atTop
      (nhds (θ * (1 - 2 * θ) / τ)) := by
  have hr := (frequency_div_ideal_tendsto_one θ τ hθ hθhalf hτ).pow 2
  have hc := hr.mul_const (θ * (1 - 2 * θ) / τ)
  norm_num only [one_pow, one_mul] at hc
  apply Filter.Tendsto.congr' _ hc
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos hn).ne'
  have hsq := idealFrequency_sq n θ τ hn hθ hθhalf hτ
  rw [div_pow, hsq]
  have hΔ : 1 - θ * 2 ≠ 0 := by linarith
  field_simp [hΔ]

lemma logFrequency_div_frequency_tendsto_zero (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => Real.log (frequency n θ τ) / frequency n θ τ) atTop (nhds 0) := by
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (frequency_tendsto θ τ hθ hθhalf hτ)

lemma logResolution_div_frequency_tendsto (θ τ c0 : ℝ) (hθ : 0 < θ)
    (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => logResolution n θ τ c0 / frequency n θ τ) atTop (nhds (τ / θ)) := by
  have hΔ : 0 < 1 - 2 * θ := by linarith
  have hcoef : 0 < θ * (1 - 2 * θ) / τ := by positivity
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hsq := (frequency_sq_log_tendsto θ τ hθ hθhalf hτ).inv₀ hcoef.ne'
  have hfirst := hsq.const_mul (1 - 2 * θ)
  have hlog := logFrequency_div_frequency_tendsto_zero θ τ hθ hθhalf hτ
  have hinv := (tendsto_inv_atTop_zero.comp hM).const_mul c0
  have htotal := (hfirst.sub hlog).add hinv
  have hvalue : (1 - 2 * θ) * (θ * (1 - 2 * θ) / τ)⁻¹ - 0 + c0 * 0 = τ / θ := by
    field_simp
    ring
  rw [hvalue] at htotal
  apply Filter.Tendsto.congr' _ htotal
  filter_upwards [hM.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop 0] with n hn hln
  have hm0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
  unfold logResolution
  simp only [Function.comp_apply]
  rw [inv_div]
  field_simp

lemma logResolution_tendsto (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => logResolution n θ τ c0) atTop atTop := by
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have ht := logResolution_div_frequency_tendsto θ τ c0 hθ hθhalf hτ
  have hprod := ht.pos_mul_atTop (div_pos hτ hθ) hM
  apply Filter.Tendsto.congr' _ hprod
  filter_upwards [hM.eventually_ge_atTop 1] with n hn
  have hm0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
  exact div_mul_cancel₀ _ hm0

lemma logR_div_frequency_tendsto_zero (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ))) :
    Tendsto (fun n => Real.log (R n) / frequency n θ τ) atTop (nhds 0) := by
  have hl := Real.isLittleO_log_id_atTop.comp_tendsto (frequency_tendsto θ τ hθ hθhalf hτ)
  exact (hR.trans_isLittleO hl).tendsto_div_nhds_zero

lemma logR_div_sqrtFrequency_tendsto_zero (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ))) :
    Tendsto (fun n => Real.log (R n) / Real.sqrt (frequency n θ τ)) atTop (nhds 0) := by
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    (frequency_tendsto θ τ hθ hθhalf hτ)
  simpa only [← Real.sqrt_eq_rpow, Function.comp_apply] using (hR.trans_isLittleO hl).tendsto_div_nhds_zero

lemma frequency_log_div_log_tendsto_zero (θ τ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ) :
    Tendsto (fun n : ℝ => frequency n θ τ * Real.log (frequency n θ τ) / Real.log n) atTop (nhds 0) := by
  have hsq := frequency_sq_log_tendsto θ τ hθ hθhalf hτ
  have hlog := logFrequency_div_frequency_tendsto_zero θ τ hθ hθhalf hτ
  have hlim := hsq.mul hlog
  norm_num only [mul_zero] at hlim
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [(frequency_tendsto θ τ hθ hθhalf hτ).eventually_ge_atTop 1] with n hn
  have hm0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
  field_simp

lemma logResolution_sub_logR_tendsto (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ))) :
    Tendsto (fun n => logResolution n θ τ c0 - Real.log (R n)) atTop atTop := by
  have hratio := (logResolution_div_frequency_tendsto θ τ c0 hθ hθhalf hτ).sub
    (logR_div_frequency_tendsto_zero θ τ hθ hθhalf hτ R hR)
  norm_num only [sub_zero] at hratio
  have hM := frequency_tendsto θ τ hθ hθhalf hτ
  have hprod := hratio.pos_mul_atTop (div_pos hτ hθ) hM
  apply Filter.Tendsto.congr' _ hprod
  filter_upwards [hM.eventually_ge_atTop 1] with n hn
  have hm0 : (frequency n θ τ : ℝ) ≠ 0 := by linarith
  rw [← sub_div, div_mul_cancel₀ _ hm0]

def selectedBlockCount (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) : ℕ :=
  blockCount n (R n) (logResolution n θ τ c0) d

def resolutionRatio (θ τ c0 : ℝ) (R : ℝ → ℝ) (d : ℕ) (n : ℝ) : ℝ :=
  (selectedBlockCount θ τ c0 R d n : ℝ) * R n / n

lemma idealSideLength_tendsto (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => idealSideLength n (R n) (logResolution n θ τ c0) d) atTop atTop := by
  have ht := logResolution_sub_logR_tendsto θ τ c0 hθ hθhalf hτ R hR
  have he := Real.tendsto_exp_atTop.comp ht
  have harg : Tendsto (fun n : ℝ => n * Real.exp (logResolution n θ τ c0) / R n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ he
    filter_upwards [hRpos, eventually_ge_atTop (1 : ℝ)] with n hRn hn
    have hRp : 0 < R n := zero_lt_one.trans_le hRn
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_log hRp]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.exp_pos (logResolution n θ τ c0)]) hRp.le
  have hdp : 0 < (d : ℝ)⁻¹ := by positivity
  exact (tendsto_rpow_atTop hdp).comp harg

/-- Rounding the block side to the actual smallest even integer has vanishing
relative loss, with no assumed integer-grid approximation. -/
theorem resolutionRatio_rounding_tendsto_one (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => resolutionRatio θ τ c0 R d n * Real.exp (-logResolution n θ τ c0)) atTop (nhds 1) := by
  have hz := idealSideLength_tendsto θ τ c0 hθ hθhalf hτ R hRpos hR d hd
  have hinv := (tendsto_inv_atTop_zero.comp hz).const_mul 2
  have hupper := ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).pow d
  norm_num only [mul_zero, add_zero, one_pow] at hupper
  have hupper0 := hupper.sub (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num only [sub_self] at hupper0
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hupper0
  · filter_upwards [hRpos, eventually_ge_atTop (1 : ℝ)] with n hRn hn
    have hRp : 0 < R n := zero_lt_one.trans_le hRn
    have hnp : 0 < n := zero_lt_one.trans_le hn
    rcases blockCount_rounding n (R n) (logResolution n θ τ c0) d hnp hRp hd with
      ⟨k, hke, hk, hmin, hlo, hhi⟩
    change ‖(blockCount n (R n) (logResolution n θ τ c0) d : ℝ) * R n / n *
      Real.exp (-logResolution n θ τ c0) - 1‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h : (blockCount n (R n) (logResolution n θ τ c0) d : ℝ) * R n / n *
        Real.exp (-logResolution n θ τ c0) - 1 ≤
      (1 + 2 / idealSideLength n (R n) (logResolution n θ τ c0) d) ^ d - 1 := by linarith
    simpa only [one_div, div_eq_mul_inv, Function.comp_apply] using h

/-- The exact logarithmic resolution error `log x - t` tends to zero. -/
theorem log_resolutionRatio_sub_tendsto_zero (θ τ c0 : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) (hτ : 0 < τ)
    (R : ℝ → ℝ) (hRpos : ∀ᶠ n in atTop, 1 ≤ R n)
    (hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n θ τ)))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℝ => Real.log (resolutionRatio θ τ c0 R d n) - logResolution n θ τ c0) atTop (nhds 0) := by
  have hratio := resolutionRatio_rounding_tendsto_one θ τ c0 hθ hθhalf hτ R hRpos hR d hd
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  norm_num only [Real.log_one] at hlog
  apply Filter.Tendsto.congr' _ hlog
  filter_upwards [hRpos, eventually_ge_atTop (1 : ℝ)] with n hRn hn
  have hRp : 0 < R n := zero_lt_one.trans_le hRn
  have hnp : 0 < n := zero_lt_one.trans_le hn
  rcases blockCount_rounding n (R n) (logResolution n θ τ c0) d hnp hRp hd with
    ⟨k, hke, hk, hmin, hlo, hhi⟩
  have hx : 0 < resolutionRatio θ τ c0 R d n := by
    have hprod : 0 < resolutionRatio θ τ c0 R d n * Real.exp (-logResolution n θ τ c0) :=
      zero_lt_one.trans_le hlo
    exact pos_of_mul_pos_left hprod (Real.exp_pos _).le
  simp only [Function.comp_apply]
  rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

end RoughRegime.ReductionScales
