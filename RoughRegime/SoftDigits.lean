module

public import RoughRegime.Lattice
public import Mathlib


@[expose] public section
namespace RoughRegime.LatticePriors

open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

/-- The fixed smooth transition specified in the lattice construction. -/
structure SmoothStep where
  f : ℝ → ℝ
  smooth : ContDiff ℝ ∞ f
  monotone : Monotone f
  nonneg : ∀ x, 0 ≤ f x
  le_one : ∀ x, f x ≤ 1
  zero : ∀ x, x ≤ -1 → f x = 0
  one : ∀ x, 1 ≤ x → f x = 1
  half : f 0 = 1 / 2

/-- A concrete transition, so the construction does not require existence
of an unspecified smooth function as an axiom. -/
noncomputable def canonicalStep : SmoothStep where
  f x := Real.smoothTransition ((x + 1) / 2)
  smooth := by fun_prop
  monotone := by intro x y hxy; apply Real.smoothTransition.monotone; linarith
  nonneg x := Real.smoothTransition.nonneg _
  le_one x := Real.smoothTransition.le_one _
  zero x hx := Real.smoothTransition.zero_of_nonpos (by linarith)
  one x hx := Real.smoothTransition.one_of_one_le (by linarith)
  half := by
    norm_num [Real.smoothTransition]
    have hp : expNegInvGlue (1 / 2) ≠ 0 :=
      (expNegInvGlue.pos_of_pos (by norm_num)).ne'
    field_simp
    norm_num

/-- A single smoothed odd interval. The periodized pulse is exactly the
nearest-integer digit selector, because adjacent transition collars are disjoint. -/
noncomputable def softPulse (U : SmoothStep) (γ y : ℝ) : ℝ :=
  U.f ((y - 1) / γ) * U.f ((2 - y) / γ)

noncomputable def softDigit (U : SmoothStep) (γ y : ℝ) : ℝ :=
  ∑' z : ℤ, softPulse U γ (y - 2 * z)

theorem softPulse_smooth (U : SmoothStep) (γ : ℝ) : ContDiff ℝ ∞ (softPulse U γ) := by
  unfold softPulse
  exact (U.smooth.comp (by fun_prop)).mul (U.smooth.comp (by fun_prop))

theorem softPulse_nonneg (U : SmoothStep) (γ y : ℝ) : 0 ≤ softPulse U γ y :=
  mul_nonneg (U.nonneg _) (U.nonneg _)

theorem softPulse_le_one (U : SmoothStep) (γ y : ℝ) : softPulse U γ y ≤ 1 := by
  unfold softPulse
  calc
    U.f ((y - 1) / γ) * U.f ((2 - y) / γ) ≤ 1 * 1 :=
      mul_le_mul (U.le_one _) (U.le_one _) (U.nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem softPulse_eq_zero_of_lt (U : SmoothStep) (γ y : ℝ) (hγ : 0 < γ) (hy : y < 1 - γ) :
    softPulse U γ y = 0 := by
  unfold softPulse
  rw [U.zero ((y - 1) / γ) (by apply (div_le_iff₀ hγ).2; linarith), zero_mul]

theorem softPulse_eq_zero_of_gt (U : SmoothStep) (γ y : ℝ) (hγ : 0 < γ) (hy : 2 + γ < y) :
    softPulse U γ y = 0 := by
  unfold softPulse
  rw [U.zero ((2 - y) / γ) (by apply (div_le_iff₀ hγ).2; linarith), mul_zero]

theorem softPulse_support_subset (U : SmoothStep) (γ : ℝ) (hγ : 0 < γ) :
    Function.support (softPulse U γ) ⊆ Icc (1 - γ) (2 + γ) := by
  intro y hy
  constructor
  · by_contra h
    exact hy (softPulse_eq_zero_of_lt U γ y hγ (lt_of_not_ge h))
  · by_contra h
    exact hy (softPulse_eq_zero_of_gt U γ y hγ (lt_of_not_ge h))

/-- Only five pulses can enter a fixed unit neighborhood. -/
theorem softDigit_local_sum (U : SmoothStep) (γ x y : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4)
    (hy : |y - x| < 1) :
    softDigit U γ y = ∑ z ∈ Finset.Icc (Int.floor (x / 2) - 2) (Int.floor (x / 2) + 2),
      softPulse U γ (y - 2 * z) := by
  unfold softDigit
  apply tsum_eq_sum
  intro z hz
  have hn0 := Int.floor_le (x / 2)
  have hn1 := Int.lt_floor_add_one (x / 2)
  rcases abs_lt.mp hy with ⟨hy0, hy1⟩
  simp only [Finset.mem_Icc, not_and_or, not_le] at hz
  rcases hz with hz | hz
  · have hzi : z ≤ Int.floor (x / 2) - 3 := by omega
    have hzr : (z : ℝ) ≤ (Int.floor (x / 2) : ℝ) - 3 := by exact_mod_cast hzi
    apply softPulse_eq_zero_of_gt U γ _ hγ
    linarith
  · have hzi : Int.floor (x / 2) + 3 ≤ z := by omega
    have hzr : (Int.floor (x / 2) : ℝ) + 3 ≤ z := by exact_mod_cast hzi
    apply softPulse_eq_zero_of_lt U γ _ hγ
    linarith

theorem softDigit_smooth (U : SmoothStep) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) :
    ContDiff ℝ ∞ (softDigit U γ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have heq : softDigit U γ =ᶠ[𝓝 x]
      (fun y => ∑ z ∈ Finset.Icc (Int.floor (x / 2) - 2) (Int.floor (x / 2) + 2),
        softPulse U γ (y - 2 * z)) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    apply softDigit_local_sum U γ x y hγ hγ1
    simpa only [Metric.mem_ball, Real.dist_eq] using hy
  apply ContDiffAt.congr_of_eventuallyEq _ heq
  apply ContDiff.contDiffAt
  apply ContDiff.sum
  intro z hz
  exact (softPulse_smooth U γ).comp (by fun_prop)

theorem softDigit_eq_single_pulse (U : SmoothStep) (γ y : ℝ) (z : ℤ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4)
    (hy0 : 1 / 2 ≤ y - 2 * z) (hy1 : y - 2 * z ≤ 5 / 2) :
    softDigit U γ y = softPulse U γ (y - 2 * z) := by
  unfold softDigit
  apply tsum_eq_single z
  intro j hj
  have hclass : j ≤ z - 1 ∨ z + 1 ≤ j := by omega
  rcases hclass with hclass | hclass
  · have hR : (j : ℝ) ≤ z - 1 := by exact_mod_cast hclass
    apply softPulse_eq_zero_of_gt U γ _ hγ
    linarith
  · have hR : (z : ℝ) + 1 ≤ j := by exact_mod_cast hclass
    apply softPulse_eq_zero_of_lt U γ _ hγ
    linarith

theorem softDigit_odd_nearest (U : SmoothStep) (γ y : ℝ) (z : ℤ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hy : |y - (2 * z + 1)| ≤ 1 / 2) :
    softDigit U γ y = U.f ((y - (2 * z + 1)) / γ) := by
  rcases abs_le.mp hy with ⟨hy0, hy1⟩
  rw [softDigit_eq_single_pulse U γ y z hγ hγ1 (by linarith) (by linarith)]
  unfold softPulse
  rw [U.one ((2 - (y - 2 * z)) / γ) (by apply (le_div_iff₀ hγ).2; linarith), mul_one]
  congr 1
  ring

theorem softDigit_even_nearest (U : SmoothStep) (γ y : ℝ) (z : ℤ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hy : |y - 2 * z| ≤ 1 / 2) :
    softDigit U γ y = U.f (-(y - 2 * z) / γ) := by
  rcases abs_le.mp hy with ⟨hy0, hy1⟩
  rw [softDigit_eq_single_pulse U γ y (z - 1) hγ hγ1 (by push_cast; linarith) (by push_cast; linarith)]
  unfold softPulse
  rw [U.one (((y - 2 * (z - 1 : ℤ)) - 1) / γ)
    (by apply (le_div_iff₀ hγ).2; push_cast; linarith), one_mul]
  congr 1
  push_cast
  ring

noncomputable def nearestInteger (y : ℝ) : ℤ := Int.floor (y + 1 / 2)

theorem nearestInteger_distance (y : ℝ) : |y - (nearestInteger y : ℝ)| ≤ 1 / 2 := by
  unfold nearestInteger
  have h0 := Int.floor_le (y + 1 / 2)
  have h1 := Int.lt_floor_add_one (y + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-- This is the source paper's nearest-integer formula, with the two possible
parities written explicitly instead of an integer power of minus one. -/
noncomputable def nearestSoftDigit (U : SmoothStep) (γ y : ℝ) : ℝ :=
  if nearestInteger y % 2 = 0 then U.f (-(y - nearestInteger y) / γ)
  else U.f ((y - nearestInteger y) / γ)

theorem softDigit_eq_nearestSoftDigit (U : SmoothStep) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) :
    softDigit U γ = nearestSoftDigit U γ := by
  ext y
  let n := nearestInteger y
  change softDigit U γ y = if n % 2 = 0 then U.f (-(y - (n : ℝ)) / γ) else U.f ((y - (n : ℝ)) / γ)
  have hclose := nearestInteger_distance y
  have hdiv : n = 2 * (n / 2) + n % 2 := by omega
  have hrem : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hrem with hrem | hrem
  · have hn : n = 2 * (n / 2) := by omega
    have hnR : (n : ℝ) = 2 * (n / 2 : ℤ) := by exact_mod_cast hn
    have hs := softDigit_even_nearest U γ y (n / 2) hγ hγ1 (by simpa [← hnR] using hclose)
    rw [ite_eq_left hrem, hnR]
    exact hs
  · have hn : n = 2 * (n / 2) + 1 := by omega
    have hnR : (n : ℝ) = 2 * (n / 2 : ℤ) + 1 := by exact_mod_cast hn
    have hs := softDigit_odd_nearest U γ y (n / 2) hγ hγ1 (by simpa [← hnR] using hclose)
    rw [ite_eq_right (by omega), hnR]
    exact hs

theorem softDigit_range (U : SmoothStep) (γ y : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) :
    0 ≤ softDigit U γ y ∧ softDigit U γ y ≤ 1 := by
  rw [softDigit_eq_nearestSoftDigit U γ hγ hγ1]
  unfold nearestSoftDigit
  split_ifs <;> exact ⟨U.nonneg _, U.le_one _⟩

theorem nearestInteger_floor_cases (y : ℝ) :
    nearestInteger y = Int.floor y ∨ nearestInteger y = Int.floor y + 1 := by
  have h0 : Int.floor y ≤ nearestInteger y := Int.floor_mono (by linarith : y ≤ y + 1 / 2)
  have h1 : nearestInteger y ≤ Int.floor y + 1 := by
    apply Int.floor_le_iff.mpr
    have h := Int.lt_floor_add_one y
    push_cast
    linarith
  omega

theorem softDigit_le_half_of_even_floor (U : SmoothStep) (γ y : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (heven : Int.floor y % 2 = 0) :
    softDigit U γ y ≤ 1 / 2 := by
  rw [softDigit_eq_nearestSoftDigit U γ hγ hγ1]
  unfold nearestSoftDigit
  have hlo := Int.floor_le y
  have hhi := Int.lt_floor_add_one y
  rcases nearestInteger_floor_cases y with hn | hn
  · rw [hn, ite_eq_left heven]
    rw [← U.half]
    apply U.monotone
    apply (div_le_iff₀ hγ).2
    linarith
  · have hodd : (Int.floor y + 1) % 2 ≠ 0 := by omega
    rw [hn, ite_eq_right hodd]
    rw [← U.half]
    apply U.monotone
    apply (div_le_iff₀ hγ).2
    push_cast
    linarith

theorem half_le_softDigit_of_odd_floor (U : SmoothStep) (γ y : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hodd : Int.floor y % 2 = 1) :
    1 / 2 ≤ softDigit U γ y := by
  rw [softDigit_eq_nearestSoftDigit U γ hγ hγ1]
  unfold nearestSoftDigit
  have hlo := Int.floor_le y
  have hhi := Int.lt_floor_add_one y
  rcases nearestInteger_floor_cases y with hn | hn
  · have hnodd : Int.floor y % 2 ≠ 0 := by omega
    rw [hn, ite_eq_right hnodd]
    rw [← U.half]
    apply U.monotone
    apply (le_div_iff₀ hγ).2
    linarith
  · have heven : (Int.floor y + 1) % 2 = 0 := by omega
    rw [hn, ite_eq_left heven]
    rw [← U.half]
    apply U.monotone
    apply (le_div_iff₀ hγ).2
    push_cast
    linarith

/-- Away from the integer collars, the actual smooth selector is the hard
binary digit exactly. -/
theorem softDigit_eq_hardDigit_off_collar (U : SmoothStep) (γ y : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hoff : ∀ z : ℤ, γ ≤ |y - z|) :
    softDigit U γ y = ((Int.floor y % 2 : ℤ) : ℝ) := by
  rw [softDigit_eq_nearestSoftDigit U γ hγ hγ1]
  unfold nearestSoftDigit
  have hlo := Int.floor_le y
  have hhi := Int.lt_floor_add_one y
  have hleft : γ ≤ y - Int.floor y := by
    simpa only [abs_of_nonneg (by linarith : 0 ≤ y - (Int.floor y : ℝ))] using hoff (Int.floor y)
  have hright : γ ≤ (Int.floor y : ℝ) + 1 - y := by
    have h := hoff (Int.floor y + 1)
    rw [Int.cast_add, Int.cast_one, abs_of_nonpos (by linarith : y - ((Int.floor y : ℝ) + 1) ≤ 0)] at h
    linarith
  have hrem : Int.floor y % 2 = 0 ∨ Int.floor y % 2 = 1 := by omega
  rcases nearestInteger_floor_cases y with hn | hn <;> rcases hrem with hrem | hrem
  · rw [hn, ite_eq_left hrem, hrem]
    norm_num only [Int.cast_zero]
    apply U.zero
    apply (div_le_iff₀ hγ).2
    linarith
  · rw [hn, ite_eq_right (by omega), hrem]
    norm_num only [Int.cast_one]
    apply U.one
    apply (le_div_iff₀ hγ).2
    linarith
  · rw [hn, ite_eq_right (by omega), hrem]
    norm_num only [Int.cast_zero]
    apply U.zero
    apply (div_le_iff₀ hγ).2
    push_cast
    linarith
  · rw [hn, ite_eq_left (by omega), hrem]
    norm_num only [Int.cast_one]
    apply U.one
    apply (le_div_iff₀ hγ).2
    push_cast
    linarith

theorem softDigit_wrong_cost (U : SmoothStep) (γ y : ℝ) (e : ℤ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (he : e = 0 ∨ e = 1)
    (hne : e ≠ Int.floor y % 2) :
    (1 / 2 : ℝ) ≤ |softDigit U γ y - e| := by
  rcases he with rfl | rfl
  · have hodd : Int.floor y % 2 = 1 := by omega
    have h := half_le_softDigit_of_odd_floor U γ y hγ hγ1 hodd
    simpa only [Int.cast_zero, sub_zero] using h.trans (le_abs_self _)
  · have heven : Int.floor y % 2 = 0 := by omega
    have h := softDigit_le_half_of_even_floor U γ y hγ hγ1 heven
    rw [Int.cast_one, abs_of_nonpos (by linarith)]
    linarith

end RoughRegime.LatticePriors
