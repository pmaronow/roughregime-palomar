module

public import RoughRegime.SoftDigits


@[expose] public section
namespace RoughRegime.LatticePriors
open Set Filter
open scoped Topology ContDiff

 theorem SmoothStep.iteratedDeriv_zero_left (U : SmoothStep) (N : ℕ) (hN : 0 < N)
    (x : ℝ) (hx : x < -1) : iteratedDeriv N U.f x = 0 := by
  have heq : U.f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact U.zero y hy.le
  rw [heq.iteratedDeriv_eq N, iteratedDeriv_const, ite_eq_right (by omega)]

 theorem SmoothStep.iteratedDeriv_zero_right (U : SmoothStep) (N : ℕ) (hN : 0 < N)
    (x : ℝ) (hx : 1 < x) : iteratedDeriv N U.f x = 0 := by
  have heq : U.f =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact U.one y hy.le
  rw [heq.iteratedDeriv_eq N, iteratedDeriv_const, ite_eq_right (by omega)]

/-- The fixed transition has globally bounded derivatives of every order. -/
 theorem SmoothStep.derivative_bound (U : SmoothStep) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |iteratedDeriv N U.f x| ≤ C := by
  by_cases hN : N = 0
  · subst N
    refine ⟨1, zero_lt_one, ?_⟩
    intro x
    simpa only [iteratedDeriv_zero, abs_of_nonneg (U.nonneg x)] using U.le_one x
  · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (U.smooth.continuous_iteratedDeriv N (by simp)).continuousOn
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · have hb : |iteratedDeriv N U.f x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
      exact hb.trans (le_max_left _ _)
    · simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [U.iteratedDeriv_zero_left N (by omega) x hx, abs_zero]
        positivity
      · rw [U.iteratedDeriv_zero_right N (by omega) x hx, abs_zero]
        positivity

 theorem softDigit_eq_single_pulse_wide (U : SmoothStep) (γ y : ℝ) (z : ℤ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4)
    (hy0 : 1 / 4 < y - 2 * z) (hy1 : y - 2 * z < 11 / 4) :
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

 theorem softDigit_odd_near_wide (U : SmoothStep) (γ y : ℝ) (z : ℤ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hy : |y - (2 * z + 1)| < 3 / 4) :
    softDigit U γ y = U.f ((y - (2 * z + 1)) / γ) := by
  rcases abs_lt.mp hy with ⟨hy0, hy1⟩
  rw [softDigit_eq_single_pulse_wide U γ y z hγ hγ1 (by linarith) (by linarith)]
  unfold softPulse
  rw [U.one ((2 - (y - 2 * z)) / γ) (by apply (le_div_iff₀ hγ).2; linarith), mul_one]
  congr 1
  ring

 theorem softDigit_even_near_wide (U : SmoothStep) (γ y : ℝ) (z : ℤ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hy : |y - 2 * z| < 3 / 4) :
    softDigit U γ y = U.f (-(y - 2 * z) / γ) := by
  rcases abs_lt.mp hy with ⟨hy0, hy1⟩
  rw [softDigit_eq_single_pulse_wide U γ y (z - 1) hγ hγ1
    (by push_cast; linarith) (by push_cast; linarith)]
  unfold softPulse
  rw [U.one (((y - 2 * (z - 1 : ℤ)) - 1) / γ)
    (by apply (le_div_iff₀ hγ).2; push_cast; linarith), one_mul]
  congr 1
  push_cast
  ring

/-- Around every point the digit selector equals a single affine rescaling of
one fixed transition. This includes the half-integers, where both formulas are flat. -/
 theorem softDigit_eventually_affine (U : SmoothStep) (γ x : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) :
    ∃ (c : ℝ) (s : ℝ), |s| = 1 ∧
      softDigit U γ =ᶠ[𝓝 x] (fun y => U.f (s * (y - c) / γ)) := by
  let n := nearestInteger x
  have hclose : |x - (n : ℝ)| ≤ 1 / 2 := nearestInteger_distance x
  have hrem : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hnear : ∀ᶠ y in 𝓝 x, |y - (n : ℝ)| < 3 / 4 := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 8)] with y hy
    have hy' : |y - x| < 1 / 8 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
    have := abs_add_le (y - x) (x - (n : ℝ))
    have heq : (y - x) + (x - (n : ℝ)) = y - n := by ring
    rw [heq] at this
    linarith
  rcases hrem with hrem | hrem
  · have hn : n = 2 * (n / 2) := by omega
    have hnR : (n : ℝ) = 2 * (n / 2 : ℤ) := by exact_mod_cast hn
    refine ⟨n, -1, by norm_num, ?_⟩
    filter_upwards [hnear] with y hy
    rw [hnR] at hy ⊢
    simpa only [neg_one_mul] using softDigit_even_near_wide U γ y (n / 2) hγ hγ1 hy
  · have hn : n = 2 * (n / 2) + 1 := by omega
    have hnR : (n : ℝ) = 2 * (n / 2 : ℤ) + 1 := by exact_mod_cast hn
    refine ⟨n, 1, by norm_num, ?_⟩
    filter_upwards [hnear] with y hy
    rw [hnR] at hy ⊢
    simpa only [one_mul] using softDigit_odd_near_wide U γ y (n / 2) hγ hγ1 hy

 theorem iteratedDeriv_affine (U : SmoothStep) (N : ℕ) (c s γ x : ℝ) :
    iteratedDeriv N (fun y => U.f (s * (y - c) / γ)) x =
      (s / γ) ^ N * iteratedDeriv N U.f (s * (x - c) / γ) := by
  have heq : (fun y => U.f (s * (y - c) / γ)) =
      (fun y => (fun z => U.f ((s / γ) * z)) (y - c)) := by
    ext y
    congr 1
    ring
  rw [heq, congrFun (iteratedDeriv_comp_sub_const N (fun z => U.f ((s / γ) * z)) c) x,
    iteratedDeriv_comp_const_mul (U.smooth.of_le (by simp) : ContDiff ℝ N U.f)]
  simp only
  congr 2
  ring

/-- The exact uniform derivative estimate in the paper, with a constant
that depends on the chosen transition and derivative order only. -/
 theorem softDigit_derivative_bound (U : SmoothStep) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ, 0 < γ → γ ≤ 1 / 4 →
      ∀ x, |iteratedDeriv N (softDigit U γ) x| ≤ C * γ ^ (-(N : ℤ)) := by
  obtain ⟨C, hC, hbound⟩ := U.derivative_bound N
  refine ⟨C, hC, ?_⟩
  intro γ hγ hγ1 x
  obtain ⟨c, s, hs, heq⟩ := softDigit_eventually_affine U γ x hγ hγ1
  rw [heq.iteratedDeriv_eq N, iteratedDeriv_affine, abs_mul, abs_pow, abs_div,
    hs, abs_of_pos hγ, one_div, inv_pow]
  have hpow : (γ ^ N)⁻¹ = γ ^ (-(N : ℤ)) := by simp
  rw [hpow]
  exact (mul_le_mul_of_nonneg_left (hbound _) (by positivity)).trans_eq (by ring)

end RoughRegime.LatticePriors
