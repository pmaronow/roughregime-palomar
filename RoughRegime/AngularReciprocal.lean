module

public import RoughRegime.Upper


@[expose] public section
/-! Exact angular reciprocal coefficients used in Lemma14(d). -/
noncomputable section
open MeasureTheory Set
open RoughRegime.Upper

namespace RoughRegime.LatticeFourier

theorem integral_cos_integer_frequency (n : ℤ) (φ : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos ((n : ℝ) * θ + φ)) =
      if n = 0 then 2 * Real.pi * Real.cos φ else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, zero_mul, zero_add, ite_true,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  · rw [ite_eq_right hn, intervalIntegral.integral_comp_mul_add Real.cos
      (by exact_mod_cast hn) φ, integral_cos]
    have he : (n : ℝ) * (2 * Real.pi) + φ = φ + n * (2 * Real.pi) := by ring
    rw [he, Real.sin_add_int_mul_two_pi]
    simp

theorem integral_cos_product (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (φ : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((M : ℝ) * θ) * Real.cos ((N : ℝ) * (θ + φ))) =
        if N = M then Real.pi * Real.cos ((M : ℝ) * φ) else 0 := by
  have he (θ : ℝ) : Real.cos ((M : ℝ) * θ) * Real.cos ((N : ℝ) * (θ + φ)) =
      (Real.cos ((((M : ℤ) - N : ℤ) : ℝ) * θ + (-(N : ℝ) * φ)) +
        Real.cos ((((M : ℤ) + N : ℤ) : ℝ) * θ + ((N : ℝ) * φ))) / 2 := by
    have hd : (((M : ℤ) - N : ℤ) : ℝ) * θ + (-(N : ℝ) * φ) =
        (M : ℝ) * θ - (N : ℝ) * (θ + φ) := by push_cast; ring
    have hs : (((M : ℤ) + N : ℤ) : ℝ) * θ + ((N : ℝ) * φ) =
        (M : ℝ) * θ + (N : ℝ) * (θ + φ) := by push_cast; ring
    rw [hd, hs, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _), integral_cos_integer_frequency,
    integral_cos_integer_frequency]
  have hplus : (M : ℤ) + N ≠ 0 := by omega
  rw [ite_eq_right hplus]
  by_cases hNM : N = M
  · subst N
    simp only [sub_self, ite_true, neg_mul, Real.cos_neg, add_zero]
    ring
  · have hsub : (M : ℤ) - N ≠ 0 := by omega
    rw [ite_eq_right hsub, ite_eq_right hNM]
    simp

/-- The exact M-th coefficient, including its sign before imposing even M. -/
theorem angular_reciprocal_coefficient (lo hi φ : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : ℕ) (hM : 0 < M) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((M : ℝ) * θ) /
        (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos (θ + φ))) /
      (2 * Real.pi) =
        (-intervalRho lo hi) ^ M * Real.cos ((M : ℝ) * φ) / intervalGeometricMean lo hi := by
  let ρ := intervalRho lo hi
  let g := intervalGeometricMean lo hi
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let F (k : ℕ) (θ : ℝ) := Real.cos ((M : ℝ) * θ) *
    ((-ρ) ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * (θ + φ)))
  let R (θ : ℝ) := Real.cos ((M : ℝ) * θ) /
    (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos (θ + φ))
  have hρ : 0 < ρ := intervalRho_pos lo hi hlo hlt
  have hρ1 : ρ < 1 := intervalRho_lt_one lo hi hlo hlt
  have hg : 0 < g := by
    unfold g intervalGeometricMean
    apply Real.sqrt_pos.mpr
    exact mul_pos hlo (hlo.trans hlt)
  have hμ : μ.real univ = 2 * Real.pi := by
    simp [μ, measureReal_def, Real.volume_Ioc, Real.pi_pos.le]
  have hFcont (k : ℕ) : Continuous (F k) := by fun_prop
  have hFint (k : ℕ) : Integrable (F k) μ := (hFcont k).integrableOn_Ioc
  have hFbound (k : ℕ) (θ : ℝ) : ‖F k θ‖ ≤ ρ ^ (k + 1) := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos hρ]
    calc
      _ = ρ ^ (k + 1) *
        (|Real.cos ((M : ℝ) * θ)| * |Real.cos (((k + 1 : ℕ) : ℝ) * (θ + φ))|) := by ring
      _ ≤ ρ ^ (k + 1) * (1 * 1) := by
        gcongr
        · exact Real.abs_cos_le_one _
        · exact Real.abs_cos_le_one _
      _ = _ := by ring
  have hFnint (k : ℕ) : (∫ θ, ‖F k θ‖ ∂μ) ≤ ρ ^ (k + 1) * (2 * Real.pi) := by
    have hh := integral_mono_ae (hFint k).norm (integrable_const (ρ ^ (k + 1)))
      (Filter.Eventually.of_forall (hFbound k))
    rw [integral_const, hμ, smul_eq_mul] at hh
    nlinarith
  have hgeom : Summable (fun k : ℕ => ρ ^ (k + 1) * (2 * Real.pi)) := by
    simpa only [pow_succ, mul_assoc] using
      (summable_geometric_of_lt_one hρ.le hρ1).mul_right (ρ * (2 * Real.pi))
  have hsum : Summable (fun k : ℕ => ∫ θ, ‖F k θ‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (fun θ => norm_nonneg _)) hFnint hgeom
  have hterm (k : ℕ) : (∫ θ, F k θ ∂μ) =
      (-ρ) ^ (k + 1) *
        (if k + 1 = M then Real.pi * Real.cos ((M : ℝ) * φ) else 0) := by
    rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have he : F k = fun θ => (-ρ) ^ (k + 1) *
        (Real.cos ((M : ℝ) * θ) * Real.cos (((k + 1 : ℕ) : ℝ) * (θ + φ))) := by
      funext θ
      dsimp [F]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_cos_product M (k + 1) hM (by omega)]
  have hsumterm : (∑' k : ℕ, ∫ θ, F k θ ∂μ) =
      (-ρ) ^ M * Real.pi * Real.cos ((M : ℝ) * φ) := by
    rw [tsum_eq_single (M - 1) (fun k hk => by
      rw [hterm, ite_eq_right (by omega : k + 1 ≠ M), mul_zero])]
    rw [hterm]
    have hsucc : M - 1 + 1 = M := by omega
    simp [hsucc, mul_assoc]
  have hRcont : Continuous R := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ
    exact (interval_angular_pos lo hi (θ + φ) hlo hlt).ne'
  have hRint : Integrable R μ := hRcont.integrableOn_Ioc
  have hCint : Integrable (fun θ : ℝ => Real.cos ((M : ℝ) * θ)) μ :=
    (by fun_prop : Continuous (fun θ : ℝ => Real.cos ((M : ℝ) * θ))).integrableOn_Ioc
  have hpoint (θ : ℝ) : (∑' k : ℕ, F k θ) =
      (g * R θ - Real.cos ((M : ℝ) * θ)) / 2 := by
    have hd : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
    let x := intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos (θ + φ)
    have hx : x ∈ Icc lo hi := by
      dsimp [x]
      have hc0 := Real.neg_one_le_cos (θ + φ)
      have hc1 := Real.cos_le_one (θ + φ)
      constructor <;> unfold intervalCenter intervalHalfWidth at * <;> nlinarith
    have hr := reciprocal_real_series lo hi x hlo hlt hx
    have harg : (x - intervalCenter lo hi) / intervalHalfWidth lo hi = Real.cos (θ + φ) := by
      dsimp [x]
      field_simp
      ring
    rw [harg] at hr
    have heval (k : ℕ) :
        (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval (Real.cos (θ + φ)) =
          Real.cos (((k + 1 : ℕ) : ℝ) * (θ + φ)) := by
      exact Polynomial.Chebyshev.T_real_cos (θ + φ) (k + 1 : ℕ)
    simp_rw [heval] at hr
    dsimp only [F]
    rw [tsum_mul_left]
    dsimp only [ρ, g, R, x] at *
    simp only [div_eq_mul_inv] at *
    linear_combination (Real.cos ((M : ℝ) * θ) / 2) * hr
  have hI : (∫ θ, (∑' k : ℕ, F k θ) ∂μ) =
      (g * (∫ θ, R θ ∂μ) - (∫ θ, Real.cos ((M : ℝ) * θ) ∂μ)) / 2 := by
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hRint.const_mul g) hCint, integral_const_mul]
  have hC : (∫ θ, Real.cos ((M : ℝ) * θ) ∂μ) = 0 := by
    rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have he := integral_cos_integer_frequency M 0
    simpa only [Int.cast_natCast, add_zero, ite_eq_right (by omega : (M : ℤ) ≠ 0)] using he
  rw [← (integral_tsum_of_summable_integral_norm hFint hsum), hsumterm, hC, sub_zero] at hI
  change (∫ θ in (0 : ℝ)..2 * Real.pi, R θ) / (2 * Real.pi) = (-ρ) ^ M * Real.cos ((M : ℝ) * φ) / g
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  apply (div_eq_div_iff (by positivity) hg.ne').mpr
  nlinarith [hI]

/-- The source chooses even M, removing the alternating coefficient sign. -/
theorem angular_reciprocal_coefficient_even (lo hi φ : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (M : ℕ) (hM : 0 < M) (heven : Even M) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((M : ℝ) * θ) /
        (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos (θ + φ))) /
      (2 * Real.pi) =
        intervalRho lo hi ^ M * Real.cos ((M : ℝ) * φ) / intervalGeometricMean lo hi := by
  rw [angular_reciprocal_coefficient lo hi φ hlo hlt M hM, heven.neg_pow]

/-- The two paired block signs (and any integer multiple of pi) have the same
coefficient at the source's even frequency. -/
theorem angular_reciprocal_coefficient_even_offset (lo hi φ : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (M b : ℕ) (hM : 0 < M) (heven : Even M) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((M : ℝ) * θ) /
        (intervalCenter lo hi + intervalHalfWidth lo hi *
          Real.cos (θ + φ + (b : ℝ) * Real.pi))) / (2 * Real.pi) =
        intervalRho lo hi ^ M * Real.cos ((M : ℝ) * φ) / intervalGeometricMean lo hi := by
  have hcos : Real.cos ((M : ℝ) * (φ + (b : ℝ) * Real.pi)) = Real.cos ((M : ℝ) * φ) := by
    have he : (M : ℝ) * (φ + (b : ℝ) * Real.pi) =
        (M : ℝ) * φ + ((M * b : ℕ) : ℝ) * Real.pi := by push_cast; ring
    rw [he, Real.cos_add_nat_mul_pi, (heven.mul_right b).neg_one_pow, one_mul]
  simpa only [← add_assoc, hcos] using
    angular_reciprocal_coefficient_even lo hi (φ + b * Real.pi) hlo hlt M hM heven

end RoughRegime.LatticeFourier
