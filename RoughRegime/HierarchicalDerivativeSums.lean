module

public import RoughRegime.HierarchicalSums


@[expose] public section
/-! The true earlier-level derivative costs of the source hierarchy are
bounded by the last level, with constants independent of the hierarchy depth. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.LatticePriors

/-- The source weight is uniformly bounded whenever the source scale m exceeds
its coarsest exponential scale. -/
theorem sourceWeight_le_gamma (gammaStar alpha0 m : ℝ) (J b : ℕ)
    (hγ : 0 < gammaStar) (ha : 0 ≤ alpha0) (hb : b ≤ J)
    (hm : (2:ℝ)^((J:ℝ)*alpha0) ≤ m) :
    sourceWeight gammaStar alpha0 m b ≤ gammaStar := by
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  have hp : (2:ℝ)^((b:ℝ)*alpha0) ≤ m := by
    apply le_trans _ hm
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hb) ha)
  have hΓ : 0 < sourceGamma gammaStar b := by unfold sourceGamma; positivity
  have hΓle : sourceGamma gammaStar b ≤ gammaStar := by
    unfold sourceGamma
    apply (div_le_iff₀ (by positivity : 0 < ((b:ℝ)+1)^2)).mpr
    have hpow : (1:ℝ) ≤ ((b:ℝ)+1)^2 := one_le_pow₀ (by linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)])
    nlinarith
  unfold sourceWeight
  apply le_trans _ hΓle
  apply (div_le_iff₀ hm0).mpr
  exact mul_le_mul_of_nonneg_left hp hΓ.le

/-- All source spatial rates are at least one on their actual levels. -/
theorem sourceRate_ge_one (J b : ℕ) (gammaStar : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1) (hb : b ≤ J) :
    1 ≤ sourceRate J gammaStar b := by
  have hΓ : 0 < sourceGamma gammaStar b := by unfold sourceGamma; positivity
  have hΓ1 : sourceGamma gammaStar b ≤ 1 := by
    have hden : (1:ℝ) ≤ ((b:ℝ)+1)^2 := one_le_pow₀ (by linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)])
    unfold sourceGamma
    apply (div_le_iff₀ (by positivity : 0 < ((b:ℝ)+1)^2)).mpr
    linarith
  have hp : (1:ℝ) ≤ (2:ℝ)^((J:ℝ)-b) := Real.one_le_rpow (by norm_num) (by
    have hb' : (b:ℝ) ≤ J := by exact_mod_cast hb
    linarith)
  unfold sourceRate
  apply (le_div_iff₀ hΓ).mpr
  simpa only [one_mul] using hΓ1.trans hp

/-- Positive integer derivative costs of all preceding levels have a uniform
last-level bound. This is the precise geometric tail used in the telescope. -/
theorem source_derivative_tail_bound (gammaStar alpha0 : ℝ)
    (hγ : 0 < gammaStar) (ha : alpha0 < 1) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J b T : ℕ, ∀ m : ℝ, 0 < m →
      (∑ i ∈ Finset.range T,
        sourceWeight gammaStar alpha0 m (b+i) * sourceRate J gammaStar (b+i)^k) ≤
      C * (sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b^k) := by
  let r : ℝ := (2:ℝ)^(-((k:ℝ)-alpha0))
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
    have hkk : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  let p : ℕ := 2*(k-1)
  obtain ⟨C,hC,hbound⟩ := shifted_polynomial_geometric_tail_bound p r hr0 hr1
  refine ⟨C,hC,?_⟩
  intro J b T m hm
  have he (v : ℕ) : sourceWeight gammaStar alpha0 m v * sourceRate J gammaStar v^k =
      (((2:ℝ)^((J:ℝ)*(k:ℝ))/m)*gammaStar^(1-(k:ℝ))) * (((v:ℝ)+1)^p*r^v) := by
    rw [← Real.rpow_natCast,sourceWeight_rate_rpow J v gammaStar alpha0 m (k:ℝ) hγ]
    have hp : (2:ℝ)*((k:ℝ)-1) = (p:ℝ) := by
      dsimp [p]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    rw [hp,Real.rpow_natCast]
    dsimp [r]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hp : 0 ≤ ((2:ℝ)^((J:ℝ)*(k:ℝ))/m)*gammaStar^(1-(k:ℝ)) := by positivity
  have hz := mul_le_mul_of_nonneg_left (hbound T b) hp
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hz

end RoughRegime.LatticePriors
