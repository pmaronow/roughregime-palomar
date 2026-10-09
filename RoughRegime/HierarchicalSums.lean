module

public import RoughRegime.LatticeScales


@[expose] public section
/-! Uniform geometric sums for the concrete hierarchical Hölder scales. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.LatticePriors

/-- Real polynomial powers times a strictly decaying geometric sequence have
finite uniform partial-sum bounds, including negative polynomial exponents. -/
theorem partial_shifted_rpow_geometric_bound (p r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ,
      (∑ b ∈ Finset.range J, ((b : ℝ) + 1) ^ p * r ^ b) ≤ C := by
  let N := Nat.ceil p
  let f : ℕ → ℝ := fun b => ((b : ℝ) + 1) ^ N * r ^ b
  have hs : Summable f := summable_shifted_polynomial_geometric N r hr0 hr1
  have hf : ∀ b, 0 ≤ f b := fun b => by dsimp [f]; positivity
  refine ⟨∑' b, f b, tsum_nonneg hf, ?_⟩
  intro J
  calc
    _ ≤ ∑ b ∈ Finset.range J, f b := by
      apply Finset.sum_le_sum
      intro b _
      dsimp [f]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0.le _)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]) (Nat.le_ceil p)
    _ ≤ _ := hs.sum_le_tsum _ (fun b _ => hf b)

/-- The earlier-level ratio is controlled by a fixed convergent series,
uniformly in the current level and the number of preceding levels. -/
theorem shifted_polynomial_geometric_tail_bound (N : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ),
      (∑ i ∈ Finset.range a, ((b + i : ℕ) + 1 : ℝ) ^ N * r ^ (b + i)) ≤
        (((b : ℝ) + 1) ^ N * r ^ b) * C := by
  let f : ℕ → ℝ := fun i => ((i : ℝ) + 1) ^ N * r ^ i
  have hs : Summable f := summable_shifted_polynomial_geometric N r hr0 hr1
  have hf : ∀ i, 0 ≤ f i := fun i => by dsimp [f]; positivity
  refine ⟨∑' i, f i, tsum_nonneg hf, ?_⟩
  intro a b
  calc
    _ ≤ ∑ i ∈ Finset.range a, (((b : ℝ) + 1) ^ N * r ^ b) * f i := by
      apply Finset.sum_le_sum
      intro i _
      have hp : ((b + i : ℕ) + 1 : ℝ) ≤ ((b : ℝ) + 1) * ((i : ℝ) + 1) := by
        push_cast
        nlinarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b), (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp N) (pow_nonneg hr0.le (b + i))
      convert hh using 1
      simp only [mul_pow, pow_add]
      dsimp [f]
      ring
    _ = (((b : ℝ) + 1) ^ N * r ^ b) * ∑ i ∈ Finset.range a, f i := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun i _ => hf i)) (by positivity)

/-- The source coefficient scale after applying the gate. -/
def sourceWeight (gammaStar alpha0 m : ℝ) (b : ℕ) : ℝ :=
  sourceGamma gammaStar b * (2 : ℝ) ^ ((b : ℝ) * alpha0) / m

/-- The digit selector's inverse spatial width. -/
def sourceRate (J : ℕ) (gammaStar : ℝ) (b : ℕ) : ℝ :=
  (2 : ℝ) ^ ((J : ℝ) - b) / sourceGamma gammaStar b

/-- Exact hierarchical weight identity at an arbitrary real smoothness exponent. -/
theorem sourceWeight_rate_rpow (J b : ℕ) (gammaStar alpha0 m t : ℝ)
    (hγ : 0 < gammaStar) :
    sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b ^ t =
      ((2 : ℝ) ^ ((J : ℝ) * t) / m) * gammaStar ^ (1 - t) *
        (((b : ℝ) + 1) ^ (2 * (t - 1))) * ((2 : ℝ) ^ (-(t - alpha0))) ^ b := by
  have hΓ : 0 < sourceGamma gammaStar b := by unfold sourceGamma; positivity
  have hb : 0 < (b : ℝ) + 1 := by positivity
  have hGamma : sourceGamma gammaStar b / sourceGamma gammaStar b ^ t =
      gammaStar ^ (1 - t) * ((b : ℝ) + 1) ^ (2 * (t - 1)) := by
    calc
      _ = sourceGamma gammaStar b ^ (1 - t) := by rw [Real.rpow_sub hΓ, Real.rpow_one]
      _ = _ := by
        unfold sourceGamma
        rw [Real.div_rpow hγ.le (by positivity), ← Real.rpow_two,
          ← Real.rpow_mul hb.le, div_eq_mul_inv, ← Real.rpow_neg hb.le]
        congr 1
        ring
  have hTwo : (2 : ℝ) ^ ((b : ℝ) * alpha0) * ((2 : ℝ) ^ ((J : ℝ) - b)) ^ t =
      (2 : ℝ) ^ ((J : ℝ) * t) * ((2 : ℝ) ^ (-(t - alpha0))) ^ b := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  unfold sourceWeight sourceRate
  rw [Real.div_rpow (by positivity) hΓ.le]
  calc
    _ = (sourceGamma gammaStar b / sourceGamma gammaStar b ^ t) *
      ((2 : ℝ) ^ ((b : ℝ) * alpha0) * ((2 : ℝ) ^ ((J : ℝ) - b)) ^ t) / m := by ring
    _ = _ := by rw [hGamma, hTwo]; ring

/-- The complete source sum of Hölder costs has a constant independent of J and m. -/
theorem source_holder_cost_sum_bound (gammaStar alpha0 t : ℝ)
    (hγ : 0 < gammaStar) (ht : alpha0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : ℕ) (m : ℝ), 0 < m →
      (∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b ^ t) ≤
        C * (2 : ℝ) ^ ((J : ℝ) * t) / m := by
  let r : ℝ := (2 : ℝ) ^ (-(t - alpha0))
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨D, hD, hbound⟩ := partial_shifted_rpow_geometric_bound (2 * (t - 1)) r hr0 hr1
  refine ⟨gammaStar ^ (1 - t) * D, by positivity, ?_⟩
  intro J m hm
  simp_rw [sourceWeight_rate_rpow J _ gammaStar alpha0 m t hγ]
  have h := mul_le_mul_of_nonneg_left (hbound J)
    (show 0 ≤ ((2 : ℝ) ^ ((J : ℝ) * t) / m) * gammaStar ^ (1 - t) by positivity)
  calc
    _ = (((2 : ℝ) ^ ((J : ℝ) * t) / m) * gammaStar ^ (1 - t)) *
      (∑ b ∈ Finset.range J, ((b : ℝ) + 1) ^ (2 * (t - 1)) * r ^ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp [r]
      ring
    _ ≤ _ := h
    _ = _ := by ring

end RoughRegime.LatticePriors
