module

public import RoughRegime.ScalarExponentialTail


@[expose] public section
/-! Reindexing of genuine summable Poisson coefficient tails. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.PoissonSeriesBounds

lemma tsum_supported_shift (f : ℕ → ℝ) (q : ℕ) (hf : Summable f)
    (hzero : ∀ k, k < q → f k = 0) :
    (∑' k, f k) = ∑' j, f (j + q) := by
  have hfin : ∑ k ∈ Finset.range q, f k = 0 :=
    Finset.sum_eq_zero (fun k hk => hzero k (Finset.mem_range.mp hk))
  simpa [hfin] using (hf.sum_add_tsum_nat_add q).symm

lemma summable_cutoff (f : ℕ → ℝ) (hf : Summable f) (M : ℕ) :
    Summable (fun k => if M ≤ k then f k else 0) := by
  exact (hf.indicator {k | M ≤ k}).congr (fun k => by simp [Set.indicator_apply])

/-- Removing two occupied labels contributes the actual `z²` factor, even when
only the weighted scalar coefficient series is assumed summable. -/
theorem two_label_tail (z : ℝ) (hz : 0 ≤ z) (M : ℕ) (Γ : ℕ → ℝ)
    (hΓ : ∀ j, 0 ≤ Γ j)
    (hs : Summable (fun j => z ^ j / j.factorial * Γ j)) :
    Summable (fun k => if M + 2 ≤ k then z ^ k / k.factorial * Γ (k - 2) else 0) ∧
    (∑' k, if M + 2 ≤ k then z ^ k / k.factorial * Γ (k - 2) else 0) ≤
      z ^ 2 * ∑' j, if M ≤ j then z ^ j / j.factorial * Γ j else 0 := by
  let f : ℕ → ℝ := fun k => if M + 2 ≤ k then z ^ k / k.factorial * Γ (k - 2) else 0
  let g : ℕ → ℝ := fun j => if M ≤ j then z ^ j / j.factorial * Γ j else 0
  have hg : Summable g := summable_cutoff _ hs M
  have hbound (j : ℕ) : f (j + 2) ≤ z ^ 2 * g j := by
    dsimp [f, g]
    by_cases hj : M ≤ j
    · have hcut : M + 2 ≤ j + 2 := by omega
      simp only [hcut, hj, ite_true, Nat.add_sub_cancel]
      have hd : z ^ (j + 2) / (j + 2).factorial ≤ z ^ (j + 2) / j.factorial :=
        div_le_div_of_nonneg_left (pow_nonneg hz _) (by positivity)
          (by exact_mod_cast Nat.factorial_le (by omega : j ≤ j + 2))
      calc
        _ ≤ z ^ (j + 2) / j.factorial * Γ j := mul_le_mul_of_nonneg_right hd (hΓ j)
        _ = _ := by rw [pow_add]; ring
    · have hcut : ¬ M + 2 ≤ j + 2 := by omega
      simp [hj, hcut]
  have hn (j : ℕ) : 0 ≤ f j := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (div_nonneg (pow_nonneg hz _) (by positivity)) (hΓ _)
    · exact le_rfl
  have hshift : Summable (fun j => f (j + 2)) :=
    Summable.of_nonneg_of_le (fun j => hn _) hbound (hg.mul_left (z ^ 2))
  have hf : Summable f := (summable_nat_add_iff 2).mp hshift
  refine ⟨hf, ?_⟩
  calc
    (∑' k, f k) = ∑' j, f (j + 2) := tsum_supported_shift f 2 hf (by
      intro k hk
      dsimp [f]
      rw [ite_eq_right (by omega)])
    _ ≤ ∑' j, z ^ 2 * g j := hshift.tsum_le_tsum hbound (hg.mul_left _)
    _ = z ^ 2 * ∑' j, g j := tsum_mul_left

/-- The actual conditional Poisson tail starts at `M+4`, and is reindexed before
applying the factorial exponential bound. -/
theorem fourth_label_tail (z : ℝ) (hz : 0 ≤ z) (M : ℕ) :
    Summable (fun k => if M + 4 ≤ k then z ^ k / k.factorial else 0) ∧
    (∑' k, if M + 4 ≤ k then z ^ k / k.factorial else 0) ≤
      z ^ 4 * (z ^ M / M.factorial) * Real.exp z := by
  let f : ℕ → ℝ := fun k => if M + 4 ≤ k then z ^ k / k.factorial else 0
  have hf : Summable f := summable_cutoff _ (Real.summable_pow_div_factorial z) (M + 4)
  refine ⟨hf, ?_⟩
  calc
    (∑' k, f k) = ∑' j, f (j + (M + 4)) := tsum_supported_shift f (M + 4) hf (by
      intro k hk
      dsimp [f]
      rw [ite_eq_right (by omega)])
    _ = ∑' j : ℕ, z ^ (j + M + 4) / (j + M + 4).factorial := by
      apply tsum_congr
      intro j
      simp [f, Nat.add_assoc, show M + 4 ≤ j + (M + 4) by omega]
    _ ≤ _ := ScalarExponentialTail.shifted_fourth_exponential_tail z hz M

end RoughRegime.PoissonSeriesBounds
