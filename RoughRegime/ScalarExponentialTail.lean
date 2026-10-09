module

public import Mathlib


@[expose] public section
/-! Factorial exponential tails used in the actual Poisson-mixture remainders. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.ScalarExponentialTail

lemma factorial_supermultiplicative (M j : ℕ) :
    (M.factorial : ℝ) * j.factorial ≤ (j + M).factorial := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (j + M))
    (by simpa only [Nat.add_comm, Nat.mul_comm] using Nat.factorial_mul_factorial_dvd_factorial_add M j)

lemma exp_series_sum (z : ℝ) : (∑' j : ℕ, z ^ j / j.factorial) = Real.exp z := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- A shifted exponential remainder has the source factorial tail bound. -/
theorem exponential_tail (z : ℝ) (hz : 0 ≤ z) (M : ℕ) :
    (∑' j : ℕ, z ^ (j + M) / (j + M).factorial) ≤
      z ^ M / M.factorial * Real.exp z := by
  have hs : Summable (fun j : ℕ => z ^ (j + M) / (j + M).factorial) :=
    (summable_nat_add_iff M).mpr (Real.summable_pow_div_factorial z)
  have hb (j : ℕ) : z ^ (j + M) / (j + M).factorial ≤
      (z ^ M / M.factorial) * (z ^ j / j.factorial) := by
    calc
      _ ≤ z ^ (j + M) / ((M.factorial : ℝ) * j.factorial) :=
        div_le_div_of_nonneg_left (pow_nonneg hz _) (by positivity)
          (factorial_supermultiplicative M j)
      _ = _ := by rw [pow_add]; ring
  have hg := (Real.summable_pow_div_factorial z).mul_left (z ^ M / M.factorial)
  exact (hs.tsum_le_tsum hb hg).trans_eq (by rw [tsum_mul_left, exp_series_sum])

/-- The denominator may start two degrees earlier, as in the source fourth-order
Poisson-label remainder. -/
theorem fourth_order_remainder (z A : ℝ) (hz : 0 ≤ z) (hA : 0 ≤ A) :
    Summable (fun j : ℕ => z ^ (j + 4) * A ^ (j + 2) / (j + 2).factorial) ∧
    (∑' j : ℕ, z ^ (j + 4) * A ^ (j + 2) / (j + 2).factorial) ≤
      z ^ 4 * A ^ 2 * Real.exp (z * A) := by
  have hb (j : ℕ) : z ^ (j + 4) * A ^ (j + 2) / (j + 2).factorial ≤
      (z ^ 4 * A ^ 2) * ((z * A) ^ j / j.factorial) := by
    calc
      _ ≤ z ^ (j + 4) * A ^ (j + 2) / j.factorial :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by exact_mod_cast Nat.factorial_le (by omega : j ≤ j + 2))
      _ = _ := by rw [pow_add, pow_add, mul_pow]; ring
  have hg := (Real.summable_pow_div_factorial (z * A)).mul_left (z ^ 4 * A ^ 2)
  have hs := Summable.of_nonneg_of_le (fun _ => by positivity) hb hg
  refine ⟨hs, ?_⟩
  exact (hs.tsum_le_tsum hb hg).trans_eq (by rw [tsum_mul_left, exp_series_sum])

/-- The combined label-count tail starts four indices after the matched-density
order, while retaining the source denominator `M!`. -/
theorem shifted_fourth_exponential_tail (z : ℝ) (hz : 0 ≤ z) (M : ℕ) :
    (∑' i : ℕ, z ^ (i + M + 4) / (i + M + 4).factorial) ≤
      z ^ 4 * (z ^ M / M.factorial) * Real.exp z := by
  have he := exponential_tail z hz (M + 4)
  simp only [Nat.add_assoc] at he ⊢
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos z).le
  calc
    z ^ (M + 4) / (M + 4).factorial ≤ z ^ (M + 4) / M.factorial :=
      div_le_div_of_nonneg_left (pow_nonneg hz _) (by positivity)
        (by exact_mod_cast Nat.factorial_le (by omega : M ≤ M + 4))
    _ = _ := by rw [pow_add]; ring

end RoughRegime.ScalarExponentialTail
