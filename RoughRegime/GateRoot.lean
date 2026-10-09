module

public import RoughRegime.SelectorFrechet


@[expose] public section
/-! A deterministic root of the gate controls every actual phase coefficient.
This retains the gate factor in higher-order composition bounds. -/
noncomputable section
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.Lattice
variable {ι : Type*} [Fintype ι]

def gateRoot (S : ℝ) (K : ℕ) : ℝ := S ^ (1 / (K : ℝ))

theorem gateRoot_power (S : ℝ) (K : ℕ) (hS : 0 ≤ S) (hK : 0 < K) :
    gateRoot S K ^ K = S := by
  unfold gateRoot
  rw [← Real.rpow_mul_natCast hS]
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  rw [one_div_mul_cancel hk, Real.rpow_one]

theorem gateRoot_bounds (S : ℝ) (K : ℕ) (hS : 0 ≤ S) (hS1 : S ≤ 1) :
    0 ≤ gateRoot S K ∧ gateRoot S K ≤ 1 :=
  ⟨Real.rpow_nonneg hS _, Real.rpow_le_one hS hS1 (by positivity)⟩

/-- The original bounded-product gate inequality implies a single root-weighted
coefficient bound; no realization-dependent norm constant is introduced. -/
theorem gateRoot_coefficient_le (Q M K : ℕ) (lam η : ι → ℝ) (z : ι → ℤ)
    (hK : 0 < K) (hKQ : K ≤ 2 * Q) (hscale : ∀ i, 0 < lam i * η i) (i : ι) :
    gateRoot (blockGate Q M lam η z) K * |latticeStep M * z i| ≤ lam i * η i := by
  classical
  let r : ι → ℕ := fun j => if j = i then K else 0
  have hr (j : ι) : r j ≤ 2 * Q := by dsimp [r]; split_ifs <;> omega
  have hprod := blockGate_weighted_product Q M lam η z r hr hscale
  have heL : (∏ j, |latticeStep M * z j| ^ r j) = |latticeStep M * z i| ^ K := by
    simp [r]
  have heR : (∏ j, (lam j * η j) ^ r j) = (lam i * η i) ^ K := by
    simp [r]
  rw [heL, heR] at hprod
  have hs := blockGate_range Q M lam η z
  apply (pow_le_pow_iff_left₀ (mul_nonneg (gateRoot_bounds _ K hs.1 hs.2).1 (abs_nonneg _))
    (hscale i).le (Nat.ne_of_gt hK)).mp
  rw [mul_pow, gateRoot_power _ K hs.1 hK]
  exact hprod

/-- Every required power consumes at most the available gate degree. -/
theorem gateRoot_power_budget (S : ℝ) (K r : ℕ) (hS : 0 < S) (hS1 : S ≤ 1)
    (hK : 0 < K) (hr : r ≤ K) :
    S / gateRoot S K ^ r ≤ 1 := by
  have hb : 0 < gateRoot S K := Real.rpow_pos_of_pos hS _
  have hb1 := (gateRoot_bounds S K hS.le hS1).2
  apply (div_le_one (pow_pos hb r)).mpr
  have h := pow_le_pow_of_le_one hb.le hb1 hr
  rw [gateRoot_power S K hS.le hK] at h
  exact h

end RoughRegime.LatticePriors
