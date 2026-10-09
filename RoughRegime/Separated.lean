module

public import Mathlib


@[expose] public section
namespace RoughRegime.Window

open scoped BigOperators

/-- The kth point of a nonnegative δ-separated finite set lies at least kδ from zero. -/
theorem orderEmbOfFin_ge_mul_sep (S : Finset ℝ) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|)
    (k : Fin S.card) : (k.val : ℝ) * δ ≤ S.orderEmbOfFin rfl k := by
  have hrank : ∀ (n : ℕ) (hn : n < S.card),
      (n : ℝ) * δ ≤ S.orderEmbOfFin rfl ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      simpa using hnonneg _ (S.orderEmbOfFin_mem rfl ⟨0, hn⟩)
    | succ n ih =>
      intro hn
      have hn' : n < S.card := Nat.lt_trans (Nat.lt_succ_self n) hn
      have hlt : S.orderEmbOfFin rfl ⟨n, hn'⟩ <
          S.orderEmbOfFin rfl ⟨n + 1, hn⟩ :=
        (S.orderEmbOfFin rfl).strictMono (by simp)
      have hstep := hsep _ (S.orderEmbOfFin_mem rfl ⟨n + 1, hn⟩)
        _ (S.orderEmbOfFin_mem rfl ⟨n, hn'⟩) (ne_of_gt hlt)
      rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at hstep
      have hi := ih hn'
      push_cast
      linarith
  exact hrank k.val k.isLt

/-- A separated finite Gaussian sum is bounded by its equally spaced comparison sum. -/
theorem separated_gaussian_sum_le (S : Finset ℝ) {δ c : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ∑ x ∈ S, Real.exp (-c * x ^ 2) ≤
      ∑ k ∈ Finset.range S.card, Real.exp (-(c * δ ^ 2) * (k : ℝ) ^ 2) := by
  have hsum : ∑ x ∈ S, Real.exp (-c * x ^ 2) =
      ∑ k : Fin S.card, Real.exp (-c * (S.orderEmbOfFin rfl k) ^ 2) := by
    simpa only [Finset.sum_map, RelEmbedding.coe_toEmbedding] using
      congrArg (fun t : Finset ℝ => ∑ x ∈ t, Real.exp (-c * x ^ 2))
        (S.map_orderEmbOfFin_univ (k := S.card) rfl).symm
  rw [hsum]
  calc
    (∑ k : Fin S.card, Real.exp (-c * (S.orderEmbOfFin rfl k) ^ 2)) ≤
        ∑ k : Fin S.card, Real.exp (-(c * δ ^ 2) * (k.val : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      apply Real.exp_le_exp.mpr
      have hn := hnonneg _ (S.orderEmbOfFin_mem rfl k)
      have hk := orderEmbOfFin_ge_mul_sep S hδ.le hnonneg hsep k
      have hp : 0 ≤ (k.val : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      have hs := (sq_le_sq₀ hp hn).mpr hk
      nlinarith
    _ = ∑ k ∈ Finset.range S.card, Real.exp (-(c * δ ^ 2) * (k : ℝ) ^ 2) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range.mp hk]

end RoughRegime.Window
