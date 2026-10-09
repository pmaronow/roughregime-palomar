module

public import RoughRegime.KernelExpressionFinite


@[expose] public section
/-! A common complex neighborhood for any actual finite family of expressions. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.KernelExpressions

 theorem uniform_finite_expression_truncations {p : ℕ} {I J : Type*} {dims : I → ℕ}
    [Fintype J] (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℂ)) (hV : Bornology.IsBounded V)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hM : ∀ i, Continuous (M i))
    (hHerm : ∀ i t, t ∈ V → (M i t).IsHermitian)
    (hSpec : ∀ i t, t ∈ V → spectrum ℝ (M i t) ⊆ Set.Icc lo hi)
    (f : J → Expression p dims) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) → ∀ j m,
        ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k ((f j).series lo hi M t)‖ ≤ C := by
  classical
  have aux (s : Finset J) : ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) → ∀ j ∈ s, ∀ m,
        ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k ((f j).series lo hi M t)‖ ≤ C := by
    induction s using Finset.induction with
    | empty => exact ⟨1, 0, by norm_num, le_rfl, le_rfl, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨εs, Cs, hεs, hεs1, hCs, hs⟩ := ih
      obtain ⟨εj, Cj, hεj, hεj1, hCj, hjb⟩ :=
        uniform_expression_truncations lo hi hlo hlt V hV M hM hHerm hSpec (f j)
      refine ⟨min εs εj, max Cs Cj, lt_min hεs hεj,
        (min_le_left _ _).trans hεs1, hCs.trans (le_max_left _ _), ?_⟩
      intro t ht i hi m
      obtain ⟨t0, ht0, hnear⟩ := ht
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact (hjb t ⟨t0, ht0, hnear.trans_le (min_le_right _ _)⟩ m).trans
          (le_max_right _ _)
      · exact (hs t ⟨t0, ht0, hnear.trans_le (min_le_left _ _)⟩ i hi m).trans
          (le_max_left _ _)
  obtain ⟨ε, C, hε, hε1, hC, hb⟩ := aux Finset.univ
  exact ⟨ε, C, hε, hε1, hC, fun t ht j m => hb t ht j (Finset.mem_univ j) m⟩

end RoughRegime.KernelExpressions
