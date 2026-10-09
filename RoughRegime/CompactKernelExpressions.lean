module

public import RoughRegime.CompactKernelUniform
public import RoughRegime.KernelExpressions


@[expose] public section
/-! One actual complex tube and truncation bound for each fixed finite kernel
expression, uniform over a compact family of its original density endpoints. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Set Metric
namespace RoughRegime.KernelExpressions
open RoughRegime.ComplexKernel
theorem compact_expression_coefficients {p : ℕ} {I : Type*} {dims : I → ℕ}
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆RoughRegime.Model.densityIntervalDomain)
    (V : Set ((ℝ×ℝ)×(Fin p→ℂ))) (hV : Bornology.IsBounded V)
    (hVG : ∀ s∈V, s.1∈G)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hM : ∀ i, Continuous (M i))
    (hHerm : ∀ i s, s∈V → (M i s.2).IsHermitian)
    (hSpec : ∀ i s, s∈V → spectrum ℝ (M i s.2)⊆Icc s.1.1 s.1.2)
    (f : Expression p dims) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ (J : ℝ×ℝ) t, (∃ t0, (J,t0)∈V ∧ ‖t-t0‖ < ε) →
        Summable (fun k => ‖PowerSeries.coeff k (f.series J.1 J.2 M t)‖) ∧
          (∑' k, ‖PowerSeries.coeff k (f.series J.1 J.2 M t)‖) ≤ C := by
  let Vt : Set (Fin p→ℂ) := Prod.snd '' V
  have hVt : Bornology.IsBounded Vt :=
    hV.image (ContinuousLinearMap.snd ℝ (ℝ×ℝ) (Fin p→ℂ))
  induction f with
  | polynomial P =>
    obtain ⟨C0, hC0⟩ := hVt.isCompact_closure.cthickening.exists_bound_of_continuousOn
      (P.continuous_eval.continuousOn : ContinuousOn (fun t => MvPolynomial.eval t P)
        (cthickening 1 (closure Vt)))
    refine ⟨1, max C0 0, zero_lt_one, le_rfl, le_max_right _ _, ?_⟩
    intro J t ht
    obtain ⟨t0, ht0, hnear⟩ := ht
    have hmem : t ∈ cthickening 1 (closure Vt) := mem_cthickening_of_dist_le t t0 1 _
      (subset_closure (show t0∈Vt from ⟨(J,t0),ht0,rfl⟩)) (by simpa only [dist_eq_norm] using hnear.le)
    have hs : Summable (fun k => ‖PowerSeries.coeff k (PowerSeries.C (MvPolynomial.eval t P))‖) := by
      apply summable_of_ne_finset_zero (s := {0})
      intro k hk
      simp only [Finset.mem_singleton] at hk
      simp [PowerSeries.coeff_C, hk]
    refine ⟨hs, ?_⟩
    simp only [Expression.series, PowerSeries.coeff_C, apply_ite norm, norm_zero, tsum_ite_eq]
    exact (hC0 t hmem).trans (le_max_left _ _)
  | kernelEntry i a b =>
    have : Nonempty (Fin (dims i)) := ⟨a⟩
    obtain ⟨ε, B, q, hε, hε1, hB, hq, hq1, hb⟩ :=
      compact_bounded_joint_kernel_coefficients G hG hGood V hV hVG
        (M i) (hM i) (hHerm i) (hSpec i)
    let D := ‖entryCLM a b‖ * B
    have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) hB
    refine ⟨ε, D * (1 - q)⁻¹, hε, hε1, by positivity, ?_⟩
    intro J t ht
    have hc (k : ℕ) : ‖PowerSeries.coeff k
        ((Expression.kernelEntry i a b).series J.1 J.2 M t)‖ ≤ D * q ^ k := by
      simp only [Expression.series, PowerSeries.coeff_mk]
      exact (ContinuousLinearMap.le_opNorm (entryCLM a b) _).trans
        ((mul_le_mul_of_nonneg_left (hb J t ht k) (norm_nonneg _)).trans_eq (by dsimp [D]; ring))
    have hg := (summable_geometric_of_lt_one hq hq1).mul_left D
    have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hc hg
    refine ⟨hs, ?_⟩
    exact (hs.tsum_le_tsum hc hg).trans_eq (by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1])
  | add f g hf hg =>
    obtain ⟨εf, Cf, hεf, hεf1, hCf, hfb⟩ := hf
    obtain ⟨εg, Cg, hεg, hεg1, hCg, hgb⟩ := hg
    refine ⟨min εf εg, Cf + Cg, lt_min hεf hεg,
      (min_le_left _ _).trans hεf1, add_nonneg hCf hCg, ?_⟩
    intro J t ht
    obtain ⟨t0, ht0, hnear⟩ := ht
    have hf' := hfb J t ⟨t0, ht0, hnear.trans_le (min_le_left _ _)⟩
    have hg' := hgb J t ⟨t0, ht0, hnear.trans_le (min_le_right _ _)⟩
    have hh := coeff_add_norm_sum_le _ _ hf'.1 hg'.1
    exact ⟨hh.1, hh.2.trans (add_le_add hf'.2 hg'.2)⟩
  | mul f g hf hg =>
    obtain ⟨εf, Cf, hεf, hεf1, hCf, hfb⟩ := hf
    obtain ⟨εg, Cg, hεg, hεg1, hCg, hgb⟩ := hg
    refine ⟨min εf εg, Cf * Cg, lt_min hεf hεg,
      (min_le_left _ _).trans hεf1, mul_nonneg hCf hCg, ?_⟩
    intro J t ht
    obtain ⟨t0, ht0, hnear⟩ := ht
    have hf' := hfb J t ⟨t0, ht0, hnear.trans_le (min_le_left _ _)⟩
    have hg' := hgb J t ⟨t0, ht0, hnear.trans_le (min_le_right _ _)⟩
    have hh := coeff_mul_norm_sum_le _ _ hf'.1 hg'.1
    exact ⟨hh.1, hh.2.trans (mul_le_mul hf'.2 hg'.2 (tsum_nonneg (fun _ => norm_nonneg _)) hCf)⟩

/-- Lemma 5(b): the same constant bounds every combined-index truncation. -/
theorem compact_expression_truncations {p : ℕ} {I : Type*} {dims : I → ℕ}
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆RoughRegime.Model.densityIntervalDomain)
    (V : Set ((ℝ×ℝ)×(Fin p→ℂ))) (hV : Bornology.IsBounded V)
    (hVG : ∀ s∈V, s.1∈G)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hM : ∀ i, Continuous (M i))
    (hHerm : ∀ i s, s∈V → (M i s.2).IsHermitian)
    (hSpec : ∀ i s, s∈V → spectrum ℝ (M i s.2)⊆Icc s.1.1 s.1.2)
    (f : Expression p dims) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ (J : ℝ×ℝ) t, (∃ t0, (J,t0)∈V ∧ ‖t-t0‖ < ε) → ∀ m : ℕ,
        ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (f.series J.1 J.2 M t)‖ ≤ C := by
  obtain ⟨ε, C, hε, hε1, hC, hb⟩ :=
    compact_expression_coefficients G hG hGood V hV hVG M hM hHerm hSpec f
  refine ⟨ε, C, hε, hε1, hC, ?_⟩
  intro J t ht m
  exact (norm_sum_le _ _).trans (((hb J t ht).1.sum_le_tsum _ (fun _ _ => norm_nonneg _)).trans (hb J t ht).2)


 theorem compact_finite_expression_truncations {p : ℕ} {I K : Type*} {dims : I → ℕ}
    [Fintype K] (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆RoughRegime.Model.densityIntervalDomain)
    (V : Set ((ℝ×ℝ)×(Fin p→ℂ))) (hV : Bornology.IsBounded V)
    (hVG : ∀ s∈V, s.1∈G)
    (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hM : ∀ i, Continuous (M i))
    (hHerm : ∀ i s, s∈V → (M i s.2).IsHermitian)
    (hSpec : ∀ i s, s∈V → spectrum ℝ (M i s.2)⊆Set.Icc s.1.1 s.1.2)
    (f : K → Expression p dims) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ (R : ℝ×ℝ) t, (∃ t0, (R,t0)∈V ∧ ‖t-t0‖ < ε) → ∀ j m,
        ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k ((f j).series R.1 R.2 M t)‖ ≤ C := by
  classical
  have aux (s : Finset K) : ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧
      ∀ (R : ℝ×ℝ) t, (∃ t0, (R,t0)∈V ∧ ‖t-t0‖ < ε) → ∀ j ∈ s, ∀ m,
        ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k ((f j).series R.1 R.2 M t)‖ ≤ C := by
    induction s using Finset.induction with
    | empty => exact ⟨1, 0, by norm_num, le_rfl, le_rfl, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨εs, Cs, hεs, hεs1, hCs, hs⟩ := ih
      obtain ⟨εj, Cj, hεj, hεj1, hCj, hjb⟩ :=
        compact_expression_truncations G hG hGood V hV hVG M hM hHerm hSpec (f j)
      refine ⟨min εs εj, max Cs Cj, lt_min hεs hεj,
        (min_le_left _ _).trans hεs1, hCs.trans (le_max_left _ _), ?_⟩
      intro R t ht i hi m
      obtain ⟨t0, ht0, hnear⟩ := ht
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact (hjb R t ⟨t0, ht0, hnear.trans_le (min_le_right _ _)⟩ m).trans
          (le_max_right _ _)
      · exact (hs R t ⟨t0, ht0, hnear.trans_le (min_le_left _ _)⟩ i hi m).trans
          (le_max_left _ _)
  obtain ⟨ε, C, hε, hε1, hC, hb⟩ := aux Finset.univ
  exact ⟨ε, C, hε, hε1, hC, fun R t ht j m => hb R t ht j (Finset.mem_univ j) m⟩

end RoughRegime.KernelExpressions
