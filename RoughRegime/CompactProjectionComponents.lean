module

public import RoughRegime.CompactKernelExpressions
public import RoughRegime.ProjectionIncrementComplex


@[expose] public section
/-! Actual projection polynomials on a common complex tube for compact original
spectral endpoints. Each polynomial retains its own endpoints and coefficients. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial Set
namespace RoughRegime.ProjectionComplex
open RoughRegime.KernelExpressions RoughRegime.ComplexPolynomialKernel
open RoughRegime.CombinedPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.Upper RoughRegime.ComplexDerivativeBridge

def unscaledEntryExpression {p N n : ℕ} (dims : Fin N → ℕ) (a b : Fin n) :
    Expression p (kernelFamilyDims n dims) :=
  .mul (.kernelEntry none a b)
    (indexedProd (fun i : Fin N => determinantExpression (some i)))

lemma truncationPolynomialMatrix_complex_eval_unscaled {p N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ))
    (t : Fin p → ℂ) (m : ℕ) (a b : Fin n) :
    complexEvaluation t (truncationPolynomialMatrix lo hi Ω M m a b) =
      (((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ : ℝ) : ℂ) *
      ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k
        ((unscaledEntryExpression dims a b).series lo hi (kernelFamily Ω M) t) := by
  rw [truncationPolynomialMatrix_complex_eval]
  simp only [entryExpression, unscaledEntryExpression, Expression.series,
    MvPolynomial.eval_C, PowerSeries.coeff_C_mul, Finset.mul_sum]

lemma compact_geometricMean_inverse_bound (G : Set (ℝ×ℝ)) (hG : IsCompact G)
    (hGood : G ⊆ RoughRegime.Model.densityIntervalDomain) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ I ∈ G,
      ‖(((intervalGeometricMean I.1 I.2 ^ k)⁻¹ : ℝ) : ℂ)‖ ≤ B := by
  have hc : ContinuousOn (fun I : ℝ×ℝ => (intervalGeometricMean I.1 I.2 ^ k)⁻¹) G := by
    apply ContinuousOn.inv₀
    · exact (Real.continuous_sqrt.comp (continuous_fst.mul continuous_snd)).continuousOn.pow k
    · intro I hI
      have h := hGood hI
      change 0 < I.1 ∧ I.1 < I.2 at h
      exact pow_ne_zero k (ne_of_gt (Real.sqrt_pos.2 (mul_pos h.1 (h.1.trans h.2))))
  obtain ⟨B, hB⟩ := hG.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro I hI
  rw [Complex.norm_real]
  exact (hB I hI).trans (le_max_left _ _)

theorem compact_uniform_bilinear_truncations {p N n : ℕ} {dims : Fin N → ℕ}
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G ⊆ RoughRegime.Model.densityIntervalDomain)
    (V : Set ((ℝ×ℝ)×(Fin p→ℂ))) (hV : Bornology.IsBounded V)
    (hVG : ∀ s∈V, s.1∈G)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ))
    (hHerm : ∀ i s, s∈V → (kernelFamily Ω M i s.2).IsHermitian)
    (hSpec : ∀ i s, s∈V → spectrum ℝ (kernelFamily Ω M i s.2) ⊆ Set.Icc s.1.1 s.1.2)
    (u v : Fin n → MvPolynomial (Fin p) ℝ) :
    ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ A ∧
      ∀ (I : ℝ×ℝ) t, (∃ t0, (I,t0)∈V ∧ ‖t-t0‖ < ε) →
        (∀ i, ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A) ∧
        (∀ i, ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A) ∧
        (∀ m i j, ‖MvPolynomial.eval t
          (complexify (truncationPolynomialMatrix I.1 I.2 Ω M m i j))‖ ≤ A) ∧
        (∀ m, ‖MvPolynomial.eval t (complexify
          (bilinearPolynomial u (truncationPolynomialMatrix I.1 I.2 Ω M m) v))‖ ≤
            (n : ℝ) ^ 2 * A ^ 3) := by
  let f : ((Fin n ⊕ Fin n) ⊕ (Fin n × Fin n)) → Expression p (kernelFamilyDims n dims)
    | Sum.inl (Sum.inl i) => .polynomial (complexify (u i))
    | Sum.inl (Sum.inr i) => .polynomial (complexify (v i))
    | Sum.inr ij => unscaledEntryExpression dims ij.1 ij.2
  have hM : ∀ i, Continuous (kernelFamily Ω M i) := by
    intro i
    cases i <;> exact continuous_pi (fun a => continuous_pi (fun b => complexEvaluation_continuous _))
  obtain ⟨ε, C, hε, hε1, hC, hb⟩ := compact_finite_expression_truncations
    G hG hGood V hV hVG (kernelFamily Ω M) hM hHerm hSpec f
  obtain ⟨B, hB, hbb⟩ := compact_geometricMean_inverse_bound G hG hGood ((∑ i, dims i) + 1)
  let A := max C (B*C)
  have hA : 0 ≤ A := hC.trans (le_max_left _ _)
  refine ⟨ε, A, hε, hε1, hA, ?_⟩
  intro I t ht
  have hu (i : Fin n) : ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A := by
    apply le_trans _ (le_max_left _ _)
    simpa [f, Expression.series] using hb I t ht (Sum.inl (Sum.inl i)) 0
  have hv (i : Fin n) : ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A := by
    apply le_trans _ (le_max_left _ _)
    simpa [f, Expression.series] using hb I t ht (Sum.inl (Sum.inr i)) 0
  have hS (m : ℕ) (i j : Fin n) :
      ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix I.1 I.2 Ω M m i j))‖ ≤ A := by
    rw [← complexEvaluation_eq, truncationPolynomialMatrix_complex_eval_unscaled, norm_mul]
    have htcopy := ht
    obtain ⟨t0, ht0, _⟩ := htcopy
    exact (mul_le_mul (hbb I (hVG (I,t0) ht0)) (hb I t ht (Sum.inr (i,j)) m)
      (norm_nonneg _) hB).trans (le_max_right _ _)
  exact ⟨hu, hv, hS, fun m => bilinearPolynomial_complex_bound t u v _ A hA hu hv (hS m)⟩
end RoughRegime.ProjectionComplex

namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.KernelExpressions RoughRegime.ProjectionComplex RoughRegime.ComplexGram
open RoughRegime.ProjectionPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ComplexDerivativeBridge

theorem compact_uniform_incrementPolynomial_components {p n a b : ℕ}
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G ⊆ RoughRegime.Model.densityIntervalDomain)
    (V : Set ((ℝ×ℝ)×(Fin p→ℝ))) (hV : Bornology.IsBounded V)
    (hVG : ∀ s∈V, s.1∈G)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (hΩ : ∀ s∈V, (Ω.map (MvPolynomial.eval s.2)).IsHermitian)
    (hSpec : ∀ s∈V, spectrum ℝ (Ω.map (MvPolynomial.eval s.2)) ⊆ Set.Icc s.1.1 s.1.2)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (u v : Fin n → MvPolynomial (Fin p) ℝ) :
    ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ A ∧
      ∀ (I : ℝ×ℝ) t, (∃ x, (I,x)∈V ∧ ‖t-realParametersCLM p x‖ < ε) →
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial Ω La u i))‖ ≤ A) ∧
        (∀ i, ‖MvPolynomial.eval t (complexify (residualMomentPolynomial Ω Lb v i))‖ ≤ A) ∧
        (∀ m i j, ‖MvPolynomial.eval t (complexify
          (truncationPolynomialMatrix I.1 I.2 Ω (twoGramPolynomials Ω La Lb) m i j))‖ ≤ A) ∧
        (∀ m, ‖MvPolynomial.eval t (complexify (incrementPolynomial I.1 I.2 Ω La Lb u v m))‖ ≤
          (n : ℝ) ^ 2 * A ^ 3) := by
  let L : ((ℝ×ℝ)×(Fin p→ℝ)) →L[ℝ] ((ℝ×ℝ)×(Fin p→ℂ)) :=
    (ContinuousLinearMap.id ℝ (ℝ×ℝ)).prodMap (realParametersCLM p)
  have hh : ∀ i s, s ∈ L '' V →
      (kernelFamily Ω (twoGramPolynomials Ω La Lb) i s.2).IsHermitian := by
    intro i s hs
    obtain ⟨x,hx,rfl⟩ := hs
    change (kernelFamily Ω (twoGramPolynomials Ω La Lb) i (realParametersCLM p x.2)).IsHermitian
    rw [kernelFamily_real]
    exact map_ofReal_isHermitian _ (realGramFamily_isHermitian _ (hΩ x hx) La Lb i)
  have hs : ∀ i s, s ∈ L '' V →
      spectrum ℝ (kernelFamily Ω (twoGramPolynomials Ω La Lb) i s.2) ⊆ Set.Icc s.1.1 s.1.2 := by
    intro i s hs
    obtain ⟨x,hx,rfl⟩ := hs
    change spectrum ℝ (kernelFamily Ω (twoGramPolynomials Ω La Lb) i (realParametersCLM p x.2)) ⊆ _
    rw [kernelFamily_real]
    exact map_ofReal_spectrum_subset x.1.1 x.1.2 _
      (realGramFamily_isHermitian _ (hΩ x hx) La Lb i)
      (realGramFamily_spectrum _ _ _ (hΩ x hx) (hSpec x hx) La Lb hLa hLb i)
  have hg : ∀ s∈L '' V, s.1∈G := by
    rintro _ ⟨x,hx,rfl⟩
    exact hVG x hx
  obtain ⟨ε,A,hε,hε1,hA,hb⟩ := compact_uniform_bilinear_truncations G hG hGood
    (L '' V) (hV.image L) hg Ω (twoGramPolynomials Ω La Lb) hh hs
    (residualMomentPolynomial Ω La u) (residualMomentPolynomial Ω Lb v)
  refine ⟨ε,A,hε,hε1,hA,?_⟩
  intro I t ht
  obtain ⟨x,hx,hnear⟩ := ht
  exact hb I t ⟨realParametersCLM p x, ⟨(I,x),hx,rfl⟩,hnear⟩
end RoughRegime.ProjectionIncrementComplex
