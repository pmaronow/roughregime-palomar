module

public import RoughRegime.CompactDesignComponents
public import RoughRegime.CompactGradientConstants
public import RoughRegime.UniformBaseApproximation


@[expose] public section
/-! Compact-endpoint inverse-energy approximation with genuine Hilbert
realizations and each endpoint's own Chebyshev decay. -/
noncomputable section
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.HilbertGram RoughRegime.ProjectionIncrementComplex
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ProjectionFrame
open RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem compact_uniform_packed_base_approximation (n : ℕ) [Nonempty (Fin n)]
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hGood : G⊆densityIntervalDomain)
    (Hmoment H : ℝ) (hHmoment : 0≤Hmoment) (hH : 0≤H) :
    ∃ C : ℝ, 1≤C ∧ ∀ (I : ℝ×ℝ) (_hI : I∈G),
      (∀ m, (packedInversePolynomial n I.1 I.2 m).totalDegree≤ m+2) ∧
      (∀ t : Fin (designMomentDimension n)→ℂ,
        (∃ x∈designMomentSet n I.1 I.2 (Hmoment*I.2),
          ‖t-realParametersCLM (designMomentDimension n) x‖<1/C)→ ∀ m,
        ‖MvPolynomial.eval t (complexify (packedInversePolynomial n I.1 I.2 m))‖≤C) ∧
      (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ∀ x∈designMomentSet n I.1 I.2 (Hmoment*I.2),∀(z : Fin n→E),LinearIndependent ℝ z→
        designMatrix x=Matrix.gram ℝ z→∀f g:E,
        designFirst x=moments z f→designSecond x=moments z g→
        ‖f‖≤H→‖g‖≤H→ ∀ m,
        ‖⟪(basisSpan z).starProjection f,(basisSpan z).starProjection g⟫-
          MvPolynomial.eval x (packedInversePolynomial n I.1 I.2 m)‖≤C*intervalRho I.1 I.2^m ∧
        ‖polynomialGradient (packedInversePolynomial n I.1 I.2 m) x‖≤C) := by
  obtain ⟨ε,B,hε,hε1,hB,hb⟩ := compact_uniform_packedInverse_components n G hG hGood Hmoment hHmoment
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩ := compact_density_endpoint_bounds G hG hGood
  obtain ⟨K,hK,hKall⟩ := compact_incrementErrorConstant_bound G hG hGood 0 0 H H hH hH
  let D := incrementGradientConstant hi (designMomentDimension n) n 0 0 H H ε B
  let T := (n : ℝ) ^ 2 * B ^ 3
  let C := max 1 (max ε⁻¹ (max T (max K D)))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hεC : ε⁻¹ ≤ C := (le_max_left ε⁻¹ _).trans (le_max_right _ _)
  have hTC : T ≤ C := (le_max_left T _).trans ((le_max_right ε⁻¹ _).trans (le_max_right _ _))
  have hKC : K ≤ C := (le_max_left K D).trans ((le_max_right T _).trans
    ((le_max_right ε⁻¹ _).trans (le_max_right _ _)))
  have hDC : D ≤ C := (le_max_right K D).trans ((le_max_right T _).trans
    ((le_max_right ε⁻¹ _).trans (le_max_right _ _)))
  have hrad : 1 / C ≤ ε := by
    apply (div_le_iff₀ hC).mpr
    calc
      1 = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
      _ ≤ ε * C := mul_le_mul_of_nonneg_left hεC hε.le
  refine ⟨C, hC1, ?_⟩
  intro I hI
  have hlo := (hGood hI).1
  have hlt := (hGood hI).2
  have hKC' := (hKall I hI).trans hKC
  have hDC' := (incrementGradientConstant_mono_hi I.2 hi (hlo.trans hlt).le
    (hbounds I hI).2 (designMomentDimension n) n 0 0 H H ε B hH hH hε hB).trans hDC
  refine ⟨packedInversePolynomial_degree n I.1 I.2, ?_, ?_⟩
  · intro t ht m
    obtain ⟨x, hx, hnear⟩ := ht
    exact ((hb I hI t ⟨x, hx, hnear.trans_le hrad⟩).2.2.2 m).trans hTC
  · intro E _ _ x hx z hz hGram f g hu hv hf hg m
    have hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc I.1 I.2 := by rw [← hGram]; exact hx.1
    have hta : (0 : E) ∈ basisSpan (parentBasis z (emptyParentMatrix n)) := Submodule.zero_mem _
    have hnF : ‖f - (0 : E)‖ ≤ H * (1 : ℝ) ^ (1 : ℝ) := by simpa using hf
    have hnG : ‖g - (0 : E)‖ ≤ H * (1 : ℝ) ^ (1 : ℝ) := by simpa using hg
    constructor
    · have he := incrementPolynomial_holder_error I.1 I.2 hlo hlt x (designGramPolynomial n)
        (emptyParentMatrix n) (emptyParentMatrix n) (emptyParentMatrix_orthonormal n)
        (emptyParentMatrix_orthonormal n) (designFirstPolynomial n) (designSecondPolynomial n)
        z hz hGram hSpec le_rfl f g 0 0 hta hta hu hv 1 1 1 H H
        zero_lt_one hH hH hnF hnG m
      simp only [emptyParentBasis_span, Submodule.starProjection_bot, _root_.zero_apply,
        inner_zero_left, sub_zero, Real.one_rpow, Nat.add_zero, pow_zero, mul_one] at he
      exact he.trans (mul_le_mul_of_nonneg_right hKC' (pow_nonneg (intervalRho_pos I.1 I.2 hlo hlt).le _))
    · have hd := incrementPolynomial_gradient_holder_bound I.1 I.2 hlo hlt x (designGramPolynomial n)
        (emptyParentMatrix n) (emptyParentMatrix n) (emptyParentMatrix_orthonormal n)
        (emptyParentMatrix_orthonormal n) (designFirstPolynomial n) (designSecondPolynomial n) m ε B hε hB
        (fun t ht => ⟨(hb I hI t ⟨x, hx, ht⟩).1, (hb I hI t ⟨x, hx, ht⟩).2.1,
          fun i j => (hb I hI t ⟨x, hx, ht⟩).2.2.1 m i j⟩)
        z hz hGram hSpec f g 0 0 hta hta hu hv 1 1 1 H H zero_lt_one le_rfl
        zero_lt_one zero_lt_one hH hH hnF hnG
      simpa only [packedInversePolynomial, Real.one_rpow, mul_one] using hd.trans (by simpa using hDC')


end RoughRegime.Model
