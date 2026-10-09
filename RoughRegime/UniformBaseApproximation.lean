module

public import RoughRegime.BasePolynomial
public import RoughRegime.ProjectionIncrementError


@[expose] public section
/-! Uniform base projection approximation, with the constant chosen before all
Hilbert realizations of the genuine packed moment vector. -/
noncomputable section
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MvPolynomial
namespace RoughRegime.Model
universe u
open RoughRegime.HilbertGram RoughRegime.ProjectionIncrementComplex
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ProjectionFrame
open RoughRegime.ComplexDerivativeBridge RoughRegime.KernelExpressions RoughRegime.Upper

 theorem uniform_packed_base_approximation (n : ℕ) [Nonempty (Fin n)]
    (lo hi R H : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (hH : 0 ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ m, (packedInversePolynomial n lo hi m).totalDegree ≤ m + 2) ∧
      (∀ t : Fin (designMomentDimension n) → ℂ,
        (∃ x ∈ designMomentSet n lo hi R,
          ‖t - realParametersCLM (designMomentDimension n) x‖ < 1 / C) → ∀ m,
        ‖MvPolynomial.eval t (complexify (packedInversePolynomial n lo hi m))‖ ≤ C) ∧
      (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ∀ x ∈ designMomentSet n lo hi R, ∀ (z : Fin n → E), LinearIndependent ℝ z →
        designMatrix x = Matrix.gram ℝ z → ∀ f g : E,
        designFirst x = moments z f → designSecond x = moments z g →
        ‖f‖ ≤ H → ‖g‖ ≤ H → ∀ m,
        ‖⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ -
          MvPolynomial.eval x (packedInversePolynomial n lo hi m)‖ ≤ C * intervalRho lo hi ^ m ∧
        ‖polynomialGradient (packedInversePolynomial n lo hi m) x‖ ≤ C) := by
  obtain ⟨ε, B, hε, hε1, hB, hb⟩ := uniform_packedInverse_components n lo hi R hlo hlt
  let K := incrementErrorConstant lo hi 0 0 H H
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
  refine ⟨C, hC1, packedInversePolynomial_degree n lo hi, ?_, ?_⟩
  · intro t ht m
    obtain ⟨x, hx, hnear⟩ := ht
    exact ((hb t ⟨x, hx, hnear.trans_le hrad⟩).2.2.2 m).trans hTC
  · intro E _ _ x hx z hz hGram f g hu hv hf hg m
    have hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi := by rw [← hGram]; exact hx.1
    have hta : (0 : E) ∈ basisSpan (parentBasis z (emptyParentMatrix n)) := Submodule.zero_mem _
    have hnF : ‖f - (0 : E)‖ ≤ H * (1 : ℝ) ^ (1 : ℝ) := by simpa using hf
    have hnG : ‖g - (0 : E)‖ ≤ H * (1 : ℝ) ^ (1 : ℝ) := by simpa using hg
    constructor
    · have he := incrementPolynomial_holder_error lo hi hlo hlt x (designGramPolynomial n)
        (emptyParentMatrix n) (emptyParentMatrix n) (emptyParentMatrix_orthonormal n)
        (emptyParentMatrix_orthonormal n) (designFirstPolynomial n) (designSecondPolynomial n)
        z hz hGram hSpec le_rfl f g 0 0 hta hta hu hv 1 1 1 H H
        zero_lt_one hH hH hnF hnG m
      simp only [emptyParentBasis_span, Submodule.starProjection_bot, ContinuousLinearMap.zero_apply,
        inner_zero_left, sub_zero, Real.one_rpow, Nat.add_zero, pow_zero, mul_one] at he
      exact he.trans (mul_le_mul_of_nonneg_right hKC (pow_nonneg (intervalRho_pos lo hi hlo hlt).le _))
    · have hd := incrementPolynomial_gradient_holder_bound lo hi hlo hlt x (designGramPolynomial n)
        (emptyParentMatrix n) (emptyParentMatrix n) (emptyParentMatrix_orthonormal n)
        (emptyParentMatrix_orthonormal n) (designFirstPolynomial n) (designSecondPolynomial n) m ε B hε hB
        (fun t ht => ⟨(hb t ⟨x, hx, ht⟩).1, (hb t ⟨x, hx, ht⟩).2.1,
          fun i j => (hb t ⟨x, hx, ht⟩).2.2.1 m i j⟩)
        z hz hGram hSpec f g 0 0 hta hta hu hv 1 1 1 H H zero_lt_one le_rfl
        zero_lt_one zero_lt_one hH hH hnF hnG
      simpa only [packedInversePolynomial, Real.one_rpow, mul_one] using hd.trans (by simpa using hDC)

end RoughRegime.Model
