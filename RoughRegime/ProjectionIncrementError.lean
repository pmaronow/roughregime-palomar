module

public import RoughRegime.ProjectionIncrementHolder


@[expose] public section
/-! The true approximation error of the same concrete increment polynomial,
with the literal source rate and an `m`-independent constant. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MvPolynomial
namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.ProjectionIncrementPolynomial RoughRegime.ProjectionError
open RoughRegime.ProjectionGram RoughRegime.HilbertGram RoughRegime.Upper

 def incrementTailConstant (lo hi : ℝ) (a b : ℕ) : ℝ :=
  2 ^ (a + b + 1) * (intervalGeometricMean lo hi ^ (a + b + 1))⁻¹ *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (a + b) * intervalRho lo hi ^ k

lemma incrementTailBound_eq (lo hi : ℝ) (a b m : ℕ) :
    incrementTailBound lo hi a b m = incrementTailConstant lo hi a b *
      ((m + 1 : ℕ) : ℝ) ^ (a + b) * intervalRho lo hi ^ m := by
  unfold incrementTailBound incrementTailConstant
  ring

lemma incrementTailConstant_nonneg (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (a b : ℕ) :
    0 ≤ incrementTailConstant lo hi a b := by
  have hρ := (intervalRho_pos lo hi hlo hlt).le
  unfold incrementTailConstant intervalGeometricMean
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (fun k => mul_nonneg (by positivity) (pow_nonneg hρ _))

lemma incrementTailBound_nonneg (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (a b m : ℕ) :
    0 ≤ incrementTailBound lo hi a b m := by
  rw [incrementTailBound_eq]
  exact mul_nonneg (mul_nonneg (incrementTailConstant_nonneg lo hi hlo hlt a b)
    (by positivity)) (pow_nonneg (intervalRho_pos lo hi hlo hlt).le _)

 def incrementErrorConstant (lo hi : ℝ) (a b : ℕ) (Ha Hb : ℝ) : ℝ :=
  4 * hi ^ (a + b + 1) * Ha * Hb * incrementTailConstant lo hi a b

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal source error rate for the actual polynomial approximation of the
true Hilbert projection increment, from genuine parent approximation errors. -/
theorem incrementPolynomial_holder_error {p n a b : ℕ} [Nonempty (Fin n)]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (x : Fin p → ℝ)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (z : Fin n → E) (hz : LinearIndependent ℝ z)
    (hGram : Ω.map (MvPolynomial.eval x) = Matrix.gram ℝ z)
    (hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi)
    (hsub : basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb))
    (f g ta tb : E) (hta : ta ∈ basisSpan (parentBasis z La))
    (htb : tb ∈ basisSpan (parentBasis z Lb))
    (hu : (fun i => MvPolynomial.eval x (u i)) = moments z f)
    (hv : (fun i => MvPolynomial.eval x (v i)) = moments z g)
    (h α β Ha Hb : ℝ) (hh : 0 < h) (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb)
    (hfa : ‖f - ta‖ ≤ Ha * h ^ α) (hgb : ‖g - tb‖ ≤ Hb * h ^ β) (m : ℕ) :
    ‖(⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ -
      ⟪(basisSpan (parentBasis z Lb)).starProjection f,
        (basisSpan (parentBasis z Lb)).starProjection g⟫) -
      MvPolynomial.eval x (incrementPolynomial lo hi Ω La Lb u v m)‖ ≤
      incrementErrorConstant lo hi a b Ha Hb * h ^ (α + β) *
        ((m + 1 : ℕ) : ℝ) ^ (a + b) * intervalRho lo hi ^ m := by
  have hhi : 0 < hi := hlo.trans hlt
  have hTail := incrementTailBound_nonneg lo hi hlo hlt a b m
  rw [incrementPolynomial_eval, hGram, hu, hv]
  calc
    _ ≤ 4 * hi ^ (a + b + 1) * ‖f - ta‖ * ‖g - tb‖ * incrementTailBound lo hi a b m :=
      incrementApproximation_error lo hi hlo hlt z hz hSpec La Lb hLa hLb hsub f g ta tb hta htb m
    _ ≤ 4 * hi ^ (a + b + 1) * (Ha * h ^ α) * (Hb * h ^ β) * incrementTailBound lo hi a b m := by
      gcongr
    _ = _ := by
      rw [incrementTailBound_eq, Real.rpow_add hh]
      unfold incrementErrorConstant
      ring

end RoughRegime.ProjectionIncrementComplex
