module

public import RoughRegime.CombinedAnalytic
public import RoughRegime.ProjectionFrame


@[expose] public section
/-! The actual projected inner-product increment and its concrete truncated Gram
approximation, with small factors derived from Hilbert parent approximation. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix RealInnerProductSpace
namespace RoughRegime.ProjectionError
open RoughRegime.ProjectionGram RoughRegime.HilbertGram RoughRegime.ProjectionFrame
open RoughRegime.CombinedAnalytic RoughRegime.MatrixUpper RoughRegime.Upper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def twoDims (a b : ℕ) : Fin 2 → ℕ := Fin.cases a (fun _ => b)

def twoGrams {n a b : ℕ} (Ω : Matrix (Fin n) (Fin n) ℝ)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ) :
    (i : Fin 2) → Matrix (Fin (twoDims a b i)) (Fin (twoDims a b i)) ℝ :=
  Fin.cases (ProjectionGram.gram Ω La) (fun _ => ProjectionGram.gram Ω Lb)

@[simp] lemma twoDims_sum (a b : ℕ) : (∑ i, twoDims a b i) = a + b := by
  simp only [Fin.sum_univ_two, twoDims, Fin.cases_zero]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide, Fin.cases_succ]

@[simp] lemma twoGrams_det_product {n a b : ℕ} (Ω : Matrix (Fin n) (Fin n) ℝ)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ) :
    (∏ i, (twoGrams Ω La Lb i).det) =
      (ProjectionGram.gram Ω La).det * (ProjectionGram.gram Ω Lb).det := by
  simp only [Fin.prod_univ_two, twoGrams, Fin.cases_zero]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide, Fin.cases_succ]
  rfl

def incrementApproximation {n a b : ℕ} (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) ℝ)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (u v : Fin n → ℝ) (m : ℕ) : ℝ :=
  (polynomialResidual Ω La).mulVec u ⬝ᵥ
    (truncationMatrix lo hi Ω (twoGrams Ω La Lb) m).mulVec
      ((polynomialResidual Ω Lb).mulVec v)

/-- Hilbert projection error contracts the actual resolvent/determinant
approximation by the two genuine small residual moment vectors. -/
theorem hilbert_increment_error {n a b : ℕ} (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (z : Fin n → E) (hz : LinearIndependent ℝ z)
    (hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (hsub : basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb))
    (f g ta tb : E) (hta : ta ∈ basisSpan (parentBasis z La))
    (htb : tb ∈ basisSpan (parentBasis z Lb))
    (S : Matrix (Fin n) (Fin n) ℝ) (C : ℝ)
    (herror : ‖(((ProjectionGram.gram (Matrix.gram ℝ z) La).det *
      (ProjectionGram.gram (Matrix.gram ℝ z) Lb).det)⁻¹ • (Matrix.gram ℝ z)⁻¹) - S‖ ≤ C) :
    ‖(⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ -
      ⟪(basisSpan (parentBasis z Lb)).starProjection f,
        (basisSpan (parentBasis z Lb)).starProjection g⟫) -
        (polynomialResidual (Matrix.gram ℝ z) La).mulVec (moments z f) ⬝ᵥ
          S.mulVec ((polynomialResidual (Matrix.gram ℝ z) Lb).mulVec (moments z g))‖ ≤
      4 * hi ^ (a + b + 1) * ‖f - ta‖ * ‖g - tb‖ * C := by
  let ra := euclidean ((polynomialResidual (Matrix.gram ℝ z) La).mulVec (moments z f))
  let rb := euclidean ((polynomialResidual (Matrix.gram ℝ z) Lb).mulVec (moments z g))
  let T := ((ProjectionGram.gram (Matrix.gram ℝ z) La).det *
    (ProjectionGram.gram (Matrix.gram ℝ z) Lb).det)⁻¹ • (Matrix.gram ℝ z)⁻¹
  have hhi : 0 ≤ hi := (hlo.trans hlt).le
  have hC : 0 ≤ C := (norm_nonneg (T - S)).trans herror
  have hra : ‖ra‖ ≤ 2 * hi ^ a * Real.sqrt hi * ‖f - ta‖ := by
    simpa [ra] using polynomialResidual_moment_norm_le_of_spectrum lo hi hlo hlt
      z hz hSpec La hLa f ta hta
  have hrb : ‖rb‖ ≤ 2 * hi ^ b * Real.sqrt hi * ‖g - tb‖ := by
    simpa [rb] using polynomialResidual_moment_norm_le_of_spectrum lo hi hlo hlt
      z hz hSpec Lb hLb g tb htb
  rw [hilbert_increment_residual_factors z hz La Lb hLa hLb hsub f g,
    ← dotProduct_sub, ← Matrix.sub_mulVec]
  change ‖(ra : Fin n → ℝ) ⬝ᵥ (T - S).mulVec (rb : Fin n → ℝ)‖ ≤ _
  calc
    _ ≤ ‖ra‖ * ‖T - S‖ * ‖rb‖ := dotProduct_mulVec_norm_le (T - S) ra rb
    _ ≤ (2 * hi ^ a * Real.sqrt hi * ‖f - ta‖) * C *
        (2 * hi ^ b * Real.sqrt hi * ‖g - tb‖) := by gcongr
    _ = 4 * hi ^ a * hi ^ b * (Real.sqrt hi) ^ 2 * ‖f - ta‖ * ‖g - tb‖ * C := by ring
    _ = _ := by rw [Real.sq_sqrt hhi, pow_succ, pow_add]; ring

/-- The explicit scalar bound inherited from the actual combined-index Gram
truncation in source Lemma 5(a). -/
def incrementTailBound (lo hi : ℝ) (a b m : ℕ) : ℝ :=
  2 ^ (a + b + 1) * (intervalGeometricMean lo hi ^ (a + b + 1))⁻¹ *
    ((m + 1 : ℕ) : ℝ) ^ (a + b) * intervalRho lo hi ^ m *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (a + b) * intervalRho lo hi ^ k

/-- Source Lemma 6's concrete approximation inequality, for the genuine Hilbert
projection increment; no inverse approximation or small residual estimate is
supplied as a hypothesis. -/
theorem incrementApproximation_error {n a b : ℕ} [Nonempty (Fin n)]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (z : Fin n → E) (hz : LinearIndependent ℝ z)
    (hSpec : spectrum ℝ (Matrix.gram ℝ z) ⊆ Set.Icc lo hi)
    (La : Matrix (Fin n) (Fin a) ℝ) (Lb : Matrix (Fin n) (Fin b) ℝ)
    (hLa : Laᵀ * La = 1) (hLb : Lbᵀ * Lb = 1)
    (hsub : basisSpan (parentBasis z La) ≤ basisSpan (parentBasis z Lb))
    (f g ta tb : E) (hta : ta ∈ basisSpan (parentBasis z La))
    (htb : tb ∈ basisSpan (parentBasis z Lb)) (m : ℕ) :
    ‖(⟪(basisSpan z).starProjection f, (basisSpan z).starProjection g⟫ -
      ⟪(basisSpan (parentBasis z Lb)).starProjection f,
        (basisSpan (parentBasis z Lb)).starProjection g⟫) -
      incrementApproximation lo hi (Matrix.gram ℝ z) La Lb (moments z f) (moments z g) m‖ ≤
      4 * hi ^ (a + b + 1) * ‖f - ta‖ * ‖g - tb‖ * incrementTailBound lo hi a b m := by
  have hΩ := Matrix.posDef_gram_of_linearIndependent hz
  have hM : ∀ i, (twoGrams (Matrix.gram ℝ z) La Lb i).IsHermitian := by
    intro i
    fin_cases i
    · exact (gram_posDef _ hΩ La hLa).isHermitian
    · exact (gram_posDef _ hΩ Lb hLb).isHermitian
  have hs : ∀ i, spectrum ℝ (twoGrams (Matrix.gram ℝ z) La Lb i) ⊆ Set.Icc lo hi := by
    intro i
    fin_cases i
    · exact gram_spectrum_subset lo hi _ hΩ.isHermitian hSpec La hLa
    · exact gram_spectrum_subset lo hi _ hΩ.isHermitian hSpec Lb hLb
  have herr := matrix_determinant_truncation_error lo hi hlo hlt _ hΩ.isHermitian hSpec
    (twoGrams (Matrix.gram ℝ z) La Lb) hM hs m
  simp only [twoGrams_det_product, twoDims_sum] at herr
  exact hilbert_increment_error lo hi hlo hlt z hz hSpec La Lb hLa hLb hsub
    f g ta tb hta htb _ (incrementTailBound lo hi a b m) herr

end RoughRegime.ProjectionError
