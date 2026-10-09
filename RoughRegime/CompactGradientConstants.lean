module

public import RoughRegime.PointwiseProjectionGradient


@[expose] public section
noncomputable section
namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.BilinearDerivative
lemma incrementGradientConstant_mono_hi (hi0 hi1 : ℝ) (h0 : 0≤hi0) (hle : hi0≤hi1)
    (p n a b : ℕ) (Ha Hb ε B : ℝ) (hHa : 0≤Ha) (hHb : 0≤Hb)
    (hε : 0<ε) (hB : 0≤B) :
    incrementGradientConstant hi0 p n a b Ha Hb ε B ≤
      incrementGradientConstant hi1 p n a b Ha Hb ε B := by
  have h1 : 0≤hi1 := h0.trans hle
  have hc : 0≤Real.sqrt p * derivativeConstant n B ε := by
    unfold derivativeConstant
    positivity
  unfold incrementGradientConstant
  apply mul_le_mul_of_nonneg_left _ hc
  gcongr
end RoughRegime.ProjectionIncrementComplex
