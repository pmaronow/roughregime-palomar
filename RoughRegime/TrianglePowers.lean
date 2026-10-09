module

public import RoughRegime.BoxConvolution


@[expose] public section
namespace RoughRegime.LatticeFourier

open MeasureTheory Set
open scoped Convolution Pointwise

/-- n+1 convolution factors of the normalized triangular density. -/
noncomputable def trianglePower (a : ℝ) : ℕ → ℝ → ℂ
  | 0 => triangleKernel a
  | n + 1 => MeasureTheory.convolution (triangleKernel a) (trianglePower a n)
      (ContinuousLinearMap.mul ℂ ℂ) volume

@[simp] theorem trianglePower_zero (a : ℝ) : trianglePower a 0 = triangleKernel a := rfl

@[simp] theorem trianglePower_succ (a : ℝ) (n : ℕ) : trianglePower a (n + 1) =
    MeasureTheory.convolution (triangleKernel a) (trianglePower a n)
      (ContinuousLinearMap.mul ℂ ℂ) volume := rfl

private theorem trianglePower_regular (a : ℝ) (n : ℕ) :
    Continuous (trianglePower a n) ∧ HasCompactSupport (trianglePower a n) := by
  induction n with
  | zero => exact ⟨triangleKernel_continuous a, triangleKernel_hasCompactSupport a⟩
  | succ n ih =>
    constructor
    · exact ih.2.continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
        (triangleKernel_integrable a).locallyIntegrable ih.1
    · exact (triangleKernel_hasCompactSupport a).convolution
        (ContinuousLinearMap.mul ℂ ℂ) ih.2

theorem trianglePower_continuous (a : ℝ) (n : ℕ) : Continuous (trianglePower a n) :=
  (trianglePower_regular a n).1

theorem trianglePower_hasCompactSupport (a : ℝ) (n : ℕ) :
    HasCompactSupport (trianglePower a n) := (trianglePower_regular a n).2

theorem trianglePower_integrable (a : ℝ) (n : ℕ) : Integrable (trianglePower a n) :=
  (trianglePower_continuous a n).integrable_of_hasCompactSupport
    (trianglePower_hasCompactSupport a n)

/-- Each convolution adds precisely the support interval of one triangular factor. -/
theorem trianglePower_support_subset (a : ℝ) (n : ℕ) :
    Function.support (trianglePower a n) ⊆ Icc (-2 * a * (n + 1)) (2 * a * (n + 1)) := by
  induction n with
  | zero => simpa using triangleKernel_support_subset a
  | succ n ih =>
    intro x hx
    have hs := MeasureTheory.support_convolution_subset
      (f := triangleKernel a) (g := trianglePower a n)
      (μ := volume) (ContinuousLinearMap.mul ℂ ℂ) hx
    rcases hs with ⟨y, hy, z, hz, rfl⟩
    have hy' := triangleKernel_support_subset a hy
    have hz' := ih hz
    simp only [mem_Icc] at hy' hz' ⊢
    push_cast
    constructor <;> nlinarith [hy'.1, hy'.2, hz'.1, hz'.2]

end RoughRegime.LatticeFourier
