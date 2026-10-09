module

public import RoughRegime.Model


@[expose] public section
open MeasureTheory Set

noncomputable section

namespace RoughRegime.Model

/-- A sign and additive constant preserve the absolute estimation error. -/
theorem sign_affine_error (s c x y : ℝ) (hs : |s| = 1) :
    |s * x + c - (s * y + c)| = |x - y| := by
  have he : s * x + c - (s * y + c) = s * (x - y) := by ring
  rw [he, abs_mul, hs, one_mul]

theorem sign_affine_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T S : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (s c t : ℝ) (hs : |s| = 1) (hS : ∀ P ∈ C, S P = s * T P + c) :
    minimaxTail n S C t ≤ minimaxTail n T C t := by
  unfold minimaxTail
  apply le_iInf
  intro f
  let g : Estimator Ω n := ⟨fun o => s * f.1 o + c,
    (measurable_const.mul f.2).add measurable_const⟩
  refine (iInf_le _ g).trans ?_
  apply iSup_mono
  intro P
  apply iSup_mono
  intro hP
  apply le_of_eq
  congr 1
  ext o
  simp only [Set.mem_ofPred_eq, g, hS P hP, sign_affine_error s c _ _ hs]

theorem sign_affine_rmse_le {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T S : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (s c : ℝ) (hs : |s| = 1) (hS : ∀ P ∈ C, S P = s * T P + c) :
    minimaxRMSE n S C ≤ minimaxRMSE n T C := by
  unfold minimaxRMSE
  apply le_iInf
  intro f
  let g : Estimator Ω n := ⟨fun o => s * f.1 o + c,
    (measurable_const.mul f.2).add measurable_const⟩
  refine (iInf_le _ g).trans ?_
  apply iSup_mono
  intro P
  apply iSup_mono
  intro hP
  apply le_of_eq
  apply eLpNorm_congr_norm_ae (g.2.sub measurable_const).aestronglyMeasurable
    (f.2.sub measurable_const).aestronglyMeasurable
  filter_upwards [] with o
  simp only [Real.norm_eq_abs, Pi.sub_apply, g, hS P hP, sign_affine_error s c _ _ hs]

/-- Exact invariance of both minimax risks under signs and additive constants,
including randomized estimators and infinite RMSE. -/
theorem sign_affine_risks_eq {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T S : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (s c t : ℝ) (hs : |s| = 1) (hS : ∀ P ∈ C, S P = s * T P + c) :
    minimaxTail n S C t = minimaxTail n T C t ∧
      minimaxRMSE n S C = minimaxRMSE n T C := by
  have hs2 : s * s = 1 := by nlinarith [sq_abs s]
  have hT : ∀ P ∈ C, T P = s * S P + (-s * c) := by
    intro P hP
    rw [hS P hP]
    calc
      T P = (s * s) * T P := by rw [hs2, one_mul]
      _ = s * (s * T P + c) + (-s * c) := by ring
  exact ⟨le_antisymm (sign_affine_tail_le n T S C s c t hs hS)
      (sign_affine_tail_le n S T C s (-s * c) t hs hT),
    le_antisymm (sign_affine_rmse_le n T S C s c hs hS)
      (sign_affine_rmse_le n S T C s (-s * c) hs hT)⟩

end RoughRegime.Model
