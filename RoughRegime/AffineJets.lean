module

public import RoughRegime.SourceProfileHolder


@[expose] public section
/-! True Frechet jets under the source affine block rescaling. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 def scaleCoords (origin : E) (ell : ℝ) (x : E) : E := ell⁻¹ • (x-origin)

 theorem scaleCoords_smooth (origin : E) (ell : ℝ) : ContDiff ℝ ∞ (scaleCoords origin ell) :=
   (contDiff_id.sub contDiff_const).const_smul _

 theorem norm_iteratedFDeriv_rescale (f : E → F) (hf : ContDiff ℝ ∞ f)
     (origin : E) (ell : ℝ) (hell : 0<ell) (q : ℕ) (x : E) :
     ‖iteratedFDeriv ℝ q (f ∘ scaleCoords origin ell) x‖ ≤
       ‖iteratedFDeriv ℝ q f (scaleCoords origin ell x)‖*ell⁻¹^q := by
   let L : E →L[ℝ] E := ell⁻¹ • ContinuousLinearMap.id ℝ E
   have hL : ‖L‖≤ell⁻¹ := by
     simp only [L,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hell)]
     exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ E‖≤1)
       (inv_nonneg.mpr hell.le)).trans_eq (by ring)
   change ‖iteratedFDeriv ℝ q (fun y => (f ∘ L) (y-origin)) x‖ ≤ _
   rw [iteratedFDeriv_comp_sub,L.iteratedFDeriv_comp_right hf (x-origin) (by simp)]
   calc
     _ ≤ ‖iteratedFDeriv ℝ q f (L (x-origin))‖*∏ _i : Fin q, ‖L‖ :=
       ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
     _ = ‖iteratedFDeriv ℝ q f (L (x-origin))‖*‖L‖^q := by simp
     _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL q) (norm_nonneg _)

end RoughRegime.Calculus
