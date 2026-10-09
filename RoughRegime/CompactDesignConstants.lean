module

public import RoughRegime.CompactDensityParameters
public import RoughRegime.DyadicDesign
public import RoughRegime.BaseDesign


@[expose] public section
/-! The actual known design-observable constants are common over a compact
family of density endpoints with all remaining model parameters fixed. -/
noncomputable section
open Set
namespace RoughRegime.Model

lemma compact_dyadicDesignConstant_bound (A : Parameters) (k : ℕ)
    (G : Set (ℝ×ℝ)) (hG : IsCompact G) (hdom : G⊆densityIntervalDomain) :
    ∃C:ℝ,1≤C ∧ ∀(I:ℝ×ℝ)(hI:I∈G),
      dyadicDesignConstant (densityParameters A I (hdom hI)) k≤C := by
  obtain ⟨B,hbound⟩:=hG.bddAbove_image (continuous_snd.continuousOn)
  let C:ℝ:=max 1 (max (Real.sqrt (Fintype.card (DesignMomentIndex (dyadicChildDimension A.d k)))*
    (A.M0*dyadicDesignBasisBound A.d k^2)) (B/A.δ))
  refine ⟨C,le_max_left _ _,?_⟩
  intro I hI
  apply max_le (le_max_left _ _) (max_le
    ((le_max_left _ _).trans (le_max_right _ _)) ?_)
  exact (div_le_div_of_nonneg_right (hbound ⟨I,hI,rfl⟩) A.hδ.le).trans
    ((le_max_right _ _).trans (le_max_right _ _))

@[simp] lemma baseDesignConstant_densityParameters (A : Parameters) (k : ℕ)
    (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) :
    baseDesignConstant (densityParameters A I hI) k=baseDesignConstant A k := rfl

end RoughRegime.Model
