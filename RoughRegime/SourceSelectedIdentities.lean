module

public import RoughRegime.CanonicalSelectedModelPrior
public import RoughRegime.SourcePoissonBudgets


@[expose] public section
/-! Exact identities between the actual canonical statistical frame and the
source numeric amplitudes and block-volume scale. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 theorem selectedFrame_Au (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedValidity θ τ c0 n) :
     (F.selectedFrame θ τ c0 n V).Au=
       selectedSourceAmplitude A0 (D+1) θ τ c0 F.epsilonU A0.α n := by
   change sourceAmplitude F.epsilonU
     (sourceGridCount (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) (D+1))
     (selectedSourceLevel A0 (D+1) θ τ n) (D+1) A0.α (selectedSourceMultiplier A0 (D+1) θ τ n)=_
   rw [selectedGrid_blockCount_eq]
   rfl

 theorem selectedFrame_Av (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedValidity θ τ c0 n) :
     (F.selectedFrame θ τ c0 n V).Av=
       selectedSourceAmplitude A0 (D+1) θ τ c0 F.epsilonV A0.β n := by
   change sourceAmplitude F.epsilonV
     (sourceGridCount (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) (D+1))
     (selectedSourceLevel A0 (D+1) θ τ n) (D+1) A0.β (selectedSourceMultiplier A0 (D+1) θ τ n)=_
   rw [selectedGrid_blockCount_eq]
   rfl

 theorem selectedFrame_volume (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedValidity θ τ c0 n) :
     ((F.selectedFrame θ τ c0 n V).ell*
       (2*selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℕ))^(D+1)=F.volume := by
   rw [F.selectedFrame_eq_latticeSetup θ τ c0 n V]
   exact F.latticeSetup.frame_volume _ _ _ _ _ _ _ _ _ _ _


 theorem selectedFrame_ell_pow (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedValidity θ τ c0 n) :
     (F.selectedFrame θ τ c0 n V).ell^(D+1)=
       F.volume/(selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) := by
   have hB : 0 < (selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) := by
     rw [←selectedGrid_blockCount_eq]
     exact sourceGridCount_pos _ _ V.positive_grid
   apply (eq_div_iff hB.ne').mpr
   have hv := F.selectedFrame_volume θ τ c0 n V
   rw [mul_pow] at hv
   have hcount : ((2*selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℕ):ℝ)^(D+1)=
       (selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) := by
     simpa only [sourceGridCount,Nat.cast_mul,Nat.cast_ofNat] using
       selectedGrid_blockCount_eq θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n
   rwa [hcount] at hv


 theorem selectedFrame_pair_poisson_mean (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedValidity θ τ c0 n) (hn : 0<(n:ℝ)) :
     2*(n:ℝ)*(F.selectedFrame θ τ c0 n V).pairMass=
       2*(F.selectedFrame θ τ c0 n V).pairBarDensity*
         selectedSourceLambda A0 (D+1) θ τ c0 F.volume n := by
   have hB : 0 < (selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) := by
     rw [←selectedGrid_blockCount_eq]
     exact sourceGridCount_pos _ _ V.positive_grid
   unfold CanonicalFrame.pairMass
   rw [F.selectedFrame_ell_pow θ τ c0 n V]
   unfold selectedSourceLambda blockInflation
   field_simp

end RoughRegime.LatticePriors.SourceModelFamily
