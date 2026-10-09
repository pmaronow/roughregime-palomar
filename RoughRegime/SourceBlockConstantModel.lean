module

public import RoughRegime.SourceSelectedModel
public import RoughRegime.SourceModelLattice
public import RoughRegime.CanonicalPairMarks


@[expose] public section
/-! The literal J=0, m=R=1 canonical source construction. It has no fine
spatial resolution and its genuine actual laws satisfy the model class. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 def blockConstantGrid (_F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) : ℕ :=
   selectedGridPairs θ τ c0 (fun _ => 1) (D+1) n

 theorem blockConstantGrid_evenCeiling (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) : F.blockConstantGrid θ τ c0 n=
     evenCeiling (idealSideLength n 1 (logResolution n θ τ c0) (D+1))/2 :=
   selectedGridPairs_eq_half_evenCeiling θ τ c0 (fun _ => 1) (D+1) n

 structure BlockConstantValidity (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) : Prop where
   positive_grid : 0 < F.blockConstantGrid θ τ c0 n
   positive_margin : 0 < sourceDensityMargin n
   margin_le : sourceDensityMargin n ≤ F.margin

 def blockConstantFrame (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ)
     (V : F.BlockConstantValidity θ τ c0 n) :
     CanonicalFrame D (F.blockConstantGrid θ τ c0 n) (Fin 0×Fin (D+1)) :=
   F.frame (F.blockConstantGrid θ τ c0 n) 0 (frequency n θ τ) V.positive_grid
     1 (sourceDensityMargin n) (by norm_num) V.positive_margin V.margin_le

 theorem blockConstantFrame_eq_latticeSetup (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantValidity θ τ c0 n) :
     F.blockConstantFrame θ τ c0 n V=
       F.latticeSetup.frame (F.blockConstantGrid θ τ c0 n) 0 (frequency n θ τ)
         V.positive_grid F.epsilonU F.epsilonV (sourceDensityMargin n)
         F.epsilonU_pos.le F.epsilonV_pos.le V.positive_margin V.margin_le := by
   exact F.frame_eq_latticeSetup _ _ _ _ _ _ _ _ _ (by simp [sourceFineScale])

 theorem blockConstantValidity_eventually (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) : ∀ᶠ n in atTop, Nonempty (F.BlockConstantValidity θ τ c0 n) := by
   have hm := sourceDensityMargin_tendsto.eventually (Iio_mem_nhds F.margin_pos)
   filter_upwards [hm,eventually_gt_atTop 1] with n hn hnp
   have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
   refine ⟨⟨?_,sourceDensityMargin_pos n hnp,hn.le⟩⟩
   exact selectedGridPairs_pos θ τ c0 (fun _ => 1) (D+1) n hn0 (by norm_num)

 theorem blockConstantFrame_Au (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantValidity θ τ c0 n) :
     (F.blockConstantFrame θ τ c0 n V).Au=
       amplitude F.epsilonU (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ)
         1 (A0.α/(D+1:ℕ)) 1 := by
   change sourceAmplitude F.epsilonU
     (sourceGridCount (selectedGridPairs θ τ c0 (fun _ => 1) (D+1) n) (D+1)) 0
     (D+1) A0.α 1=_
   rw [selectedGrid_blockCount_eq]
   simp only [sourceAmplitude,sourceSpatialVolume,zero_mul,pow_zero,amplitude]

 theorem blockConstantFrame_Av (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantValidity θ τ c0 n) :
     (F.blockConstantFrame θ τ c0 n V).Av=
       amplitude F.epsilonV (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ)
         1 (A0.β/(D+1:ℕ)) 1 := by
   change sourceAmplitude F.epsilonV
     (sourceGridCount (selectedGridPairs θ τ c0 (fun _ => 1) (D+1) n) (D+1)) 0
     (D+1) A0.β 1=_
   rw [selectedGrid_blockCount_eq]
   simp only [sourceAmplitude,sourceSpatialVolume,zero_mul,pow_zero,amplitude]

 theorem blockConstantFrame_volume (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantValidity θ τ c0 n) :
     ((F.blockConstantFrame θ τ c0 n V).ell*(2*F.blockConstantGrid θ τ c0 n:ℕ))^(D+1)=F.volume := by
   rw [F.blockConstantFrame_eq_latticeSetup θ τ c0 n V]
   exact F.latticeSetup.frame_volume _ _ _ _ _ _ _ _ _ _ _

 theorem blockConstantFrame_ell_pow (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantValidity θ τ c0 n) :
     (F.blockConstantFrame θ τ c0 n V).ell^(D+1)=
       F.volume/(selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ) := by
   have hB : 0 < (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ) := by
     rw [←selectedGrid_blockCount_eq]
     exact sourceGridCount_pos _ _ V.positive_grid
   apply (eq_div_iff hB.ne').mpr
   have hv := F.blockConstantFrame_volume θ τ c0 n V
   rw [mul_pow] at hv
   have hcount : ((2*F.blockConstantGrid θ τ c0 n:ℕ):ℝ)^(D+1)=
       (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ) := by
     simpa only [blockConstantGrid,sourceGridCount,Nat.cast_mul,Nat.cast_ofNat] using
       selectedGrid_blockCount_eq θ τ c0 (fun _ => 1) (D+1) n
   rwa [hcount] at hv

 theorem eventually_blockConstant_hard_laws (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ c0 r : ℝ) (hθ : 0 < θ) (hhalf : θ < 1/2) (hτ : 0 < τ) (hr : 0 < r) :
     ∀ᶠ n in atTop, ∃ V : F.BlockConstantValidity θ τ c0 n,
       let B := F.blockConstantFrame θ τ c0 n V
       ∃ hsmall : (B.Au+B.Av)/F.rminus*F.scores.C ≤ 1/4,
         ∀ z, (SpatialAffine.law F.scores (B.field z) hsmall).probabilityMeasure∈
           Model.localClass (A0.withDimension D) O π r ∧
           (∀ x, |B.u z x| ≤ (n:ℝ)^(-(A0.α/(D+1:ℕ)))/F.rminus) ∧
           (∀ x, |B.v z x| ≤ (n:ℝ)^(-(A0.β/(D+1:ℕ)))/F.rminus) := by
   have hR : (fun x:ℝ => Real.log (1:ℝ)) =O[atTop]
       (fun x => Real.log (frequency x θ τ)) := by
     apply Asymptotics.IsBigO.of_bound 0
     simp
   have hm0 : ∀ᶠ n:ℕ in atTop, (2:ℝ)^(((0:ℕ):ℝ)*sourceAlpha0 A0.α A0.β) ≤ 1 := by simp
   have hmU : ∀ᶠ n:ℕ in atTop, (1:ℝ) ≤ (2:ℝ)^(((0:ℕ):ℝ)*A0.α) := by simp
   have hmV : ∀ᶠ n:ℕ in atTop, (1:ℝ) ≤ (2:ℝ)^(((0:ℕ):ℝ)*A0.β) := by simp
   have hh := F.eventually_selected_hard_laws hF θ τ c0 r hθ hhalf hτ hr
     (fun _ => 1) (Eventually.of_forall (fun _ => le_rfl)) hR (fun _ => 0) (fun _ => 1)
     hm0 hmU hmV
   filter_upwards [hh] with n hn
   obtain ⟨hN,_,hd,hmargin,hsmall,hclass⟩ := hn
   refine ⟨⟨hN,hd,hmargin⟩,hsmall,hclass⟩

 theorem blockConstantFrame_pair_mean (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantValidity θ τ c0 n) :
     2*(n:ℝ)*(F.blockConstantFrame θ τ c0 n V).pairMass=
       2*(F.blockConstantFrame θ τ c0 n V).pairBarDensity*
         (2*F.volume*(n:ℝ)/(selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ)) := by
   unfold CanonicalFrame.pairMass
   rw [F.blockConstantFrame_ell_pow θ τ c0 n V]
   ring

end RoughRegime.LatticePriors.SourceModelFamily
