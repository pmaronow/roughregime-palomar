module

public import RoughRegime.SourceModelLattice
public import RoughRegime.CanonicalModelPrior
public import RoughRegime.SourceSelectedExtras


@[expose] public section
/-! Actual model prior controls at the literal selected source resolutions.
All small-neighborhood, target-integrability, mean and variance requirements
are discharged from the original model parameters and actual source laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ContDiff Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 theorem selectedFrame_eq_latticeSetup (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedValidity θ τ c0 n) :
     F.selectedFrame θ τ c0 n V =
       F.latticeSetup.frame
         (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)
         (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ) V.positive_grid
         F.epsilonU F.epsilonV (sourceDensityMargin n) F.epsilonU_pos.le F.epsilonV_pos.le
         V.positive_margin V.margin_le :=
   F.frame_eq_latticeSetup _ _ _ _ _ _ _ _ _ rfl

 theorem eventually_selected_profile_radius (F : SourceModelFamily A0 D O π)
     (θ τ c0 epsilon : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (he : 0<epsilon) :
     ∀ᶠ n in atTop, ∀ V : F.SelectedValidity θ τ c0 n,
       let G := F.selectedFrame θ τ c0 n V
       G.Au/G.rminus≤epsilon ∧ G.Av/G.rminus≤epsilon := by
   have hamp := F.selectedFrame_amplitude_le_envelope θ τ c0 hθ hθhalf hτ
   have heps := (selectedAmplitudeEnvelope_tendsto A0 (D+1) (Nat.succ_pos _)).eventually_lt_const
     (mul_pos he F.interval.1)
   filter_upwards [hamp,heps] with n hn hnsmall
   intro V
   dsimp only
   let G := F.selectedFrame θ τ c0 n V
   have hsum : G.Au+G.Av≤epsilon*F.rminus := (hn V).trans hnsmall.le
   have hrm : G.rminus=F.rminus := rfl
   rw [hrm]
   constructor
   · apply (div_le_iff₀ F.interval.1).mpr
     exact (le_add_of_nonneg_right G.Av_nonneg).trans hsum
   · apply (div_le_iff₀ F.interval.1).mpr
     exact (le_add_of_nonneg_left G.Au_nonneg).trans hsum

 theorem eventually_actual_prior_control (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ c0 r : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (hr : 0<r) :
     ∃ epsilon>0,∃ C≥0,∃ B≥0,
       OddTaylor.mixedDerivative F.integrand 0≠0 ∧
       (∀ u v:ℝ,|u|≤epsilon→|v|≤epsilon→|F.integrand (u,v)-F.integrand 0|≤B) ∧
       ∀ᶠ n in atTop, ∃ V : F.SelectedValidity θ τ c0 n,
         let G := F.selectedFrame θ τ c0 n V
         ∃ hsmall : (G.Au+G.Av)/G.rminus*F.scores.C≤1/4,
           (∀ z, (SpatialAffine.law F.scores (G.field z)
             (by simpa only [CanonicalFrame.field] using hsmall)).probabilityMeasure∈
               Model.localClass (A0.withDimension D) O π r) ∧
           G.Au/G.rminus≤epsilon ∧ G.Av/G.rminus≤epsilon ∧
           ∀ (nu : Measure (Fin (selectedSourceLevel A0 (D+1) θ τ n)×Fin (D+1)→ℤ)) [IsProbabilityMeasure nu],
             (∀ positive : Bool, MemLp (F.actualTarget G hsmall) 2 (globalBlockPrior nu G.M positive)) ∧
             (∀ positive : Bool, variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive)≤
               4*(F.rplus*B)^2/(selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ)) ∧
             |((∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M true)-
                (∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M false))-
                OddTaylor.mixedDerivative F.integrand 0*G.priorMeanDifference (fun x=>x.1*x.2) nu|≤
               F.volume*(C*F.rplus*(G.Au/F.rminus)*(G.Av/F.rminus)*
                 ((G.Au/F.rminus)^2+(G.Av/F.rminus)^2)) := by
   obtain ⟨epsilon,he,C,hC,B,hB,hbound,hTaylor⟩ := F.uniform_actualTarget_prior_taylor
   refine ⟨epsilon,he,C,hC,B,hB,F.integrand_mixed_nonzero,hbound,?_⟩
   have hm := F.eventually_final_selected_hard_laws hF θ τ c0 r hθ hθhalf hτ hr
   have hs := F.eventually_selected_profile_radius θ τ c0 epsilon hθ hθhalf hτ he
   filter_upwards [hm,hs] with n hn hns
   obtain ⟨hN,hm,hd,hmargin,hsmall,hclass⟩ := hn
   let V : F.SelectedValidity θ τ c0 n := ⟨hN,hm,hd,hmargin⟩
   let G := F.selectedFrame θ τ c0 n V
   have hrm : G.rminus=F.rminus := rfl
   have hrp : G.rplus=F.rplus := rfl
   have hsm : (G.Au+G.Av)/G.rminus*F.scores.C≤1/4 := hsmall
   have hrad := hns V
   have hpoint (u v:ℝ) (hu:|u|≤G.Au/G.rminus) (hv:|v|≤G.Av/G.rminus) :
       |F.integrand (u,v)-F.integrand 0|≤B := hbound u v (hu.trans hrad.1) (hv.trans hrad.2)
   refine ⟨V,hsm,fun z=>(hclass z).1,hrad.1,hrad.2,?_⟩
   intro nu _
   refine ⟨fun positive=>F.actualTarget_prior_memLp G hsm B hpoint nu positive,?_,?_⟩
   · intro positive
     have hv := F.actualTarget_prior_variance_grid G hN hsm B hB hpoint nu positive
     have hcount : ((2*selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℕ):ℝ)^(D+1)=
         (selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) := by
       simpa only [sourceGridCount,Nat.cast_mul,Nat.cast_ofNat] using
         selectedGrid_blockCount_eq θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n
     simpa only [hrp,hcount] using hv
   · have ht := hTaylor G hsm nu hrad.1 hrad.2
     have hvolume : (G.ell*(2*selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℕ))^(D+1)=F.volume := by
       change ((F.selectedFrame θ τ c0 n V).ell*
         (2*selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℕ))^(D+1)=F.volume
       rw [F.selectedFrame_eq_latticeSetup θ τ c0 n V]
       exact F.latticeSetup.frame_volume _ _ _ _ _ _ _ _ _ _ _
     simpa only [hvolume,hrm,hrp] using ht

end RoughRegime.LatticePriors.SourceModelFamily
