module

public import RoughRegime.CanonicalPoissonComparison
public import RoughRegime.CanonicalPairedMixtures
public import RoughRegime.SourceSelectedIdentities


@[expose] public section
/-! The actual original selected prior pair-data experiment satisfies the
source Poisson majorant. No Hellinger or likelihood bound is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

 theorem block_mul_canonicalPoissonMajorant (B R Lambda Au Av Cstar CG CE : ℝ)
     (M : ℕ) (hR : 0<R) (hCG : 0<CG) (hM : 0<M) :
     B*canonicalPoissonMajorant Cstar CG CE R Lambda Au Av M =
       let I := B*Lambda^2*Au^2*Av^2*R^(1-(M:ℝ))*Real.exp (CE*M)*
         (Cstar*CG*Lambda)^M/M.factorial
       Cstar*CG*I*Real.exp (CG*Cstar*Lambda*R^Real.sqrt M)+
         I*remainderRatio Cstar Lambda Au Av R CE CG M := by
   have hcast : ((M-1:ℕ):ℝ)=(M:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤M)]; norm_num
   have hRinv : R^(1-(M:ℝ))=(R^(M-1))⁻¹ := by
     rw [←Real.rpow_natCast]
     rw [hcast,show 1-(M:ℝ) = -((M:ℝ)-1) by ring,Real.rpow_neg hR.le]
   dsimp only
   unfold canonicalPoissonMajorant remainderRatio
   rw [hRinv]
   simp only [neg_mul,Real.exp_neg,mul_pow]
   field_simp

namespace SourceModelFamily
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

structure SelectedPoissonValidity (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) : Prop where
  validity : F.SelectedValidity θ τ c0 n
  positive_frequency : 0<frequency n θ τ
  band_budget : sourceFineScale (selectedSourceLevel A0 (D+1) θ τ n) (min A0.α A0.β)≤
    sourceBandConstant (D+1) A0.α A0.β*frequency n θ τ
  small : ((F.selectedFrame θ τ c0 n validity).Au+(F.selectedFrame θ τ c0 n validity).Av)/F.rminus*F.scores.C≤1/4

 def sourceObservationRate (n : ℕ) : ℝ≥0 := ⟨2*(n:ℝ),by positivity⟩

 def selectedPairedMixture (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ)
     (V : F.SelectedPoissonValidity θ τ c0 n) (positive : Bool) :=
   let G := F.selectedFrame θ τ c0 n V.validity
   G.canonicalPairedMixture
     (F.latticeSetup.coefficientPrior (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ)
       V.positive_frequency V.band_budget) π F.scores V.small
     (G.pairPoissonRate (sourceObservationRate n)) positive

 def selectedPairedHellinger (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) : ℝ := by
   classical
   exact if h : Nonempty (F.SelectedPoissonValidity θ τ c0 n) then
     GeneralTesting.hellingerSquared
       (F.selectedPairedMixture θ τ c0 n (Classical.choice h) true)
       (F.selectedPairedMixture θ τ c0 n (Classical.choice h) false)
   else 0

 theorem selectedPairedHellinger_eq (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ)
     (V : F.SelectedPoissonValidity θ τ c0 n) :
     F.selectedPairedHellinger θ τ c0 n=GeneralTesting.hellingerSquared
       (F.selectedPairedMixture θ τ c0 n V true) (F.selectedPairedMixture θ τ c0 n V false) := by
   simp only [selectedPairedHellinger,dite_eq_left (show Nonempty (F.SelectedPoissonValidity θ τ c0 n) from ⟨V⟩)]

 theorem selectedPoissonValidity_eventually (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ c0 : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) :
     ∀ᶠ n : ℕ in atTop, Nonempty (F.SelectedPoissonValidity θ τ c0 n) := by
   have hf := tendsto_natCast_atTop_atTop.eventually
     ((frequency_tendsto θ τ hθ hθhalf hτ).eventually_ge_atTop 1)
   have hb := tendsto_natCast_atTop_atTop.eventually
     (selectedSourceMultiplier_frequency_budget A0 (D+1) (Nat.succ_pos _) θ τ hθ hθhalf hτ)
   filter_upwards [F.eventually_final_selected_hard_laws hF θ τ c0 1 hθ hθhalf hτ (by norm_num),hf,hb]
     with n hn hnf hnb
   obtain ⟨hN,hm,hd,hmargin,hsmall,_⟩ := hn
   have hM : 0<frequency n θ τ := by
     have hp : (0:ℝ)<(frequency n θ τ:ℝ) := lt_of_lt_of_le (by norm_num) hnf
     exact_mod_cast hp
   exact ⟨⟨⟨hN,hm,hd,hmargin⟩,hM,hnb,hsmall⟩⟩

 theorem selectedSourceLambda_tendsto_zero (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) :
     Tendsto (fun n : ℕ => selectedSourceLambda A0 (D+1) θ τ c0 F.volume n) atTop (𝓝 0) := by
   have hB := blockInflation_div_logPower_tendsto θ τ c0 0 hθ hθhalf hτ
     (selectedSourceVolume A0 (D+1) θ τ)
     (Eventually.of_forall (selectedSourceVolume_ge_one A0 (D+1) θ τ))
     (selectedSourceVolume_log_isBigO A0 (D+1) (Nat.succ_pos _) θ τ hθ hθhalf hτ)
     (D+1) (Nat.succ_pos _)
   simp only [Real.rpow_zero,div_one] at hB
   have h := (tendsto_inv_atTop_zero.comp (hB.comp tendsto_natCast_atTop_atTop)).const_mul (2*F.volume)
   simpa only [Function.comp_apply,mul_zero,div_eq_mul_inv,selectedSourceLambda] using h

 theorem selectedFrame_pair_rate_le (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedPoissonValidity θ τ c0 n) (hn : 0<(n:ℝ)) :
     0 ≤ selectedSourceLambda A0 (D+1) θ τ c0 F.volume n ∧
     ((F.selectedFrame θ τ c0 n V.validity).pairPoissonRate (sourceObservationRate n):ℝ)≤
       2*F.rplus*selectedSourceLambda A0 (D+1) θ τ c0 F.volume n := by
   let G := F.selectedFrame θ τ c0 n V.validity
   have hΛ : 0 ≤ selectedSourceLambda A0 (D+1) θ τ c0 F.volume n := by
     unfold selectedSourceLambda blockInflation
     exact div_nonneg (mul_nonneg (by norm_num) F.volume_pos.le)
       (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
   refine ⟨hΛ,?_⟩
   change 2*(n:ℝ)*G.pairMass≤_
   rw [F.selectedFrame_pair_poisson_mean θ τ c0 n V.validity hn]
   exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left G.pairBarDensity_bounds.2 (by norm_num)) hΛ

 def SelectedPairBound (F : SourceModelFamily A0 D O π) (Cstar CG CE : ℝ) : Prop :=
   ∀ (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedPoissonValidity θ τ c0 n),
     0<(n:ℝ) → A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ →
     ((F.selectedFrame θ τ c0 n V.validity).pairPoissonRate (sourceObservationRate n):ℝ)≤1 →
     GeneralTesting.hellingerSquared
       (F.selectedPairedMixture θ τ c0 n V true) (F.selectedPairedMixture θ τ c0 n V false) ≤
       selectedSourcePoissonMajorant A0 (D+1) θ τ c0 F.volume F.epsilonU F.epsilonV CE Cstar CG n

 /-- Fixed comparison constants precede every resolution and margin. -/
 theorem uniform_selected_pair_bound (F : SourceModelFamily A0 D O π) :
     ∃ C CG CE Cstar : ℝ, SourceLatticeConclusions F.latticeSetup C CG CE ∧
       1≤Cstar ∧ F.SelectedPairBound Cstar CG CE := by
   obtain ⟨C,CG,CE,H⟩ := source_lattice_priors F.latticeSetup
   obtain ⟨Cstar,hCstar,hcomp⟩ := F.latticeSetup.uniform_canonical_pair_comparison C CG CE H π F.scores
   refine ⟨C,CG,CE,Cstar,H,hCstar,?_⟩
   intro θ τ c0 n V hn hab hrate
   let G := F.selectedFrame θ τ c0 n V.validity
   let ν := F.latticeSetup.coefficientPrior (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ)
     V.positive_frequency V.band_budget
   let Λ := selectedSourceLambda A0 (D+1) θ τ c0 F.volume n
   have hr := F.selectedFrame_pair_rate_le θ τ c0 n V hn
   have hp := hcomp _ (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ)
     V.validity.positive_grid F.epsilonU F.epsilonV (sourceDensityMargin n)
     F.epsilonU_pos.le F.epsilonV_pos.le V.validity.positive_margin V.validity.margin_le
     V.positive_frequency V.band_budget F.epsilonU_le F.epsilonV_le V.small
     (G.pairPoissonRate (sourceObservationRate n)) Λ hr.1 hrate hr.2
   have hp' : GeneralTesting.hellingerSquared
       (G.canonicalPairMixture ν π F.scores V.small (G.pairPoissonRate (sourceObservationRate n)) true)
       (G.canonicalPairMixture ν π F.scores V.small (G.pairPoissonRate (sourceObservationRate n)) false) ≤
       canonicalPoissonMajorant Cstar CG CE (selectedSourceVolume A0 (D+1) θ τ n) Λ G.Au G.Av
         (frequency n θ τ) := by
     simpa only [G,selectedFrame,SourceModelFamily.frame,SourceLatticeSetup.frame,latticeSetup,
       ν,selectedSourceMultiplier,selectedFineScale,largestFineScale,sourceFineScale,
       selectedSourceVolume,selectedFineVolume,largestFineVolume,selectedSourceLevel,
       selectedFineLevel,Nat.mul_comm] using hp
   have ht := G.canonicalPairedMixture_hellinger_le ν π F.scores V.small
     (G.pairPoissonRate (sourceObservationRate n))
   have hcard : (Fintype.card (GridPair D (selectedGridPairs θ τ c0
       (selectedSourceVolume A0 (D+1) θ τ) (D+1) n)):ℝ)≤
       (selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) := by
     rw [←selectedGrid_blockCount_eq,gridPair_card]
     unfold sourceGridCount
     push_cast
     rw [pow_succ]
     nlinarith [pow_nonneg (by positivity : 0≤(2:ℝ)*
       selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) D]
   have hmajor : 0≤canonicalPoissonMajorant Cstar CG CE (selectedSourceVolume A0 (D+1) θ τ n)
       Λ G.Au G.Av (frequency n θ τ) := by
     have hstar : 0≤Cstar := zero_le_one.trans hCstar
     have hcg : 0≤CG := zero_le_one.trans H.gamma_constant_ge_one
     have hΛ : 0≤Λ := hr.1
     have hR : 0 ≤ selectedSourceVolume A0 (D+1) θ τ n :=
       zero_le_one.trans (selectedSourceVolume_ge_one A0 (D+1) θ τ n)
     unfold canonicalPoissonMajorant
     positivity
   have hprod := (ht.trans (mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg _))).trans
     (mul_le_mul_of_nonneg_right hcard hmajor)
   change GeneralTesting.hellingerSquared (F.selectedPairedMixture θ τ c0 n V true)
       (F.selectedPairedMixture θ τ c0 n V false) ≤ _ at hprod
   apply hprod.trans_eq
   rw [block_mul_canonicalPoissonMajorant _ _ _ _ _ _ _ _ _
     (zero_lt_one.trans_le (selectedSourceVolume_ge_one A0 (D+1) θ τ n))
     (zero_lt_one.trans_le H.gamma_constant_ge_one) V.positive_frequency]
   dsimp only
   rw [show G.Au=selectedSourceAmplitude A0 (D+1) θ τ c0 F.epsilonU A0.α n from
     F.selectedFrame_Au θ τ c0 n V.validity,
     show G.Av=selectedSourceAmplitude A0 (D+1) θ τ c0 F.epsilonV A0.β n from
     F.selectedFrame_Av θ τ c0 n V.validity,
     ←selectedSourceRawI_eq_physical A0 (D+1) θ τ c0 F.volume F.epsilonU F.epsilonV CE Cstar CG n hn hab]
   rfl

 theorem selectedFrame_pair_rate_eventually_le_one (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) :
     ∀ᶠ n : ℕ in atTop, ∀ V : F.SelectedPoissonValidity θ τ c0 n,
       ((F.selectedFrame θ τ c0 n V.validity).pairPoissonRate (sourceObservationRate n):ℝ)≤1 := by
   have he := (F.selectedSourceLambda_tendsto_zero θ τ c0 hθ hθhalf hτ).const_mul (2*F.rplus)
   simp only [mul_zero] at he
   filter_upwards [he.eventually_lt_const (by norm_num : (0:ℝ)<1),eventually_gt_atTop 0]
     with n hn hnp
   intro V
   have hn0 : 0<(n:ℝ) := by exact_mod_cast hnp
   exact (F.selectedFrame_pair_rate_le θ τ c0 n V hn0).2.trans hn.le

 theorem selectedPairedHellinger_nonneg (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) :
     0 ≤ F.selectedPairedHellinger θ τ c0 n := by
   classical
   unfold selectedPairedHellinger
   split_ifs
   · unfold GeneralTesting.hellingerSquared
     exact integral_nonneg (fun _=>sq_nonneg _)
   · exact le_refl _

 theorem SelectedPairBound.eventually_bound {F : SourceModelFamily A0 D O π} {Cstar CG CE : ℝ}
     (HB : F.SelectedPairBound Cstar CG CE) (hF : F.Localized) (θ τ c0 : ℝ)
     (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ) :
     ∀ᶠ n : ℕ in atTop,
       F.selectedPairedHellinger θ τ c0 n≤
         selectedSourcePoissonMajorant A0 (D+1) θ τ c0 F.volume F.epsilonU F.epsilonV CE Cstar CG n := by
   classical
   filter_upwards [F.selectedPoissonValidity_eventually hF θ τ c0 hθ hθhalf hτ,
     F.selectedFrame_pair_rate_eventually_le_one θ τ c0 hθ hθhalf hτ,eventually_gt_atTop 0]
     with n hn hr hn0
   let V := Classical.choice hn
   rw [F.selectedPairedHellinger_eq θ τ c0 n V]
   exact HB θ τ c0 n V (by exact_mod_cast hn0) hab (hr V)

 theorem SelectedPairBound.tendsto_zero {F : SourceModelFamily A0 D O π} {Cstar CG CE : ℝ}
     (HB : F.SelectedPairBound Cstar CG CE) (hF : F.Localized)
     (hCstar : 1≤Cstar) (hCG : 1≤CG) (hCE : 0≤CE) (θ τ c0 : ℝ)
     (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ)
     (hmargin : 1+Real.log (2*F.volume*Cstar*CG)+CE<c0) :
     Tendsto (F.selectedPairedHellinger θ τ c0) atTop (𝓝 0) := by
   have hmajor := (selectedSourcePoissonMajorant_tendsto_zero A0 (D+1) (Nat.succ_pos _)
     θ τ c0 F.volume F.epsilonU F.epsilonV CE Cstar CG hθ hθhalf hτ F.volume_pos
     F.epsilonU_pos F.epsilonU_le F.epsilonV_pos F.epsilonV_le hCE hCstar hCG hmargin).comp
       tendsto_natCast_atTop_atTop
   exact squeeze_zero' (Eventually.of_forall (F.selectedPairedHellinger_nonneg θ τ c0))
     (HB.eventually_bound hF θ τ c0 hθ hθhalf hτ hab) hmajor

 /-- Actual original selected independent-prior Poisson experiment: the
 Hellinger square tends to zero and is eventually at most 1/128. -/
 theorem selected_poisson_comparison (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ)
     (hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ) :
     ∃ C CG CE Cstar : ℝ, SourceLatticeConclusions F.latticeSetup C CG CE ∧ 1≤Cstar ∧
       ∀ c0 : ℝ, 1+Real.log (2*F.volume*Cstar*CG)+CE<c0 →
         Tendsto (F.selectedPairedHellinger θ τ c0) atTop (𝓝 0) ∧
         (∀ᶠ n : ℕ in atTop, F.selectedPairedHellinger θ τ c0 n≤
           selectedSourcePoissonMajorant A0 (D+1) θ τ c0 F.volume F.epsilonU F.epsilonV CE Cstar CG n) ∧
         (∀ᶠ n : ℕ in atTop, ∃ V : F.SelectedPoissonValidity θ τ c0 n,
           GeneralTesting.hellingerSquared (F.selectedPairedMixture θ τ c0 n V true)
             (F.selectedPairedMixture θ τ c0 n V false)≤1/128) := by
   classical
   obtain ⟨C,CG,CE,Cstar,H,hstar,HB⟩ := F.uniform_selected_pair_bound
   refine ⟨C,CG,CE,Cstar,H,hstar,?_⟩
   intro c0 hmargin
   have hl := HB.tendsto_zero hF hstar H.gamma_constant_ge_one H.entropy_constant_nonneg θ τ c0
     hθ hθhalf hτ hab hmargin
   refine ⟨hl,HB.eventually_bound hF θ τ c0 hθ hθhalf hτ hab,?_⟩
   filter_upwards [F.selectedPoissonValidity_eventually hF θ τ c0 hθ hθhalf hτ,
     hl.eventually_lt_const (by norm_num : (0:ℝ)<1/128)] with n hn hh
   let V := Classical.choice hn
   refine ⟨V,?_⟩
   rw [←F.selectedPairedHellinger_eq θ τ c0 n V]
   exact hh.le

 theorem exists_selected_poisson_small (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (θ τ : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ)
     (hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ) :
     ∃ c0 : ℝ, Tendsto (F.selectedPairedHellinger θ τ c0) atTop (𝓝 0) ∧
       (∀ᶠ n : ℕ in atTop, Nonempty (F.SelectedPoissonValidity θ τ c0 n) ∧
         F.selectedPairedHellinger θ τ c0 n≤1/128) := by
   obtain ⟨C,CG,CE,Cstar,_,_,hc⟩ := F.selected_poisson_comparison hF θ τ hθ hθhalf hτ hab
   let c0 := 2+Real.log (2*F.volume*Cstar*CG)+CE
   have hh : 1+Real.log (2*F.volume*Cstar*CG)+CE<c0 := by dsimp [c0]; linarith
   have hl := (hc c0 hh).1
   refine ⟨c0,hl,?_⟩
   filter_upwards [F.selectedPoissonValidity_eventually hF θ τ c0 hθ hθhalf hτ,
     hl.eventually_lt_const (by norm_num : (0:ℝ)<1/128)] with n hv hn
   exact ⟨hv,hn.le⟩

end SourceModelFamily
end RoughRegime.LatticePriors
