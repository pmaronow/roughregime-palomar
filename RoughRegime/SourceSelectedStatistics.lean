module

public import RoughRegime.CanonicalSelectedModelPrior
public import RoughRegime.SourceNonlinearGap
public import RoughRegime.SourceTaylorScales
public import RoughRegime.SourceSelectedIdentities


@[expose] public section
/-! True selected source target means and prior concentration, derived from
original nondegeneracy, C4 regularity and the actual lattice scale choices. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 theorem selectedFrame_puv_separation (F : SourceModelFamily A0 D O π)
     (θ τ c0 : ℝ) (n : ℕ) (V : F.SelectedValidity θ τ c0 n)
     (hM : 0<frequency n θ τ)
     (hscale : sourceFineScale (selectedSourceLevel A0 (D+1) θ τ n) (min A0.α A0.β) ≤
       sourceBandConstant (D+1) A0.α A0.β*frequency n θ τ) :
     let G := F.selectedFrame θ τ c0 n V
     let nu := F.latticeSetup.coefficientPrior (selectedSourceLevel A0 (D+1) θ τ n)
       (frequency n θ τ) hM hscale
     F.latticeSetup.separationConstant*G.Au*G.Av*
       Upper.intervalRho (F.rminus+sourceDensityMargin n) (F.rplus-sourceDensityMargin n)^
         (frequency n θ τ) ≤ G.priorMeanDifference (fun x=>x.1*x.2) nu := by
   dsimp only
   rw [F.selectedFrame_eq_latticeSetup θ τ c0 n V]
   have ht := F.latticeSetup.target_separation _ _ _ V.positive_grid hM
     (nearestEven_even _) hscale F.epsilonU F.epsilonV (sourceDensityMargin n)
     F.epsilonU_pos.le F.epsilonV_pos.le V.positive_margin V.margin_le
   dsimp only at ht
   rw [←CanonicalFrame.responseFunctional_bilinear] at ht
   exact ht


 def gapCoefficient (F : SourceModelFamily A0 D O π) : ℝ :=
   |OddTaylor.mixedDerivative F.integrand 0| *F.latticeSetup.separationConstant/2

 theorem gapCoefficient_pos (F : SourceModelFamily A0 D O π) : 0<F.gapCoefficient :=
   div_pos (mul_pos (abs_pos.mpr F.integrand_mixed_nonzero) F.latticeSetup.separationConstant_pos)
     (by norm_num)

 def actualMeanGap (F : SourceModelFamily A0 D O π) {N : ℕ} {ι : Type*} [Fintype ι]
     (G : CanonicalFrame D N ι) (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4)
     (nu : Measure (ι→ℤ)) : ℝ :=
   |(∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M true)-
     (∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M false)|

 theorem eventually_selected_mean_gap (F : SourceModelFamily A0 D O π)
     (θ c0 : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2)
     (hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ) :
     let τ := RoughRegime.Rates.tau F.rminus F.rplus
     ∀ᶠ n in atTop, ∀ (V : F.SelectedValidity θ τ c0 n)
       (hM : 0<frequency n θ τ)
       (hscale : sourceFineScale (selectedSourceLevel A0 (D+1) θ τ n) (min A0.α A0.β) ≤
         sourceBandConstant (D+1) A0.α A0.β*frequency n θ τ),
     let G := F.selectedFrame θ τ c0 n V
     ∀ hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4,
     F.gapCoefficient*selectedSourceGapScale A0 (D+1) θ τ c0 F.epsilonU F.epsilonV F.rminus F.rplus n ≤
       F.actualMeanGap G hsmall (F.latticeSetup.coefficientPrior
         (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ) hM hscale) := by
   dsimp only
   let τ := RoughRegime.Rates.tau F.rminus F.rplus
   have hτ := RoughRegime.Rates.tau_pos F.rminus F.rplus F.interval.1
     (F.interval.2.1.trans F.interval.2.2)
   obtain ⟨epsilon,he,C,hC,B,hB,hbound,hTaylor⟩ := F.uniform_actualTarget_prior_taylor
   let Cerr := F.volume*C*F.rplus/F.rminus^4
   have hsmallError := (selectedSource_scaled_TaylorError_gapRatio_tendsto_zero A0 (D+1)
     (Nat.succ_pos _) θ c0 F.epsilonU F.epsilonV F.rminus F.rplus Cerr
     hθ hθhalf F.epsilonU_pos F.epsilonU_le F.epsilonV_pos F.epsilonV_le F.interval.1
     (F.interval.2.1.trans F.interval.2.2)).eventually_lt_const F.gapCoefficient_pos
   obtain ⟨cg,hcg,hgap⟩ := selectedSourceGapScale_eventually_log_lower A0 (D+1)
     (Nat.succ_pos _) θ c0 F.epsilonU F.epsilonV F.rminus F.rplus hθ hθhalf
     F.epsilonU_pos F.epsilonV_pos F.interval.1 (F.interval.2.1.trans F.interval.2.2) hab
   have hrad := F.eventually_selected_profile_radius θ τ c0 epsilon hθ hθhalf hτ he
   filter_upwards [hrad,tendsto_natCast_atTop_atTop.eventually hsmallError,
     tendsto_natCast_atTop_atTop.eventually hgap,eventually_gt_atTop 1] with n hradn hEn hgn hn
   intro V hM hscale
   let G := F.selectedFrame θ τ c0 n V
   intro hsmall
   let nu := F.latticeSetup.coefficientPrior (selectedSourceLevel A0 (D+1) θ τ n)
     (frequency n θ τ) hM hscale
   let Au := selectedSourceAmplitude A0 (D+1) θ τ c0 F.epsilonU A0.α n
   let Av := selectedSourceAmplitude A0 (D+1) θ τ c0 F.epsilonV A0.β n
   let gap := selectedSourceGapScale A0 (D+1) θ τ c0 F.epsilonU F.epsilonV F.rminus F.rplus n
   have hnr : 1<(n:ℝ) := by exact_mod_cast hn
   have hgp : 0<gap := (mul_pos (mul_pos hcg (Real.log_pos hnr))
     (RoughRegime.Rates.scale_pos n θ τ hnr)).trans_le hgn
   have hE : Cerr*Au*Av*(Au^2+Av^2) ≤ F.gapCoefficient*gap := by
     apply (div_le_iff₀ hgp).mp
     exact hEn.le
   have ht := hTaylor G hsmall nu (hradn V).1 (hradn V).2
   have herror : (G.ell*(2*selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℕ))^(D+1)*
       (C*G.rplus*(G.Au/G.rminus)*(G.Av/G.rminus)*
         ((G.Au/G.rminus)^2+(G.Av/G.rminus)^2))=Cerr*Au*Av*(Au^2+Av^2) := by
     rw [F.selectedFrame_volume θ τ c0 n V]
     change F.volume*(C*F.rplus*(G.Au/F.rminus)*(G.Av/F.rminus)*
       ((G.Au/F.rminus)^2+(G.Av/F.rminus)^2))=Cerr*Au*Av*(Au^2+Av^2)
     rw [F.selectedFrame_Au θ τ c0 n V,F.selectedFrame_Av θ τ c0 n V]
     dsimp [Cerr,Au,Av]
     field_simp [F.interval.1.ne']
   rw [herror] at ht
   have huv := F.selectedFrame_puv_separation θ τ c0 n V hM hscale
   dsimp only at huv
   have hlead : F.latticeSetup.separationConstant*gap ≤ G.priorMeanDifference (fun x=>x.1*x.2) nu := by
     simpa only [gap,G,nu,selectedSourceGapScale,Upper.narrowedRho,sourceDensityMargin,
       F.selectedFrame_Au θ τ c0 n V,F.selectedFrame_Av θ τ c0 n V,mul_assoc] using huv
   have hm := mul_le_mul_of_nonneg_left (hlead.trans (le_abs_self _))
     (abs_nonneg (OddTaylor.mixedDerivative F.integrand 0))
   have htriangle : |OddTaylor.mixedDerivative F.integrand 0*G.priorMeanDifference (fun x=>x.1*x.2) nu| ≤
       |((∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M true)-
          (∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M false))-
          OddTaylor.mixedDerivative F.integrand 0*G.priorMeanDifference (fun x=>x.1*x.2) nu|+
         F.actualMeanGap G hsmall nu := by
     have h := abs_add_le (OddTaylor.mixedDerivative F.integrand 0*G.priorMeanDifference (fun x=>x.1*x.2) nu-
       ((∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M true)-
        (∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M false)))
       ((∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M true)-
        (∫ z,F.actualTarget G hsmall z ∂globalBlockPrior nu G.M false))
     rw [sub_add_cancel,abs_sub_comm] at h
     exact h
   rw [abs_mul] at htriangle
   change F.gapCoefficient*gap ≤ F.actualMeanGap G hsmall nu
   dsimp [gapCoefficient] at hE ⊢
   nlinarith


 theorem actualTarget_measurable (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4) : Measurable (F.actualTarget G hsmall) :=
   SpatialAffine.model_target_measurable (A0.withDimension D) O π F.scores G.field
     (fun _=>hsmall) G.field_p_measurable G.field_u_measurable G.field_v_measurable F.baseline_positive

 theorem eventually_selected_mean_gap_log_lower (F : SourceModelFamily A0 D O π)
     (θ c0 : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2)
     (hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ) :
     let τ := RoughRegime.Rates.tau F.rminus F.rplus
     ∃ c>0,∀ᶠ n in atTop, ∀ (V : F.SelectedValidity θ τ c0 n)
       (hM : 0<frequency n θ τ)
       (hscale : sourceFineScale (selectedSourceLevel A0 (D+1) θ τ n) (min A0.α A0.β) ≤
         sourceBandConstant (D+1) A0.α A0.β*frequency n θ τ),
     let G := F.selectedFrame θ τ c0 n V
     ∀ hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4,
     c*Real.log n*RoughRegime.Rates.subcriticalScale n θ τ ≤
       F.actualMeanGap G hsmall (F.latticeSetup.coefficientPrior
         (selectedSourceLevel A0 (D+1) θ τ n) (frequency n θ τ) hM hscale) := by
   dsimp only
   let τ := RoughRegime.Rates.tau F.rminus F.rplus
   obtain ⟨cg,hcg,hg⟩ := selectedSourceGapScale_eventually_log_lower A0 (D+1)
     (Nat.succ_pos _) θ c0 F.epsilonU F.epsilonV F.rminus F.rplus hθ hθhalf
     F.epsilonU_pos F.epsilonV_pos F.interval.1 (F.interval.2.1.trans F.interval.2.2) hab
   refine ⟨F.gapCoefficient*cg,mul_pos F.gapCoefficient_pos hcg,?_⟩
   filter_upwards [F.eventually_selected_mean_gap θ c0 hθ hθhalf hab,
     tendsto_natCast_atTop_atTop.eventually hg] with n hn hgn
   intro V hM hscale hsmall
   have hh := mul_le_mul_of_nonneg_left hgn F.gapCoefficient_pos.le
   calc
     _ = F.gapCoefficient*(cg*Real.log n*RoughRegime.Rates.subcriticalScale n θ τ) := by ring
     _ ≤ _ := hh
     _ ≤ _ := hn V hM hscale hsmall


 theorem actualMeanGap_nonneg (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4) (nu : Measure (ι→ℤ)) :
     0 ≤ F.actualMeanGap G hsmall nu := abs_nonneg _


end RoughRegime.LatticePriors.SourceModelFamily
