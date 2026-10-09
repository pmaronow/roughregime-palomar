module

public import RoughRegime.SourceSelectedStatistics


@[expose] public section
/-! Genuine selected variance budgets and their finite-model transfer. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 theorem eventually_selected_scaled_variance_bound (F : SourceModelFamily A0 D O π)
     (θ c0 Cvar : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2)
     (hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ) :
     let τ := RoughRegime.Rates.tau F.rminus F.rplus
     ∀ᶠ n : ℕ in atTop,
       Cvar/(selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) ≤
       (F.gapCoefficient*selectedSourceGapScale A0 (D+1) θ τ c0
         F.epsilonU F.epsilonV F.rminus F.rplus n)^2/1024 := by
   dsimp only
   let τ := RoughRegime.Rates.tau F.rminus F.rplus
   have hrat := (selectedSource_scaled_prior_variance_ratio_tendsto_zero A0 (D+1)
     (Nat.succ_pos _) θ c0 F.epsilonU F.epsilonV F.rminus F.rplus Cvar F.gapCoefficient
     hθ hθhalf F.epsilonU_pos F.epsilonV_pos F.interval.1 (F.interval.2.1.trans F.interval.2.2)
     hab F.gapCoefficient_pos.ne').eventually_lt_const (by norm_num : (0:ℝ)<1/1024)
   obtain ⟨cg,hcg,hgap⟩ := selectedSourceGapScale_eventually_log_lower A0 (D+1)
     (Nat.succ_pos _) θ c0 F.epsilonU F.epsilonV F.rminus F.rplus hθ hθhalf
     F.epsilonU_pos F.epsilonV_pos F.interval.1 (F.interval.2.1.trans F.interval.2.2) hab
   filter_upwards [tendsto_natCast_atTop_atTop.eventually hrat,
     tendsto_natCast_atTop_atTop.eventually hgap,eventually_gt_atTop 1] with n hratn hgapn hn
   let gap := selectedSourceGapScale A0 (D+1) θ τ c0 F.epsilonU F.epsilonV F.rminus F.rplus n
   have hnr : 1<(n:ℝ) := by exact_mod_cast hn
   have hgp : 0<gap := (mul_pos (mul_pos hcg (Real.log_pos hnr))
     (RoughRegime.Rates.scale_pos n θ τ hnr)).trans_le hgapn
   have hbase : 0<F.gapCoefficient*gap := mul_pos F.gapCoefficient_pos hgp
   have h := (div_le_iff₀ (sq_pos_of_pos hbase)).mp hratn.le
   nlinarith

 theorem prior_variance_control_of_bounds (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4) (nu : Measure (ι→ℤ))
     (vbound gbase : ℝ) (hbase : 0 ≤ gbase)
     (hv : ∀ positive:Bool,variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive) ≤ vbound)
     (hb : vbound ≤ gbase^2/1024) (hg : gbase ≤ F.actualMeanGap G hsmall nu) :
     ∀ positive:Bool,variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive) ≤
       (F.actualMeanGap G hsmall nu)^2/1024 := by
   intro positive
   have hs : gbase^2 ≤ (F.actualMeanGap G hsmall nu)^2 := pow_le_pow_left₀ hbase hg 2
   exact (hv positive).trans (hb.trans (div_le_div_of_nonneg_right hs (by norm_num)))

end RoughRegime.LatticePriors.SourceModelFamily
