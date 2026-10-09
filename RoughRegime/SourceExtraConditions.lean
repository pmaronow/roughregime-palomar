module

public import RoughRegime.SourceModelWeights
public import RoughRegime.SourceGermHolder
public import RoughRegime.SourceFinalModel


@[expose] public section
/-! Literal finite smooth-germ restrictions on the actual selected hard laws.
The constants are chosen with fixed scores and fixed design volume, before
shrinking the positive construction weights. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace RoughRegime.LatticePriors
open RoughRegime.Localization RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false

structure SourceExtraCondition (alpha beta : ℝ) where
  condition : Condition
  mode : GermMode
  axis : mode.axisCondition condition.germ
  exponent : match condition with
    | .holder _ t _ => t ≤ mode.exponent alpha beta
    | _ => True

namespace SourceModelFamily
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 theorem extra_condition_budget (F : SourceModelFamily A0 D O π)
     (e : SourceExtraCondition A0.α A0.β)
     (hbase : e.condition.baselineAdmissible F.rminus F.rplus) :
     ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
       ∀ (epsilonU epsilonV : ℝ) (heU : 0 < epsilonU) (heV : 0 < epsilonV)
         (hleU : epsilonU ≤ F.epsilonU) (hleV : epsilonV ≤ F.epsilonV)
         (N J M : ℕ) (hN : 0 < N) (m delta : ℝ) (hm : 0 < m) (hd : 0 < delta)
         (hmargin : delta ≤ F.margin),
       (2:ℝ)^((J:ℝ)*sourceAlpha0 A0.α A0.β) ≤ m →
       m ≤ (2:ℝ)^((J:ℝ)*min A0.α A0.β) →
       let G := (F.withWeights epsilonU epsilonV heU heV hleU hleV).frame N J M hN m delta hm hd hmargin
       G.Au+G.Av ≤ eta → ∀ z : GridPair D N→PairState (Fin J×Fin (D+1)),
         e.condition.perturbationBound C (epsilonU+epsilonV) (G.field z).u (G.field z).v := by
   cases e with
   | mk condition mode haxis hexp =>
     cases condition with
     | interval G lo hi =>
       exact ⟨1,1,by norm_num,by norm_num,by intros; trivial⟩
     | weighted G lo hi =>
       exact ⟨1,1,by norm_num,by norm_num,by intros; trivial⟩
     | holder G t H =>
       have hgamma := sourceGammaStar_bounds (D+1) (Nat.succ_pos _)
       have hlam := zero_lt_one.trans_le (sourceLambdaStar_ge_one (D+1) A0.α A0.β)
       obtain ⟨eta,C,heta,hC,hbound⟩ := source_germ_holder D (sourceGateOrder A0.α A0.β)
         (sourceJetBudget A0.α A0.β) (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) A0.α A0.β)
         (sourceAlpha0 A0.α A0.β) A0.α A0.β F.volume F.rminus F.rplus
         hgamma.1 hgamma.2.1 hlam (sourceAlpha0_pos _ _ A0.hα A0.hβ).le
         (sourceAlpha0_lt_one _ _) (sourceJetBudget_pos _ _) (sourceJetBudget_le_twice_order _ _)
         (lt_min (sourceAlpha0_lt_alpha _ _ A0.hα) (sourceAlpha0_lt_beta _ _ A0.hβ))
         (source_alpha_derivative_budget _ _ A0.hα) (source_beta_derivative_budget _ _ A0.hβ)
         F.volume_pos (F.volume_half.trans (by norm_num)) F.interval.1
         (F.interval.2.1.trans F.interval.2.2) F.denominator_pos G mode haxis
       refine ⟨eta,C,heta,hC,?_⟩
       intro epsilonU epsilonV heU heV hleU hleV N J M hN m delta hm hd hmargin hm0 hm1
       dsimp only
       intro hsmall z
       obtain ⟨hs,hb⟩ := hbound N J M hN m epsilonU epsilonV delta hm heU.le heV.le hd hmargin
         hm0 hm1 hsmall z
       exact ⟨hs,hb t hbase.1 hexp⟩

 theorem finite_extra_holder_cap (F : SourceModelFamily A0 D O π)
     {ι : Type*} [Fintype ι] (e : ι→SourceExtraCondition A0.α A0.β)
     (hbase : ∀ i, (e i).condition.baselineAdmissible F.rminus F.rplus)
     (cost : ι→ℝ) :
     ∃ cap : ℝ, 0 < cap ∧ ∀ i, cost i*cap ≤ (e i).condition.holderBudget := by
   have he : ∀ᶠ c : ℝ in 𝓝 0, ∀ i, cost i*c < (e i).condition.holderBudget := by
     apply eventually_all.mpr
     intro i
     have hb := Condition.holderBudget_pos (e i).condition F.rminus F.rplus (hbase i)
     have hcont : ContinuousAt (fun c : ℝ => cost i*c) 0 := by fun_prop
     have hc : Tendsto (fun c : ℝ => cost i*c) (𝓝 0) (𝓝 0) := by
       simpa only [mul_zero] using hcont.tendsto
     exact hc.eventually_lt_const hb
   obtain ⟨r,hr,heball⟩ := Metric.eventually_nhds_iff.mp he
   refine ⟨r/2,half_pos hr,?_⟩
   have hh := heball (show dist (r/2) (0:ℝ)<r by rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)]; exact half_lt_self hr)
   exact fun i => (hh i).le

end SourceModelFamily
end RoughRegime.LatticePriors
